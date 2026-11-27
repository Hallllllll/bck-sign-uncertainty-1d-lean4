import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000111111111_0 : Blocks := edgeBlocks% "full/vectors/00000111111111-V-0000.bin"
noncomputable def vp00000111111111 : Blocks := vp00000111111111_0
theorem coverp00000111111111 : Covers (-255261639/500000 : ℚ) vp00000111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111111110_0 : Blocks := edgeBlocks% "full/vectors/00000111111110-V-0000.bin"
noncomputable def vp00000111111110 : Blocks := vp00000111111110_0
theorem coverp00000111111110 : Covers (-254761639/500000 : ℚ) vp00000111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111111_0 : Blocks := edgeBlocks% "full/vectors/0000011111111-V-0000.bin"
noncomputable def vp0000011111111 : Blocks := vp0000011111111_0
private theorem bp00000111111110 : Branch 0 (-254761639/1000000 : ℚ) vp0000011111111 := by
  apply branch_left_normalized (c:=vp00000111111110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-254761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-254761639/500000 : ℚ) by norm_num]
  exact coverp00000111111110
private noncomputable def ep00000111111111_0 : Blocks := edgeBlocks% "full/vectors/00000111111111-E-0000.bin"
noncomputable def ep00000111111111 : Blocks := ep00000111111111_0
private theorem idp00000111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111111.list =
    C ((2:ℤ)^80) * horner X vp00000111111111.list + horner X ep00000111111111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111111111 : Branch 1 (-254761639/1000000 : ℚ) vp0000011111111 := by
  apply branch_checked idp00000111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-254761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-255261639/500000 : ℚ) by norm_num]
  exact coverp00000111111111
theorem coverp0000011111111 : Covers (-254761639/1000000 : ℚ) vp0000011111111 := join_branches bp00000111111110 bp00000111111111
private noncomputable def vp00000111111101_0 : Blocks := edgeBlocks% "full/vectors/00000111111101-V-0000.bin"
noncomputable def vp00000111111101 : Blocks := vp00000111111101_0
theorem coverp00000111111101 : Covers (-254261639/500000 : ℚ) vp00000111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111111100_0 : Blocks := edgeBlocks% "full/vectors/00000111111100-V-0000.bin"
noncomputable def vp00000111111100 : Blocks := vp00000111111100_0
theorem coverp00000111111100 : Covers (-253761639/500000 : ℚ) vp00000111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111110_0 : Blocks := edgeBlocks% "full/vectors/0000011111110-V-0000.bin"
noncomputable def vp0000011111110 : Blocks := vp0000011111110_0
private theorem bp00000111111100 : Branch 0 (-253761639/1000000 : ℚ) vp0000011111110 := by
  apply branch_left_normalized (c:=vp00000111111100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-253761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-253761639/500000 : ℚ) by norm_num]
  exact coverp00000111111100
private noncomputable def ep00000111111101_0 : Blocks := edgeBlocks% "full/vectors/00000111111101-E-0000.bin"
noncomputable def ep00000111111101 : Blocks := ep00000111111101_0
private theorem idp00000111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111110.list =
    C ((2:ℤ)^81) * horner X vp00000111111101.list + horner X ep00000111111101.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111111101 : Branch 1 (-253761639/1000000 : ℚ) vp0000011111110 := by
  apply branch_checked idp00000111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-253761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-254261639/500000 : ℚ) by norm_num]
  exact coverp00000111111101
theorem coverp0000011111110 : Covers (-253761639/1000000 : ℚ) vp0000011111110 := join_branches bp00000111111100 bp00000111111101
private noncomputable def vp000001111111_0 : Blocks := edgeBlocks% "full/vectors/000001111111-V-0000.bin"
private noncomputable def vp000001111111_1 : Blocks := edgeBlocks% "full/vectors/000001111111-V-0001.bin"
noncomputable def vp000001111111 : Blocks := (Blocks.join vp000001111111_0 vp000001111111_1)
private theorem bp0000011111110 : Branch 0 (-253761639/2000000 : ℚ) vp000001111111 := by
  apply branch_left_normalized (c:=vp0000011111110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-253761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-253761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111110
private noncomputable def ep0000011111111_0 : Blocks := edgeBlocks% "full/vectors/0000011111111-E-0000.bin"
private noncomputable def ep0000011111111_1 : Blocks := edgeBlocks% "full/vectors/0000011111111-E-0001.bin"
noncomputable def ep0000011111111 : Blocks := (Blocks.join ep0000011111111_0 ep0000011111111_1)
private theorem idp0000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111111.list =
    C ((2:ℤ)^146) * horner X vp0000011111111.list + horner X ep0000011111111.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011111111 : Branch 1 (-253761639/2000000 : ℚ) vp000001111111 := by
  apply branch_checked idp0000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-253761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-254761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111111
theorem coverp000001111111 : Covers (-253761639/2000000 : ℚ) vp000001111111 := join_branches bp0000011111110 bp0000011111111
private noncomputable def vp00000111111011_0 : Blocks := edgeBlocks% "full/vectors/00000111111011-V-0000.bin"
noncomputable def vp00000111111011 : Blocks := vp00000111111011_0
theorem coverp00000111111011 : Covers (-253261639/500000 : ℚ) vp00000111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111111010_0 : Blocks := edgeBlocks% "full/vectors/00000111111010-V-0000.bin"
noncomputable def vp00000111111010 : Blocks := vp00000111111010_0
theorem coverp00000111111010 : Covers (-252761639/500000 : ℚ) vp00000111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000011111101-V-0000.bin"
noncomputable def vp0000011111101 : Blocks := vp0000011111101_0
private theorem bp00000111111010 : Branch 0 (-252761639/1000000 : ℚ) vp0000011111101 := by
  apply branch_left_normalized (c:=vp00000111111010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-252761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-252761639/500000 : ℚ) by norm_num]
  exact coverp00000111111010
private noncomputable def ep00000111111011_0 : Blocks := edgeBlocks% "full/vectors/00000111111011-E-0000.bin"
noncomputable def ep00000111111011 : Blocks := ep00000111111011_0
private theorem idp00000111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111101.list =
    C ((2:ℤ)^81) * horner X vp00000111111011.list + horner X ep00000111111011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111111011 : Branch 1 (-252761639/1000000 : ℚ) vp0000011111101 := by
  apply branch_checked idp00000111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-252761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-253261639/500000 : ℚ) by norm_num]
  exact coverp00000111111011
theorem coverp0000011111101 : Covers (-252761639/1000000 : ℚ) vp0000011111101 := join_branches bp00000111111010 bp00000111111011
private noncomputable def vp00000111111001_0 : Blocks := edgeBlocks% "full/vectors/00000111111001-V-0000.bin"
noncomputable def vp00000111111001 : Blocks := vp00000111111001_0
theorem coverp00000111111001 : Covers (-252261639/500000 : ℚ) vp00000111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111111000_0 : Blocks := edgeBlocks% "full/vectors/00000111111000-V-0000.bin"
noncomputable def vp00000111111000 : Blocks := vp00000111111000_0
theorem coverp00000111111000 : Covers (-251761639/500000 : ℚ) vp00000111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111100_0 : Blocks := edgeBlocks% "full/vectors/0000011111100-V-0000.bin"
noncomputable def vp0000011111100 : Blocks := vp0000011111100_0
private theorem bp00000111111000 : Branch 0 (-251761639/1000000 : ℚ) vp0000011111100 := by
  apply branch_left_normalized (c:=vp00000111111000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-251761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-251761639/500000 : ℚ) by norm_num]
  exact coverp00000111111000
private noncomputable def ep00000111111001_0 : Blocks := edgeBlocks% "full/vectors/00000111111001-E-0000.bin"
noncomputable def ep00000111111001 : Blocks := ep00000111111001_0
private theorem idp00000111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111100.list =
    C ((2:ℤ)^82) * horner X vp00000111111001.list + horner X ep00000111111001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111111001 : Branch 1 (-251761639/1000000 : ℚ) vp0000011111100 := by
  apply branch_checked idp00000111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-251761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-252261639/500000 : ℚ) by norm_num]
  exact coverp00000111111001
theorem coverp0000011111100 : Covers (-251761639/1000000 : ℚ) vp0000011111100 := join_branches bp00000111111000 bp00000111111001
private noncomputable def vp000001111110_0 : Blocks := edgeBlocks% "full/vectors/000001111110-V-0000.bin"
private noncomputable def vp000001111110_1 : Blocks := edgeBlocks% "full/vectors/000001111110-V-0001.bin"
noncomputable def vp000001111110 : Blocks := (Blocks.join vp000001111110_0 vp000001111110_1)
private theorem bp0000011111100 : Branch 0 (-251761639/2000000 : ℚ) vp000001111110 := by
  apply branch_left_normalized (c:=vp0000011111100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-251761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-251761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111100
private noncomputable def ep0000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000011111101-E-0000.bin"
private noncomputable def ep0000011111101_1 : Blocks := edgeBlocks% "full/vectors/0000011111101-E-0001.bin"
noncomputable def ep0000011111101 : Blocks := (Blocks.join ep0000011111101_0 ep0000011111101_1)
private theorem idp0000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111110.list =
    C ((2:ℤ)^148) * horner X vp0000011111101.list + horner X ep0000011111101.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011111101 : Branch 1 (-251761639/2000000 : ℚ) vp000001111110 := by
  apply branch_checked idp0000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-251761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-252761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111101
theorem coverp000001111110 : Covers (-251761639/2000000 : ℚ) vp000001111110 := join_branches bp0000011111100 bp0000011111101
private noncomputable def vp00000111111_0 : Blocks := edgeBlocks% "full/vectors/00000111111-V-0000.bin"
private noncomputable def vp00000111111_1 : Blocks := edgeBlocks% "full/vectors/00000111111-V-0001.bin"
private noncomputable def vp00000111111_2 : Blocks := edgeBlocks% "full/vectors/00000111111-V-0002.bin"
noncomputable def vp00000111111 : Blocks := (Blocks.join vp00000111111_0 (Blocks.join vp00000111111_1 vp00000111111_2))
private theorem bp000001111110 : Branch 0 (-251761639/4000000 : ℚ) vp00000111111 := by
  apply branch_left_normalized (c:=vp000001111110) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-251761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-251761639/2000000 : ℚ) by norm_num]
  exact coverp000001111110
private noncomputable def ep000001111111_0 : Blocks := edgeBlocks% "full/vectors/000001111111-E-0000.bin"
private noncomputable def ep000001111111_1 : Blocks := edgeBlocks% "full/vectors/000001111111-E-0001.bin"
private noncomputable def ep000001111111_2 : Blocks := edgeBlocks% "full/vectors/000001111111-E-0002.bin"
noncomputable def ep000001111111 : Blocks := (Blocks.join ep000001111111_0 (Blocks.join ep000001111111_1 ep000001111111_2))
private theorem idp000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111111.list =
    C ((2:ℤ)^278) * horner X vp000001111111.list + horner X ep000001111111.list := by
  exact edge_identity (B := (2:ℤ)^489) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111111 : Branch 1 (-251761639/4000000 : ℚ) vp00000111111 := by
  apply branch_checked idp000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-251761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-253761639/2000000 : ℚ) by norm_num]
  exact coverp000001111111
theorem coverp00000111111 : Covers (-251761639/4000000 : ℚ) vp00000111111 := join_branches bp000001111110 bp000001111111
private noncomputable def vp00000111110111_0 : Blocks := edgeBlocks% "full/vectors/00000111110111-V-0000.bin"
noncomputable def vp00000111110111 : Blocks := vp00000111110111_0
theorem coverp00000111110111 : Covers (-251261639/500000 : ℚ) vp00000111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111110110_0 : Blocks := edgeBlocks% "full/vectors/00000111110110-V-0000.bin"
noncomputable def vp00000111110110 : Blocks := vp00000111110110_0
theorem coverp00000111110110 : Covers (-250761639/500000 : ℚ) vp00000111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111011_0 : Blocks := edgeBlocks% "full/vectors/0000011111011-V-0000.bin"
noncomputable def vp0000011111011 : Blocks := vp0000011111011_0
private theorem bp00000111110110 : Branch 0 (-250761639/1000000 : ℚ) vp0000011111011 := by
  apply branch_left_normalized (c:=vp00000111110110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-250761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-250761639/500000 : ℚ) by norm_num]
  exact coverp00000111110110
private noncomputable def ep00000111110111_0 : Blocks := edgeBlocks% "full/vectors/00000111110111-E-0000.bin"
noncomputable def ep00000111110111 : Blocks := ep00000111110111_0
private theorem idp00000111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111011.list =
    C ((2:ℤ)^82) * horner X vp00000111110111.list + horner X ep00000111110111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111110111 : Branch 1 (-250761639/1000000 : ℚ) vp0000011111011 := by
  apply branch_checked idp00000111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-250761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-251261639/500000 : ℚ) by norm_num]
  exact coverp00000111110111
theorem coverp0000011111011 : Covers (-250761639/1000000 : ℚ) vp0000011111011 := join_branches bp00000111110110 bp00000111110111
private noncomputable def vp00000111110101_0 : Blocks := edgeBlocks% "full/vectors/00000111110101-V-0000.bin"
noncomputable def vp00000111110101 : Blocks := vp00000111110101_0
theorem coverp00000111110101 : Covers (-250261639/500000 : ℚ) vp00000111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111110100_0 : Blocks := edgeBlocks% "full/vectors/00000111110100-V-0000.bin"
noncomputable def vp00000111110100 : Blocks := vp00000111110100_0
theorem coverp00000111110100 : Covers (-249761639/500000 : ℚ) vp00000111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111010_0 : Blocks := edgeBlocks% "full/vectors/0000011111010-V-0000.bin"
noncomputable def vp0000011111010 : Blocks := vp0000011111010_0
private theorem bp00000111110100 : Branch 0 (-249761639/1000000 : ℚ) vp0000011111010 := by
  apply branch_left_normalized (c:=vp00000111110100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-249761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-249761639/500000 : ℚ) by norm_num]
  exact coverp00000111110100
private noncomputable def ep00000111110101_0 : Blocks := edgeBlocks% "full/vectors/00000111110101-E-0000.bin"
noncomputable def ep00000111110101 : Blocks := ep00000111110101_0
private theorem idp00000111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111010.list =
    C ((2:ℤ)^85) * horner X vp00000111110101.list + horner X ep00000111110101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111110101 : Branch 1 (-249761639/1000000 : ℚ) vp0000011111010 := by
  apply branch_checked idp00000111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-249761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-250261639/500000 : ℚ) by norm_num]
  exact coverp00000111110101
theorem coverp0000011111010 : Covers (-249761639/1000000 : ℚ) vp0000011111010 := join_branches bp00000111110100 bp00000111110101
private noncomputable def vp000001111101_0 : Blocks := edgeBlocks% "full/vectors/000001111101-V-0000.bin"
private noncomputable def vp000001111101_1 : Blocks := edgeBlocks% "full/vectors/000001111101-V-0001.bin"
noncomputable def vp000001111101 : Blocks := (Blocks.join vp000001111101_0 vp000001111101_1)
private theorem bp0000011111010 : Branch 0 (-249761639/2000000 : ℚ) vp000001111101 := by
  apply branch_left_normalized (c:=vp0000011111010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-249761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-249761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111010
private noncomputable def ep0000011111011_0 : Blocks := edgeBlocks% "full/vectors/0000011111011-E-0000.bin"
private noncomputable def ep0000011111011_1 : Blocks := edgeBlocks% "full/vectors/0000011111011-E-0001.bin"
noncomputable def ep0000011111011 : Blocks := (Blocks.join ep0000011111011_0 ep0000011111011_1)
private theorem idp0000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111101.list =
    C ((2:ℤ)^152) * horner X vp0000011111011.list + horner X ep0000011111011.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011111011 : Branch 1 (-249761639/2000000 : ℚ) vp000001111101 := by
  apply branch_checked idp0000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-249761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-250761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111011
theorem coverp000001111101 : Covers (-249761639/2000000 : ℚ) vp000001111101 := join_branches bp0000011111010 bp0000011111011
private noncomputable def vp00000111110011_0 : Blocks := edgeBlocks% "full/vectors/00000111110011-V-0000.bin"
noncomputable def vp00000111110011 : Blocks := vp00000111110011_0
theorem coverp00000111110011 : Covers (-249261639/500000 : ℚ) vp00000111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111110010_0 : Blocks := edgeBlocks% "full/vectors/00000111110010-V-0000.bin"
noncomputable def vp00000111110010 : Blocks := vp00000111110010_0
theorem coverp00000111110010 : Covers (-248761639/500000 : ℚ) vp00000111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011111001_0 : Blocks := edgeBlocks% "full/vectors/0000011111001-V-0000.bin"
noncomputable def vp0000011111001 : Blocks := vp0000011111001_0
private theorem bp00000111110010 : Branch 0 (-248761639/1000000 : ℚ) vp0000011111001 := by
  apply branch_left_normalized (c:=vp00000111110010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-248761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-248761639/500000 : ℚ) by norm_num]
  exact coverp00000111110010
private noncomputable def ep00000111110011_0 : Blocks := edgeBlocks% "full/vectors/00000111110011-E-0000.bin"
noncomputable def ep00000111110011 : Blocks := ep00000111110011_0
private theorem idp00000111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111001.list =
    C ((2:ℤ)^89) * horner X vp00000111110011.list + horner X ep00000111110011.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111110011 : Branch 1 (-248761639/1000000 : ℚ) vp0000011111001 := by
  apply branch_checked idp00000111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-248761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-249261639/500000 : ℚ) by norm_num]
  exact coverp00000111110011
theorem coverp0000011111001 : Covers (-248761639/1000000 : ℚ) vp0000011111001 := join_branches bp00000111110010 bp00000111110011
private noncomputable def vp000001111100011_0 : Blocks := edgeBlocks% "full/vectors/000001111100011-V-0000.bin"
noncomputable def vp000001111100011 : Blocks := vp000001111100011_0
theorem coverp000001111100011 : Covers (-248511639/250000 : ℚ) vp000001111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111100010_0 : Blocks := edgeBlocks% "full/vectors/000001111100010-V-0000.bin"
noncomputable def vp000001111100010 : Blocks := vp000001111100010_0
theorem coverp000001111100010 : Covers (-248261639/250000 : ℚ) vp000001111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111110001_0 : Blocks := edgeBlocks% "full/vectors/00000111110001-V-0000.bin"
noncomputable def vp00000111110001 : Blocks := vp00000111110001_0
private theorem bp000001111100010 : Branch 0 (-248261639/500000 : ℚ) vp00000111110001 := by
  apply branch_left_normalized (c:=vp000001111100010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-248261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-248261639/250000 : ℚ) by norm_num]
  exact coverp000001111100010
private noncomputable def ep000001111100011_0 : Blocks := edgeBlocks% "full/vectors/000001111100011-E-0000.bin"
noncomputable def ep000001111100011 : Blocks := ep000001111100011_0
private theorem idp000001111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111110001.list =
    C ((2:ℤ)^54) * horner X vp000001111100011.list + horner X ep000001111100011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111100011 : Branch 1 (-248261639/500000 : ℚ) vp00000111110001 := by
  apply branch_checked idp000001111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-248261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-248511639/250000 : ℚ) by norm_num]
  exact coverp000001111100011
theorem coverp00000111110001 : Covers (-248261639/500000 : ℚ) vp00000111110001 := join_branches bp000001111100010 bp000001111100011
private noncomputable def vp000001111100001_0 : Blocks := edgeBlocks% "full/vectors/000001111100001-V-0000.bin"
noncomputable def vp000001111100001 : Blocks := vp000001111100001_0
theorem coverp000001111100001 : Covers (-248011639/250000 : ℚ) vp000001111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111100000_0 : Blocks := edgeBlocks% "full/vectors/000001111100000-V-0000.bin"
noncomputable def vp000001111100000 : Blocks := vp000001111100000_0
theorem coverp000001111100000 : Covers (-247761639/250000 : ℚ) vp000001111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111110000_0 : Blocks := edgeBlocks% "full/vectors/00000111110000-V-0000.bin"
noncomputable def vp00000111110000 : Blocks := vp00000111110000_0
private theorem bp000001111100000 : Branch 0 (-247761639/500000 : ℚ) vp00000111110000 := by
  apply branch_left_normalized (c:=vp000001111100000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-247761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-247761639/250000 : ℚ) by norm_num]
  exact coverp000001111100000
private noncomputable def ep000001111100001_0 : Blocks := edgeBlocks% "full/vectors/000001111100001-E-0000.bin"
noncomputable def ep000001111100001 : Blocks := ep000001111100001_0
private theorem idp000001111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111110000.list =
    C ((2:ℤ)^52) * horner X vp000001111100001.list + horner X ep000001111100001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111100001 : Branch 1 (-247761639/500000 : ℚ) vp00000111110000 := by
  apply branch_checked idp000001111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-247761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-248011639/250000 : ℚ) by norm_num]
  exact coverp000001111100001
theorem coverp00000111110000 : Covers (-247761639/500000 : ℚ) vp00000111110000 := join_branches bp000001111100000 bp000001111100001
private noncomputable def vp0000011111000_0 : Blocks := edgeBlocks% "full/vectors/0000011111000-V-0000.bin"
noncomputable def vp0000011111000 : Blocks := vp0000011111000_0
private theorem bp00000111110000 : Branch 0 (-247761639/1000000 : ℚ) vp0000011111000 := by
  apply branch_left_normalized (c:=vp00000111110000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-247761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-247761639/500000 : ℚ) by norm_num]
  exact coverp00000111110000
private noncomputable def ep00000111110001_0 : Blocks := edgeBlocks% "full/vectors/00000111110001-E-0000.bin"
noncomputable def ep00000111110001 : Blocks := ep00000111110001_0
private theorem idp00000111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111000.list =
    C ((2:ℤ)^85) * horner X vp00000111110001.list + horner X ep00000111110001.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111110001 : Branch 1 (-247761639/1000000 : ℚ) vp0000011111000 := by
  apply branch_checked idp00000111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-247761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-248261639/500000 : ℚ) by norm_num]
  exact coverp00000111110001
theorem coverp0000011111000 : Covers (-247761639/1000000 : ℚ) vp0000011111000 := join_branches bp00000111110000 bp00000111110001
private noncomputable def vp000001111100_0 : Blocks := edgeBlocks% "full/vectors/000001111100-V-0000.bin"
private noncomputable def vp000001111100_1 : Blocks := edgeBlocks% "full/vectors/000001111100-V-0001.bin"
noncomputable def vp000001111100 : Blocks := (Blocks.join vp000001111100_0 vp000001111100_1)
private theorem bp0000011111000 : Branch 0 (-247761639/2000000 : ℚ) vp000001111100 := by
  apply branch_left_normalized (c:=vp0000011111000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-247761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-247761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111000
private noncomputable def ep0000011111001_0 : Blocks := edgeBlocks% "full/vectors/0000011111001-E-0000.bin"
private noncomputable def ep0000011111001_1 : Blocks := edgeBlocks% "full/vectors/0000011111001-E-0001.bin"
noncomputable def ep0000011111001 : Blocks := (Blocks.join ep0000011111001_0 ep0000011111001_1)
private theorem idp0000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111100.list =
    C ((2:ℤ)^153) * horner X vp0000011111001.list + horner X ep0000011111001.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011111001 : Branch 1 (-247761639/2000000 : ℚ) vp000001111100 := by
  apply branch_checked idp0000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-247761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-248761639/1000000 : ℚ) by norm_num]
  exact coverp0000011111001
theorem coverp000001111100 : Covers (-247761639/2000000 : ℚ) vp000001111100 := join_branches bp0000011111000 bp0000011111001
private noncomputable def vp00000111110_0 : Blocks := edgeBlocks% "full/vectors/00000111110-V-0000.bin"
private noncomputable def vp00000111110_1 : Blocks := edgeBlocks% "full/vectors/00000111110-V-0001.bin"
private noncomputable def vp00000111110_2 : Blocks := edgeBlocks% "full/vectors/00000111110-V-0002.bin"
noncomputable def vp00000111110 : Blocks := (Blocks.join vp00000111110_0 (Blocks.join vp00000111110_1 vp00000111110_2))
private theorem bp000001111100 : Branch 0 (-247761639/4000000 : ℚ) vp00000111110 := by
  apply branch_left_normalized (c:=vp000001111100) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-247761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-247761639/2000000 : ℚ) by norm_num]
  exact coverp000001111100
private noncomputable def ep000001111101_0 : Blocks := edgeBlocks% "full/vectors/000001111101-E-0000.bin"
private noncomputable def ep000001111101_1 : Blocks := edgeBlocks% "full/vectors/000001111101-E-0001.bin"
private noncomputable def ep000001111101_2 : Blocks := edgeBlocks% "full/vectors/000001111101-E-0002.bin"
noncomputable def ep000001111101 : Blocks := (Blocks.join ep000001111101_0 (Blocks.join ep000001111101_1 ep000001111101_2))
private theorem idp000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111110.list =
    C ((2:ℤ)^288) * horner X vp000001111101.list + horner X ep000001111101.list := by
  exact edge_identity (B := (2:ℤ)^505) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111101 : Branch 1 (-247761639/4000000 : ℚ) vp00000111110 := by
  apply branch_checked idp000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-247761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-249761639/2000000 : ℚ) by norm_num]
  exact coverp000001111101
theorem coverp00000111110 : Covers (-247761639/4000000 : ℚ) vp00000111110 := join_branches bp000001111100 bp000001111101
private noncomputable def vp0000011111_0 : Blocks := edgeBlocks% "full/vectors/0000011111-V-0000.bin"
private noncomputable def vp0000011111_1 : Blocks := edgeBlocks% "full/vectors/0000011111-V-0001.bin"
private noncomputable def vp0000011111_2 : Blocks := edgeBlocks% "full/vectors/0000011111-V-0002.bin"
private noncomputable def vp0000011111_3 : Blocks := edgeBlocks% "full/vectors/0000011111-V-0003.bin"
private noncomputable def vp0000011111_4 : Blocks := edgeBlocks% "full/vectors/0000011111-V-0004.bin"
noncomputable def vp0000011111 : Blocks := (Blocks.join (Blocks.join vp0000011111_0 vp0000011111_1) (Blocks.join vp0000011111_2 (Blocks.join vp0000011111_3 vp0000011111_4)))
private theorem bp00000111110 : Branch 0 (-247761639/8000000 : ℚ) vp0000011111 := by
  apply branch_left_normalized (c:=vp00000111110) (k:=0) (m:=271) (by decide +kernel)
  rw [show 2*(-247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-247761639/4000000 : ℚ) by norm_num]
  exact coverp00000111110
private noncomputable def ep00000111111_0 : Blocks := edgeBlocks% "full/vectors/00000111111-E-0000.bin"
private noncomputable def ep00000111111_1 : Blocks := edgeBlocks% "full/vectors/00000111111-E-0001.bin"
private noncomputable def ep00000111111_2 : Blocks := edgeBlocks% "full/vectors/00000111111-E-0002.bin"
private noncomputable def ep00000111111_3 : Blocks := edgeBlocks% "full/vectors/00000111111-E-0003.bin"
private noncomputable def ep00000111111_4 : Blocks := edgeBlocks% "full/vectors/00000111111-E-0004.bin"
noncomputable def ep00000111111 : Blocks := (Blocks.join (Blocks.join ep00000111111_0 ep00000111111_1) (Blocks.join ep00000111111_2 (Blocks.join ep00000111111_3 ep00000111111_4)))
private theorem idp00000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011111.list =
    C ((2:ℤ)^550) * horner X vp00000111111.list + horner X ep00000111111.list := by
  exact edge_identity (B := (2:ℤ)^884) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111111 : Branch 1 (-247761639/8000000 : ℚ) vp0000011111 := by
  apply branch_checked idp00000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-251761639/4000000 : ℚ) by norm_num]
  exact coverp00000111111
theorem coverp0000011111 : Covers (-247761639/8000000 : ℚ) vp0000011111 := join_branches bp00000111110 bp00000111111
private noncomputable def vp000001111011111_0 : Blocks := edgeBlocks% "full/vectors/000001111011111-V-0000.bin"
noncomputable def vp000001111011111 : Blocks := vp000001111011111_0
theorem coverp000001111011111 : Covers (-247511639/250000 : ℚ) vp000001111011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111011110_0 : Blocks := edgeBlocks% "full/vectors/000001111011110-V-0000.bin"
noncomputable def vp000001111011110 : Blocks := vp000001111011110_0
theorem coverp000001111011110 : Covers (-247261639/250000 : ℚ) vp000001111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101111_0 : Blocks := edgeBlocks% "full/vectors/00000111101111-V-0000.bin"
noncomputable def vp00000111101111 : Blocks := vp00000111101111_0
private theorem bp000001111011110 : Branch 0 (-247261639/500000 : ℚ) vp00000111101111 := by
  apply branch_left_normalized (c:=vp000001111011110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-247261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-247261639/250000 : ℚ) by norm_num]
  exact coverp000001111011110
private noncomputable def ep000001111011111_0 : Blocks := edgeBlocks% "full/vectors/000001111011111-E-0000.bin"
noncomputable def ep000001111011111 : Blocks := ep000001111011111_0
private theorem idp000001111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101111.list =
    C ((2:ℤ)^51) * horner X vp000001111011111.list + horner X ep000001111011111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111011111 : Branch 1 (-247261639/500000 : ℚ) vp00000111101111 := by
  apply branch_checked idp000001111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-247261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-247511639/250000 : ℚ) by norm_num]
  exact coverp000001111011111
theorem coverp00000111101111 : Covers (-247261639/500000 : ℚ) vp00000111101111 := join_branches bp000001111011110 bp000001111011111
private noncomputable def vp00000111101110_0 : Blocks := edgeBlocks% "full/vectors/00000111101110-V-0000.bin"
noncomputable def vp00000111101110 : Blocks := vp00000111101110_0
theorem coverp00000111101110 : Covers (-246761639/500000 : ℚ) vp00000111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000011110111-V-0000.bin"
noncomputable def vp0000011110111 : Blocks := vp0000011110111_0
private theorem bp00000111101110 : Branch 0 (-246761639/1000000 : ℚ) vp0000011110111 := by
  apply branch_left_normalized (c:=vp00000111101110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-246761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-246761639/500000 : ℚ) by norm_num]
  exact coverp00000111101110
private noncomputable def ep00000111101111_0 : Blocks := edgeBlocks% "full/vectors/00000111101111-E-0000.bin"
noncomputable def ep00000111101111 : Blocks := ep00000111101111_0
private theorem idp00000111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110111.list =
    C ((2:ℤ)^86) * horner X vp00000111101111.list + horner X ep00000111101111.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111101111 : Branch 1 (-246761639/1000000 : ℚ) vp0000011110111 := by
  apply branch_checked idp00000111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-246761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-247261639/500000 : ℚ) by norm_num]
  exact coverp00000111101111
theorem coverp0000011110111 : Covers (-246761639/1000000 : ℚ) vp0000011110111 := join_branches bp00000111101110 bp00000111101111
private noncomputable def vp000001111011011_0 : Blocks := edgeBlocks% "full/vectors/000001111011011-V-0000.bin"
noncomputable def vp000001111011011 : Blocks := vp000001111011011_0
theorem coverp000001111011011 : Covers (-246511639/250000 : ℚ) vp000001111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111011010_0 : Blocks := edgeBlocks% "full/vectors/000001111011010-V-0000.bin"
noncomputable def vp000001111011010 : Blocks := vp000001111011010_0
theorem coverp000001111011010 : Covers (-246261639/250000 : ℚ) vp000001111011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101101_0 : Blocks := edgeBlocks% "full/vectors/00000111101101-V-0000.bin"
noncomputable def vp00000111101101 : Blocks := vp00000111101101_0
private theorem bp000001111011010 : Branch 0 (-246261639/500000 : ℚ) vp00000111101101 := by
  apply branch_left_normalized (c:=vp000001111011010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-246261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-246261639/250000 : ℚ) by norm_num]
  exact coverp000001111011010
private noncomputable def ep000001111011011_0 : Blocks := edgeBlocks% "full/vectors/000001111011011-E-0000.bin"
noncomputable def ep000001111011011 : Blocks := ep000001111011011_0
private theorem idp000001111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101101.list =
    C ((2:ℤ)^53) * horner X vp000001111011011.list + horner X ep000001111011011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111011011 : Branch 1 (-246261639/500000 : ℚ) vp00000111101101 := by
  apply branch_checked idp000001111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-246261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-246511639/250000 : ℚ) by norm_num]
  exact coverp000001111011011
theorem coverp00000111101101 : Covers (-246261639/500000 : ℚ) vp00000111101101 := join_branches bp000001111011010 bp000001111011011
private noncomputable def vp000001111011001_0 : Blocks := edgeBlocks% "full/vectors/000001111011001-V-0000.bin"
noncomputable def vp000001111011001 : Blocks := vp000001111011001_0
theorem coverp000001111011001 : Covers (-246011639/250000 : ℚ) vp000001111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111011000_0 : Blocks := edgeBlocks% "full/vectors/000001111011000-V-0000.bin"
noncomputable def vp000001111011000 : Blocks := vp000001111011000_0
theorem coverp000001111011000 : Covers (-245761639/250000 : ℚ) vp000001111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101100_0 : Blocks := edgeBlocks% "full/vectors/00000111101100-V-0000.bin"
noncomputable def vp00000111101100 : Blocks := vp00000111101100_0
private theorem bp000001111011000 : Branch 0 (-245761639/500000 : ℚ) vp00000111101100 := by
  apply branch_left_normalized (c:=vp000001111011000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-245761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-245761639/250000 : ℚ) by norm_num]
  exact coverp000001111011000
private noncomputable def ep000001111011001_0 : Blocks := edgeBlocks% "full/vectors/000001111011001-E-0000.bin"
noncomputable def ep000001111011001 : Blocks := ep000001111011001_0
private theorem idp000001111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101100.list =
    C ((2:ℤ)^52) * horner X vp000001111011001.list + horner X ep000001111011001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111011001 : Branch 1 (-245761639/500000 : ℚ) vp00000111101100 := by
  apply branch_checked idp000001111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-245761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-246011639/250000 : ℚ) by norm_num]
  exact coverp000001111011001
theorem coverp00000111101100 : Covers (-245761639/500000 : ℚ) vp00000111101100 := join_branches bp000001111011000 bp000001111011001
private noncomputable def vp0000011110110_0 : Blocks := edgeBlocks% "full/vectors/0000011110110-V-0000.bin"
noncomputable def vp0000011110110 : Blocks := vp0000011110110_0
private theorem bp00000111101100 : Branch 0 (-245761639/1000000 : ℚ) vp0000011110110 := by
  apply branch_left_normalized (c:=vp00000111101100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-245761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-245761639/500000 : ℚ) by norm_num]
  exact coverp00000111101100
private noncomputable def ep00000111101101_0 : Blocks := edgeBlocks% "full/vectors/00000111101101-E-0000.bin"
noncomputable def ep00000111101101 : Blocks := ep00000111101101_0
private theorem idp00000111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110110.list =
    C ((2:ℤ)^87) * horner X vp00000111101101.list + horner X ep00000111101101.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111101101 : Branch 1 (-245761639/1000000 : ℚ) vp0000011110110 := by
  apply branch_checked idp00000111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-245761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-246261639/500000 : ℚ) by norm_num]
  exact coverp00000111101101
theorem coverp0000011110110 : Covers (-245761639/1000000 : ℚ) vp0000011110110 := join_branches bp00000111101100 bp00000111101101
private noncomputable def vp000001111011_0 : Blocks := edgeBlocks% "full/vectors/000001111011-V-0000.bin"
private noncomputable def vp000001111011_1 : Blocks := edgeBlocks% "full/vectors/000001111011-V-0001.bin"
noncomputable def vp000001111011 : Blocks := (Blocks.join vp000001111011_0 vp000001111011_1)
private theorem bp0000011110110 : Branch 0 (-245761639/2000000 : ℚ) vp000001111011 := by
  apply branch_left_normalized (c:=vp0000011110110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-245761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-245761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110110
private noncomputable def ep0000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000011110111-E-0000.bin"
private noncomputable def ep0000011110111_1 : Blocks := edgeBlocks% "full/vectors/0000011110111-E-0001.bin"
noncomputable def ep0000011110111 : Blocks := (Blocks.join ep0000011110111_0 ep0000011110111_1)
private theorem idp0000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111011.list =
    C ((2:ℤ)^154) * horner X vp0000011110111.list + horner X ep0000011110111.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011110111 : Branch 1 (-245761639/2000000 : ℚ) vp000001111011 := by
  apply branch_checked idp0000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-245761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-246761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110111
theorem coverp000001111011 : Covers (-245761639/2000000 : ℚ) vp000001111011 := join_branches bp0000011110110 bp0000011110111
private noncomputable def vp000001111010111_0 : Blocks := edgeBlocks% "full/vectors/000001111010111-V-0000.bin"
noncomputable def vp000001111010111 : Blocks := vp000001111010111_0
theorem coverp000001111010111 : Covers (-245511639/250000 : ℚ) vp000001111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111010110_0 : Blocks := edgeBlocks% "full/vectors/000001111010110-V-0000.bin"
noncomputable def vp000001111010110 : Blocks := vp000001111010110_0
theorem coverp000001111010110 : Covers (-245261639/250000 : ℚ) vp000001111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101011_0 : Blocks := edgeBlocks% "full/vectors/00000111101011-V-0000.bin"
noncomputable def vp00000111101011 : Blocks := vp00000111101011_0
private theorem bp000001111010110 : Branch 0 (-245261639/500000 : ℚ) vp00000111101011 := by
  apply branch_left_normalized (c:=vp000001111010110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-245261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-245261639/250000 : ℚ) by norm_num]
  exact coverp000001111010110
private noncomputable def ep000001111010111_0 : Blocks := edgeBlocks% "full/vectors/000001111010111-E-0000.bin"
noncomputable def ep000001111010111 : Blocks := ep000001111010111_0
private theorem idp000001111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101011.list =
    C ((2:ℤ)^53) * horner X vp000001111010111.list + horner X ep000001111010111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111010111 : Branch 1 (-245261639/500000 : ℚ) vp00000111101011 := by
  apply branch_checked idp000001111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-245261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-245511639/250000 : ℚ) by norm_num]
  exact coverp000001111010111
theorem coverp00000111101011 : Covers (-245261639/500000 : ℚ) vp00000111101011 := join_branches bp000001111010110 bp000001111010111
private noncomputable def vp000001111010101_0 : Blocks := edgeBlocks% "full/vectors/000001111010101-V-0000.bin"
noncomputable def vp000001111010101 : Blocks := vp000001111010101_0
theorem coverp000001111010101 : Covers (-245011639/250000 : ℚ) vp000001111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111010100_0 : Blocks := edgeBlocks% "full/vectors/000001111010100-V-0000.bin"
noncomputable def vp000001111010100 : Blocks := vp000001111010100_0
theorem coverp000001111010100 : Covers (-244761639/250000 : ℚ) vp000001111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101010_0 : Blocks := edgeBlocks% "full/vectors/00000111101010-V-0000.bin"
noncomputable def vp00000111101010 : Blocks := vp00000111101010_0
private theorem bp000001111010100 : Branch 0 (-244761639/500000 : ℚ) vp00000111101010 := by
  apply branch_left_normalized (c:=vp000001111010100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-244761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-244761639/250000 : ℚ) by norm_num]
  exact coverp000001111010100
private noncomputable def ep000001111010101_0 : Blocks := edgeBlocks% "full/vectors/000001111010101-E-0000.bin"
noncomputable def ep000001111010101 : Blocks := ep000001111010101_0
private theorem idp000001111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101010.list =
    C ((2:ℤ)^54) * horner X vp000001111010101.list + horner X ep000001111010101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111010101 : Branch 1 (-244761639/500000 : ℚ) vp00000111101010 := by
  apply branch_checked idp000001111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-244761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-245011639/250000 : ℚ) by norm_num]
  exact coverp000001111010101
theorem coverp00000111101010 : Covers (-244761639/500000 : ℚ) vp00000111101010 := join_branches bp000001111010100 bp000001111010101
private noncomputable def vp0000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000011110101-V-0000.bin"
noncomputable def vp0000011110101 : Blocks := vp0000011110101_0
private theorem bp00000111101010 : Branch 0 (-244761639/1000000 : ℚ) vp0000011110101 := by
  apply branch_left_normalized (c:=vp00000111101010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-244761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-244761639/500000 : ℚ) by norm_num]
  exact coverp00000111101010
private noncomputable def ep00000111101011_0 : Blocks := edgeBlocks% "full/vectors/00000111101011-E-0000.bin"
noncomputable def ep00000111101011 : Blocks := ep00000111101011_0
private theorem idp00000111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110101.list =
    C ((2:ℤ)^89) * horner X vp00000111101011.list + horner X ep00000111101011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111101011 : Branch 1 (-244761639/1000000 : ℚ) vp0000011110101 := by
  apply branch_checked idp00000111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-244761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-245261639/500000 : ℚ) by norm_num]
  exact coverp00000111101011
theorem coverp0000011110101 : Covers (-244761639/1000000 : ℚ) vp0000011110101 := join_branches bp00000111101010 bp00000111101011
private noncomputable def vp000001111010011_0 : Blocks := edgeBlocks% "full/vectors/000001111010011-V-0000.bin"
noncomputable def vp000001111010011 : Blocks := vp000001111010011_0
theorem coverp000001111010011 : Covers (-244511639/250000 : ℚ) vp000001111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111010010_0 : Blocks := edgeBlocks% "full/vectors/000001111010010-V-0000.bin"
noncomputable def vp000001111010010 : Blocks := vp000001111010010_0
theorem coverp000001111010010 : Covers (-244261639/250000 : ℚ) vp000001111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101001_0 : Blocks := edgeBlocks% "full/vectors/00000111101001-V-0000.bin"
noncomputable def vp00000111101001 : Blocks := vp00000111101001_0
private theorem bp000001111010010 : Branch 0 (-244261639/500000 : ℚ) vp00000111101001 := by
  apply branch_left_normalized (c:=vp000001111010010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-244261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-244261639/250000 : ℚ) by norm_num]
  exact coverp000001111010010
private noncomputable def ep000001111010011_0 : Blocks := edgeBlocks% "full/vectors/000001111010011-E-0000.bin"
noncomputable def ep000001111010011 : Blocks := ep000001111010011_0
private theorem idp000001111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101001.list =
    C ((2:ℤ)^53) * horner X vp000001111010011.list + horner X ep000001111010011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111010011 : Branch 1 (-244261639/500000 : ℚ) vp00000111101001 := by
  apply branch_checked idp000001111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-244261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-244511639/250000 : ℚ) by norm_num]
  exact coverp000001111010011
theorem coverp00000111101001 : Covers (-244261639/500000 : ℚ) vp00000111101001 := join_branches bp000001111010010 bp000001111010011
private noncomputable def vp000001111010001_0 : Blocks := edgeBlocks% "full/vectors/000001111010001-V-0000.bin"
noncomputable def vp000001111010001 : Blocks := vp000001111010001_0
theorem coverp000001111010001 : Covers (-244011639/250000 : ℚ) vp000001111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111010000_0 : Blocks := edgeBlocks% "full/vectors/000001111010000-V-0000.bin"
noncomputable def vp000001111010000 : Blocks := vp000001111010000_0
theorem coverp000001111010000 : Covers (-243761639/250000 : ℚ) vp000001111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111101000_0 : Blocks := edgeBlocks% "full/vectors/00000111101000-V-0000.bin"
noncomputable def vp00000111101000 : Blocks := vp00000111101000_0
private theorem bp000001111010000 : Branch 0 (-243761639/500000 : ℚ) vp00000111101000 := by
  apply branch_left_normalized (c:=vp000001111010000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-243761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-243761639/250000 : ℚ) by norm_num]
  exact coverp000001111010000
private noncomputable def ep000001111010001_0 : Blocks := edgeBlocks% "full/vectors/000001111010001-E-0000.bin"
noncomputable def ep000001111010001 : Blocks := ep000001111010001_0
private theorem idp000001111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101000.list =
    C ((2:ℤ)^52) * horner X vp000001111010001.list + horner X ep000001111010001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111010001 : Branch 1 (-243761639/500000 : ℚ) vp00000111101000 := by
  apply branch_checked idp000001111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-243761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-244011639/250000 : ℚ) by norm_num]
  exact coverp000001111010001
theorem coverp00000111101000 : Covers (-243761639/500000 : ℚ) vp00000111101000 := join_branches bp000001111010000 bp000001111010001
private noncomputable def vp0000011110100_0 : Blocks := edgeBlocks% "full/vectors/0000011110100-V-0000.bin"
noncomputable def vp0000011110100 : Blocks := vp0000011110100_0
private theorem bp00000111101000 : Branch 0 (-243761639/1000000 : ℚ) vp0000011110100 := by
  apply branch_left_normalized (c:=vp00000111101000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-243761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-243761639/500000 : ℚ) by norm_num]
  exact coverp00000111101000
private noncomputable def ep00000111101001_0 : Blocks := edgeBlocks% "full/vectors/00000111101001-E-0000.bin"
noncomputable def ep00000111101001 : Blocks := ep00000111101001_0
private theorem idp00000111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110100.list =
    C ((2:ℤ)^86) * horner X vp00000111101001.list + horner X ep00000111101001.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111101001 : Branch 1 (-243761639/1000000 : ℚ) vp0000011110100 := by
  apply branch_checked idp00000111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-243761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-244261639/500000 : ℚ) by norm_num]
  exact coverp00000111101001
theorem coverp0000011110100 : Covers (-243761639/1000000 : ℚ) vp0000011110100 := join_branches bp00000111101000 bp00000111101001
private noncomputable def vp000001111010_0 : Blocks := edgeBlocks% "full/vectors/000001111010-V-0000.bin"
private noncomputable def vp000001111010_1 : Blocks := edgeBlocks% "full/vectors/000001111010-V-0001.bin"
noncomputable def vp000001111010 : Blocks := (Blocks.join vp000001111010_0 vp000001111010_1)
private theorem bp0000011110100 : Branch 0 (-243761639/2000000 : ℚ) vp000001111010 := by
  apply branch_left_normalized (c:=vp0000011110100) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-243761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-243761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110100
private noncomputable def ep0000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000011110101-E-0000.bin"
private noncomputable def ep0000011110101_1 : Blocks := edgeBlocks% "full/vectors/0000011110101-E-0001.bin"
noncomputable def ep0000011110101 : Blocks := (Blocks.join ep0000011110101_0 ep0000011110101_1)
private theorem idp0000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111010.list =
    C ((2:ℤ)^154) * horner X vp0000011110101.list + horner X ep0000011110101.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011110101 : Branch 1 (-243761639/2000000 : ℚ) vp000001111010 := by
  apply branch_checked idp0000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-243761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-244761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110101
theorem coverp000001111010 : Covers (-243761639/2000000 : ℚ) vp000001111010 := join_branches bp0000011110100 bp0000011110101
private noncomputable def vp00000111101_0 : Blocks := edgeBlocks% "full/vectors/00000111101-V-0000.bin"
private noncomputable def vp00000111101_1 : Blocks := edgeBlocks% "full/vectors/00000111101-V-0001.bin"
private noncomputable def vp00000111101_2 : Blocks := edgeBlocks% "full/vectors/00000111101-V-0002.bin"
noncomputable def vp00000111101 : Blocks := (Blocks.join vp00000111101_0 (Blocks.join vp00000111101_1 vp00000111101_2))
private theorem bp000001111010 : Branch 0 (-243761639/4000000 : ℚ) vp00000111101 := by
  apply branch_left_normalized (c:=vp000001111010) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-243761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-243761639/2000000 : ℚ) by norm_num]
  exact coverp000001111010
private noncomputable def ep000001111011_0 : Blocks := edgeBlocks% "full/vectors/000001111011-E-0000.bin"
private noncomputable def ep000001111011_1 : Blocks := edgeBlocks% "full/vectors/000001111011-E-0001.bin"
private noncomputable def ep000001111011_2 : Blocks := edgeBlocks% "full/vectors/000001111011-E-0002.bin"
noncomputable def ep000001111011 : Blocks := (Blocks.join ep000001111011_0 (Blocks.join ep000001111011_1 ep000001111011_2))
private theorem idp000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111101.list =
    C ((2:ℤ)^288) * horner X vp000001111011.list + horner X ep000001111011.list := by
  exact edge_identity (B := (2:ℤ)^510) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111011 : Branch 1 (-243761639/4000000 : ℚ) vp00000111101 := by
  apply branch_checked idp000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-243761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-245761639/2000000 : ℚ) by norm_num]
  exact coverp000001111011
theorem coverp00000111101 : Covers (-243761639/4000000 : ℚ) vp00000111101 := join_branches bp000001111010 bp000001111011
private noncomputable def vp000001111001111_0 : Blocks := edgeBlocks% "full/vectors/000001111001111-V-0000.bin"
noncomputable def vp000001111001111 : Blocks := vp000001111001111_0
theorem coverp000001111001111 : Covers (-243511639/250000 : ℚ) vp000001111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111001110_0 : Blocks := edgeBlocks% "full/vectors/000001111001110-V-0000.bin"
noncomputable def vp000001111001110 : Blocks := vp000001111001110_0
theorem coverp000001111001110 : Covers (-243261639/250000 : ℚ) vp000001111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100111_0 : Blocks := edgeBlocks% "full/vectors/00000111100111-V-0000.bin"
noncomputable def vp00000111100111 : Blocks := vp00000111100111_0
private theorem bp000001111001110 : Branch 0 (-243261639/500000 : ℚ) vp00000111100111 := by
  apply branch_left_normalized (c:=vp000001111001110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-243261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-243261639/250000 : ℚ) by norm_num]
  exact coverp000001111001110
private noncomputable def ep000001111001111_0 : Blocks := edgeBlocks% "full/vectors/000001111001111-E-0000.bin"
noncomputable def ep000001111001111 : Blocks := ep000001111001111_0
private theorem idp000001111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100111.list =
    C ((2:ℤ)^52) * horner X vp000001111001111.list + horner X ep000001111001111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111001111 : Branch 1 (-243261639/500000 : ℚ) vp00000111100111 := by
  apply branch_checked idp000001111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-243261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-243511639/250000 : ℚ) by norm_num]
  exact coverp000001111001111
theorem coverp00000111100111 : Covers (-243261639/500000 : ℚ) vp00000111100111 := join_branches bp000001111001110 bp000001111001111
private noncomputable def vp000001111001101_0 : Blocks := edgeBlocks% "full/vectors/000001111001101-V-0000.bin"
noncomputable def vp000001111001101 : Blocks := vp000001111001101_0
theorem coverp000001111001101 : Covers (-243011639/250000 : ℚ) vp000001111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111001100_0 : Blocks := edgeBlocks% "full/vectors/000001111001100-V-0000.bin"
noncomputable def vp000001111001100 : Blocks := vp000001111001100_0
theorem coverp000001111001100 : Covers (-242761639/250000 : ℚ) vp000001111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100110_0 : Blocks := edgeBlocks% "full/vectors/00000111100110-V-0000.bin"
noncomputable def vp00000111100110 : Blocks := vp00000111100110_0
private theorem bp000001111001100 : Branch 0 (-242761639/500000 : ℚ) vp00000111100110 := by
  apply branch_left_normalized (c:=vp000001111001100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-242761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-242761639/250000 : ℚ) by norm_num]
  exact coverp000001111001100
private noncomputable def ep000001111001101_0 : Blocks := edgeBlocks% "full/vectors/000001111001101-E-0000.bin"
noncomputable def ep000001111001101 : Blocks := ep000001111001101_0
private theorem idp000001111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100110.list =
    C ((2:ℤ)^53) * horner X vp000001111001101.list + horner X ep000001111001101.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111001101 : Branch 1 (-242761639/500000 : ℚ) vp00000111100110 := by
  apply branch_checked idp000001111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-242761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-243011639/250000 : ℚ) by norm_num]
  exact coverp000001111001101
theorem coverp00000111100110 : Covers (-242761639/500000 : ℚ) vp00000111100110 := join_branches bp000001111001100 bp000001111001101
private noncomputable def vp0000011110011_0 : Blocks := edgeBlocks% "full/vectors/0000011110011-V-0000.bin"
noncomputable def vp0000011110011 : Blocks := vp0000011110011_0
private theorem bp00000111100110 : Branch 0 (-242761639/1000000 : ℚ) vp0000011110011 := by
  apply branch_left_normalized (c:=vp00000111100110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-242761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-242761639/500000 : ℚ) by norm_num]
  exact coverp00000111100110
private noncomputable def ep00000111100111_0 : Blocks := edgeBlocks% "full/vectors/00000111100111-E-0000.bin"
noncomputable def ep00000111100111 : Blocks := ep00000111100111_0
private theorem idp00000111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110011.list =
    C ((2:ℤ)^87) * horner X vp00000111100111.list + horner X ep00000111100111.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111100111 : Branch 1 (-242761639/1000000 : ℚ) vp0000011110011 := by
  apply branch_checked idp00000111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-242761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-243261639/500000 : ℚ) by norm_num]
  exact coverp00000111100111
theorem coverp0000011110011 : Covers (-242761639/1000000 : ℚ) vp0000011110011 := join_branches bp00000111100110 bp00000111100111
private noncomputable def vp000001111001011_0 : Blocks := edgeBlocks% "full/vectors/000001111001011-V-0000.bin"
noncomputable def vp000001111001011 : Blocks := vp000001111001011_0
theorem coverp000001111001011 : Covers (-242511639/250000 : ℚ) vp000001111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111001010_0 : Blocks := edgeBlocks% "full/vectors/000001111001010-V-0000.bin"
noncomputable def vp000001111001010 : Blocks := vp000001111001010_0
theorem coverp000001111001010 : Covers (-242261639/250000 : ℚ) vp000001111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100101_0 : Blocks := edgeBlocks% "full/vectors/00000111100101-V-0000.bin"
noncomputable def vp00000111100101 : Blocks := vp00000111100101_0
private theorem bp000001111001010 : Branch 0 (-242261639/500000 : ℚ) vp00000111100101 := by
  apply branch_left_normalized (c:=vp000001111001010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-242261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-242261639/250000 : ℚ) by norm_num]
  exact coverp000001111001010
private noncomputable def ep000001111001011_0 : Blocks := edgeBlocks% "full/vectors/000001111001011-E-0000.bin"
noncomputable def ep000001111001011 : Blocks := ep000001111001011_0
private theorem idp000001111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100101.list =
    C ((2:ℤ)^53) * horner X vp000001111001011.list + horner X ep000001111001011.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111001011 : Branch 1 (-242261639/500000 : ℚ) vp00000111100101 := by
  apply branch_checked idp000001111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-242261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-242511639/250000 : ℚ) by norm_num]
  exact coverp000001111001011
theorem coverp00000111100101 : Covers (-242261639/500000 : ℚ) vp00000111100101 := join_branches bp000001111001010 bp000001111001011
private noncomputable def vp000001111001001_0 : Blocks := edgeBlocks% "full/vectors/000001111001001-V-0000.bin"
noncomputable def vp000001111001001 : Blocks := vp000001111001001_0
theorem coverp000001111001001 : Covers (-242011639/250000 : ℚ) vp000001111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111001000_0 : Blocks := edgeBlocks% "full/vectors/000001111001000-V-0000.bin"
noncomputable def vp000001111001000 : Blocks := vp000001111001000_0
theorem coverp000001111001000 : Covers (-241761639/250000 : ℚ) vp000001111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100100_0 : Blocks := edgeBlocks% "full/vectors/00000111100100-V-0000.bin"
noncomputable def vp00000111100100 : Blocks := vp00000111100100_0
private theorem bp000001111001000 : Branch 0 (-241761639/500000 : ℚ) vp00000111100100 := by
  apply branch_left_normalized (c:=vp000001111001000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-241761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-241761639/250000 : ℚ) by norm_num]
  exact coverp000001111001000
private noncomputable def ep000001111001001_0 : Blocks := edgeBlocks% "full/vectors/000001111001001-E-0000.bin"
noncomputable def ep000001111001001 : Blocks := ep000001111001001_0
private theorem idp000001111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100100.list =
    C ((2:ℤ)^54) * horner X vp000001111001001.list + horner X ep000001111001001.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111001001 : Branch 1 (-241761639/500000 : ℚ) vp00000111100100 := by
  apply branch_checked idp000001111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-241761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-242011639/250000 : ℚ) by norm_num]
  exact coverp000001111001001
theorem coverp00000111100100 : Covers (-241761639/500000 : ℚ) vp00000111100100 := join_branches bp000001111001000 bp000001111001001
private noncomputable def vp0000011110010_0 : Blocks := edgeBlocks% "full/vectors/0000011110010-V-0000.bin"
noncomputable def vp0000011110010 : Blocks := vp0000011110010_0
private theorem bp00000111100100 : Branch 0 (-241761639/1000000 : ℚ) vp0000011110010 := by
  apply branch_left_normalized (c:=vp00000111100100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-241761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-241761639/500000 : ℚ) by norm_num]
  exact coverp00000111100100
private noncomputable def ep00000111100101_0 : Blocks := edgeBlocks% "full/vectors/00000111100101-E-0000.bin"
noncomputable def ep00000111100101 : Blocks := ep00000111100101_0
private theorem idp00000111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110010.list =
    C ((2:ℤ)^88) * horner X vp00000111100101.list + horner X ep00000111100101.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111100101 : Branch 1 (-241761639/1000000 : ℚ) vp0000011110010 := by
  apply branch_checked idp00000111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-241761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-242261639/500000 : ℚ) by norm_num]
  exact coverp00000111100101
theorem coverp0000011110010 : Covers (-241761639/1000000 : ℚ) vp0000011110010 := join_branches bp00000111100100 bp00000111100101
private noncomputable def vp000001111001_0 : Blocks := edgeBlocks% "full/vectors/000001111001-V-0000.bin"
private noncomputable def vp000001111001_1 : Blocks := edgeBlocks% "full/vectors/000001111001-V-0001.bin"
noncomputable def vp000001111001 : Blocks := (Blocks.join vp000001111001_0 vp000001111001_1)
private theorem bp0000011110010 : Branch 0 (-241761639/2000000 : ℚ) vp000001111001 := by
  apply branch_left_normalized (c:=vp0000011110010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-241761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-241761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110010
private noncomputable def ep0000011110011_0 : Blocks := edgeBlocks% "full/vectors/0000011110011-E-0000.bin"
private noncomputable def ep0000011110011_1 : Blocks := edgeBlocks% "full/vectors/0000011110011-E-0001.bin"
noncomputable def ep0000011110011 : Blocks := (Blocks.join ep0000011110011_0 ep0000011110011_1)
private theorem idp0000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111001.list =
    C ((2:ℤ)^154) * horner X vp0000011110011.list + horner X ep0000011110011.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011110011 : Branch 1 (-241761639/2000000 : ℚ) vp000001111001 := by
  apply branch_checked idp0000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-241761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-242761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110011
theorem coverp000001111001 : Covers (-241761639/2000000 : ℚ) vp000001111001 := join_branches bp0000011110010 bp0000011110011
private noncomputable def vp000001111000111_0 : Blocks := edgeBlocks% "full/vectors/000001111000111-V-0000.bin"
noncomputable def vp000001111000111 : Blocks := vp000001111000111_0
theorem coverp000001111000111 : Covers (-241511639/250000 : ℚ) vp000001111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111000110_0 : Blocks := edgeBlocks% "full/vectors/000001111000110-V-0000.bin"
noncomputable def vp000001111000110 : Blocks := vp000001111000110_0
theorem coverp000001111000110 : Covers (-241261639/250000 : ℚ) vp000001111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100011_0 : Blocks := edgeBlocks% "full/vectors/00000111100011-V-0000.bin"
noncomputable def vp00000111100011 : Blocks := vp00000111100011_0
private theorem bp000001111000110 : Branch 0 (-241261639/500000 : ℚ) vp00000111100011 := by
  apply branch_left_normalized (c:=vp000001111000110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-241261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-241261639/250000 : ℚ) by norm_num]
  exact coverp000001111000110
private noncomputable def ep000001111000111_0 : Blocks := edgeBlocks% "full/vectors/000001111000111-E-0000.bin"
noncomputable def ep000001111000111 : Blocks := ep000001111000111_0
private theorem idp000001111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100011.list =
    C ((2:ℤ)^52) * horner X vp000001111000111.list + horner X ep000001111000111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111000111 : Branch 1 (-241261639/500000 : ℚ) vp00000111100011 := by
  apply branch_checked idp000001111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-241261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-241511639/250000 : ℚ) by norm_num]
  exact coverp000001111000111
theorem coverp00000111100011 : Covers (-241261639/500000 : ℚ) vp00000111100011 := join_branches bp000001111000110 bp000001111000111
private noncomputable def vp000001111000101_0 : Blocks := edgeBlocks% "full/vectors/000001111000101-V-0000.bin"
noncomputable def vp000001111000101 : Blocks := vp000001111000101_0
theorem coverp000001111000101 : Covers (-241011639/250000 : ℚ) vp000001111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111000100_0 : Blocks := edgeBlocks% "full/vectors/000001111000100-V-0000.bin"
noncomputable def vp000001111000100 : Blocks := vp000001111000100_0
theorem coverp000001111000100 : Covers (-240761639/250000 : ℚ) vp000001111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100010_0 : Blocks := edgeBlocks% "full/vectors/00000111100010-V-0000.bin"
noncomputable def vp00000111100010 : Blocks := vp00000111100010_0
private theorem bp000001111000100 : Branch 0 (-240761639/500000 : ℚ) vp00000111100010 := by
  apply branch_left_normalized (c:=vp000001111000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-240761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-240761639/250000 : ℚ) by norm_num]
  exact coverp000001111000100
private noncomputable def ep000001111000101_0 : Blocks := edgeBlocks% "full/vectors/000001111000101-E-0000.bin"
noncomputable def ep000001111000101 : Blocks := ep000001111000101_0
private theorem idp000001111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100010.list =
    C ((2:ℤ)^54) * horner X vp000001111000101.list + horner X ep000001111000101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111000101 : Branch 1 (-240761639/500000 : ℚ) vp00000111100010 := by
  apply branch_checked idp000001111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-240761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-241011639/250000 : ℚ) by norm_num]
  exact coverp000001111000101
theorem coverp00000111100010 : Covers (-240761639/500000 : ℚ) vp00000111100010 := join_branches bp000001111000100 bp000001111000101
private noncomputable def vp0000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000011110001-V-0000.bin"
noncomputable def vp0000011110001 : Blocks := vp0000011110001_0
private theorem bp00000111100010 : Branch 0 (-240761639/1000000 : ℚ) vp0000011110001 := by
  apply branch_left_normalized (c:=vp00000111100010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-240761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-240761639/500000 : ℚ) by norm_num]
  exact coverp00000111100010
private noncomputable def ep00000111100011_0 : Blocks := edgeBlocks% "full/vectors/00000111100011-E-0000.bin"
noncomputable def ep00000111100011 : Blocks := ep00000111100011_0
private theorem idp00000111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110001.list =
    C ((2:ℤ)^90) * horner X vp00000111100011.list + horner X ep00000111100011.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111100011 : Branch 1 (-240761639/1000000 : ℚ) vp0000011110001 := by
  apply branch_checked idp00000111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-240761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-241261639/500000 : ℚ) by norm_num]
  exact coverp00000111100011
theorem coverp0000011110001 : Covers (-240761639/1000000 : ℚ) vp0000011110001 := join_branches bp00000111100010 bp00000111100011
private noncomputable def vp000001111000011_0 : Blocks := edgeBlocks% "full/vectors/000001111000011-V-0000.bin"
noncomputable def vp000001111000011 : Blocks := vp000001111000011_0
theorem coverp000001111000011 : Covers (-240511639/250000 : ℚ) vp000001111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111000010_0 : Blocks := edgeBlocks% "full/vectors/000001111000010-V-0000.bin"
noncomputable def vp000001111000010 : Blocks := vp000001111000010_0
theorem coverp000001111000010 : Covers (-240261639/250000 : ℚ) vp000001111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000111100001-V-0000.bin"
noncomputable def vp00000111100001 : Blocks := vp00000111100001_0
private theorem bp000001111000010 : Branch 0 (-240261639/500000 : ℚ) vp00000111100001 := by
  apply branch_left_normalized (c:=vp000001111000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-240261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-240261639/250000 : ℚ) by norm_num]
  exact coverp000001111000010
private noncomputable def ep000001111000011_0 : Blocks := edgeBlocks% "full/vectors/000001111000011-E-0000.bin"
noncomputable def ep000001111000011 : Blocks := ep000001111000011_0
private theorem idp000001111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100001.list =
    C ((2:ℤ)^53) * horner X vp000001111000011.list + horner X ep000001111000011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111000011 : Branch 1 (-240261639/500000 : ℚ) vp00000111100001 := by
  apply branch_checked idp000001111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-240261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-240511639/250000 : ℚ) by norm_num]
  exact coverp000001111000011
theorem coverp00000111100001 : Covers (-240261639/500000 : ℚ) vp00000111100001 := join_branches bp000001111000010 bp000001111000011
private noncomputable def vp000001111000001_0 : Blocks := edgeBlocks% "full/vectors/000001111000001-V-0000.bin"
noncomputable def vp000001111000001 : Blocks := vp000001111000001_0
theorem coverp000001111000001 : Covers (-240011639/250000 : ℚ) vp000001111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001111000000_0 : Blocks := edgeBlocks% "full/vectors/000001111000000-V-0000.bin"
noncomputable def vp000001111000000 : Blocks := vp000001111000000_0
theorem coverp000001111000000 : Covers (-239761639/250000 : ℚ) vp000001111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111100000_0 : Blocks := edgeBlocks% "full/vectors/00000111100000-V-0000.bin"
noncomputable def vp00000111100000 : Blocks := vp00000111100000_0
private theorem bp000001111000000 : Branch 0 (-239761639/500000 : ℚ) vp00000111100000 := by
  apply branch_left_normalized (c:=vp000001111000000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-239761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/250000 : ℚ) by norm_num]
  exact coverp000001111000000
private noncomputable def ep000001111000001_0 : Blocks := edgeBlocks% "full/vectors/000001111000001-E-0000.bin"
noncomputable def ep000001111000001 : Blocks := ep000001111000001_0
private theorem idp000001111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100000.list =
    C ((2:ℤ)^53) * horner X vp000001111000001.list + horner X ep000001111000001.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111000001 : Branch 1 (-239761639/500000 : ℚ) vp00000111100000 := by
  apply branch_checked idp000001111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-240011639/250000 : ℚ) by norm_num]
  exact coverp000001111000001
theorem coverp00000111100000 : Covers (-239761639/500000 : ℚ) vp00000111100000 := join_branches bp000001111000000 bp000001111000001
private noncomputable def vp0000011110000_0 : Blocks := edgeBlocks% "full/vectors/0000011110000-V-0000.bin"
noncomputable def vp0000011110000 : Blocks := vp0000011110000_0
private theorem bp00000111100000 : Branch 0 (-239761639/1000000 : ℚ) vp0000011110000 := by
  apply branch_left_normalized (c:=vp00000111100000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-239761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/500000 : ℚ) by norm_num]
  exact coverp00000111100000
private noncomputable def ep00000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000111100001-E-0000.bin"
noncomputable def ep00000111100001 : Blocks := ep00000111100001_0
private theorem idp00000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110000.list =
    C ((2:ℤ)^89) * horner X vp00000111100001.list + horner X ep00000111100001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111100001 : Branch 1 (-239761639/1000000 : ℚ) vp0000011110000 := by
  apply branch_checked idp00000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-240261639/500000 : ℚ) by norm_num]
  exact coverp00000111100001
theorem coverp0000011110000 : Covers (-239761639/1000000 : ℚ) vp0000011110000 := join_branches bp00000111100000 bp00000111100001
private noncomputable def vp000001111000_0 : Blocks := edgeBlocks% "full/vectors/000001111000-V-0000.bin"
private noncomputable def vp000001111000_1 : Blocks := edgeBlocks% "full/vectors/000001111000-V-0001.bin"
noncomputable def vp000001111000 : Blocks := (Blocks.join vp000001111000_0 vp000001111000_1)
private theorem bp0000011110000 : Branch 0 (-239761639/2000000 : ℚ) vp000001111000 := by
  apply branch_left_normalized (c:=vp0000011110000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-239761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110000
private noncomputable def ep0000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000011110001-E-0000.bin"
private noncomputable def ep0000011110001_1 : Blocks := edgeBlocks% "full/vectors/0000011110001-E-0001.bin"
noncomputable def ep0000011110001 : Blocks := (Blocks.join ep0000011110001_0 ep0000011110001_1)
private theorem idp0000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111000.list =
    C ((2:ℤ)^156) * horner X vp0000011110001.list + horner X ep0000011110001.list := by
  exact edge_identity (B := (2:ℤ)^320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011110001 : Branch 1 (-239761639/2000000 : ℚ) vp000001111000 := by
  apply branch_checked idp0000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-240761639/1000000 : ℚ) by norm_num]
  exact coverp0000011110001
theorem coverp000001111000 : Covers (-239761639/2000000 : ℚ) vp000001111000 := join_branches bp0000011110000 bp0000011110001
private noncomputable def vp00000111100_0 : Blocks := edgeBlocks% "full/vectors/00000111100-V-0000.bin"
private noncomputable def vp00000111100_1 : Blocks := edgeBlocks% "full/vectors/00000111100-V-0001.bin"
private noncomputable def vp00000111100_2 : Blocks := edgeBlocks% "full/vectors/00000111100-V-0002.bin"
noncomputable def vp00000111100 : Blocks := (Blocks.join vp00000111100_0 (Blocks.join vp00000111100_1 vp00000111100_2))
private theorem bp000001111000 : Branch 0 (-239761639/4000000 : ℚ) vp00000111100 := by
  apply branch_left_normalized (c:=vp000001111000) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-239761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/2000000 : ℚ) by norm_num]
  exact coverp000001111000
private noncomputable def ep000001111001_0 : Blocks := edgeBlocks% "full/vectors/000001111001-E-0000.bin"
private noncomputable def ep000001111001_1 : Blocks := edgeBlocks% "full/vectors/000001111001-E-0001.bin"
private noncomputable def ep000001111001_2 : Blocks := edgeBlocks% "full/vectors/000001111001-E-0002.bin"
noncomputable def ep000001111001 : Blocks := (Blocks.join ep000001111001_0 (Blocks.join ep000001111001_1 ep000001111001_2))
private theorem idp000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111100.list =
    C ((2:ℤ)^290) * horner X vp000001111001.list + horner X ep000001111001.list := by
  exact edge_identity (B := (2:ℤ)^514) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111001 : Branch 1 (-239761639/4000000 : ℚ) vp00000111100 := by
  apply branch_checked idp000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-241761639/2000000 : ℚ) by norm_num]
  exact coverp000001111001
theorem coverp00000111100 : Covers (-239761639/4000000 : ℚ) vp00000111100 := join_branches bp000001111000 bp000001111001
private noncomputable def vp0000011110_0 : Blocks := edgeBlocks% "full/vectors/0000011110-V-0000.bin"
private noncomputable def vp0000011110_1 : Blocks := edgeBlocks% "full/vectors/0000011110-V-0001.bin"
private noncomputable def vp0000011110_2 : Blocks := edgeBlocks% "full/vectors/0000011110-V-0002.bin"
private noncomputable def vp0000011110_3 : Blocks := edgeBlocks% "full/vectors/0000011110-V-0003.bin"
private noncomputable def vp0000011110_4 : Blocks := edgeBlocks% "full/vectors/0000011110-V-0004.bin"
noncomputable def vp0000011110 : Blocks := (Blocks.join (Blocks.join vp0000011110_0 vp0000011110_1) (Blocks.join vp0000011110_2 (Blocks.join vp0000011110_3 vp0000011110_4)))
private theorem bp00000111100 : Branch 0 (-239761639/8000000 : ℚ) vp0000011110 := by
  apply branch_left_normalized (c:=vp00000111100) (k:=0) (m:=276) (by decide +kernel)
  rw [show 2*(-239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/4000000 : ℚ) by norm_num]
  exact coverp00000111100
private noncomputable def ep00000111101_0 : Blocks := edgeBlocks% "full/vectors/00000111101-E-0000.bin"
private noncomputable def ep00000111101_1 : Blocks := edgeBlocks% "full/vectors/00000111101-E-0001.bin"
private noncomputable def ep00000111101_2 : Blocks := edgeBlocks% "full/vectors/00000111101-E-0002.bin"
private noncomputable def ep00000111101_3 : Blocks := edgeBlocks% "full/vectors/00000111101-E-0003.bin"
private noncomputable def ep00000111101_4 : Blocks := edgeBlocks% "full/vectors/00000111101-E-0004.bin"
noncomputable def ep00000111101 : Blocks := (Blocks.join (Blocks.join ep00000111101_0 ep00000111101_1) (Blocks.join ep00000111101_2 (Blocks.join ep00000111101_3 ep00000111101_4)))
private theorem idp00000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011110.list =
    C ((2:ℤ)^552) * horner X vp00000111101.list + horner X ep00000111101.list := by
  exact edge_identity (B := (2:ℤ)^899) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111101 : Branch 1 (-239761639/8000000 : ℚ) vp0000011110 := by
  apply branch_checked idp00000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-243761639/4000000 : ℚ) by norm_num]
  exact coverp00000111101
theorem coverp0000011110 : Covers (-239761639/8000000 : ℚ) vp0000011110 := join_branches bp00000111100 bp00000111101
private noncomputable def vp000001111_0 : Blocks := edgeBlocks% "full/vectors/000001111-V-0000.bin"
private noncomputable def vp000001111_1 : Blocks := edgeBlocks% "full/vectors/000001111-V-0001.bin"
private noncomputable def vp000001111_2 : Blocks := edgeBlocks% "full/vectors/000001111-V-0002.bin"
private noncomputable def vp000001111_3 : Blocks := edgeBlocks% "full/vectors/000001111-V-0003.bin"
private noncomputable def vp000001111_4 : Blocks := edgeBlocks% "full/vectors/000001111-V-0004.bin"
private noncomputable def vp000001111_5 : Blocks := edgeBlocks% "full/vectors/000001111-V-0005.bin"
private noncomputable def vp000001111_6 : Blocks := edgeBlocks% "full/vectors/000001111-V-0006.bin"
private noncomputable def vp000001111_7 : Blocks := edgeBlocks% "full/vectors/000001111-V-0007.bin"
private noncomputable def vp000001111_8 : Blocks := edgeBlocks% "full/vectors/000001111-V-0008.bin"
noncomputable def vp000001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001111_0 vp000001111_1) (Blocks.join vp000001111_2 vp000001111_3)) (Blocks.join (Blocks.join vp000001111_4 vp000001111_5) (Blocks.join vp000001111_6 (Blocks.join vp000001111_7 vp000001111_8))))
private theorem bp0000011110 : Branch 0 (-239761639/16000000 : ℚ) vp000001111 := by
  apply branch_left_normalized (c:=vp0000011110) (k:=0) (m:=527) (by decide +kernel)
  rw [show 2*(-239761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-239761639/8000000 : ℚ) by norm_num]
  exact coverp0000011110
private noncomputable def ep0000011111_0 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0000.bin"
private noncomputable def ep0000011111_1 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0001.bin"
private noncomputable def ep0000011111_2 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0002.bin"
private noncomputable def ep0000011111_3 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0003.bin"
private noncomputable def ep0000011111_4 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0004.bin"
private noncomputable def ep0000011111_5 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0005.bin"
private noncomputable def ep0000011111_6 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0006.bin"
private noncomputable def ep0000011111_7 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0007.bin"
private noncomputable def ep0000011111_8 : Blocks := edgeBlocks% "full/vectors/0000011111-E-0008.bin"
noncomputable def ep0000011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000011111_0 ep0000011111_1) (Blocks.join ep0000011111_2 ep0000011111_3)) (Blocks.join (Blocks.join ep0000011111_4 ep0000011111_5) (Blocks.join ep0000011111_6 (Blocks.join ep0000011111_7 ep0000011111_8))))
private theorem idp0000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001111.list =
    C ((2:ℤ)^1073) * horner X vp0000011111.list + horner X ep0000011111.list := by
  exact edge_identity (B := (2:ℤ)^1664) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011111 : Branch 1 (-239761639/16000000 : ℚ) vp000001111 := by
  apply branch_checked idp0000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-239761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-247761639/8000000 : ℚ) by norm_num]
  exact coverp0000011111
theorem coverp000001111 : Covers (-239761639/16000000 : ℚ) vp000001111 := join_branches bp0000011110 bp0000011111
end NextProof.EdgeFull

