import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00052

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00001001111111_0 : Blocks := edgeBlocks% "full/vectors/00001001111111-V-0000.bin"
noncomputable def vp00001001111111 : Blocks := vp00001001111111_0
theorem coverp00001001111111 : Covers (-319261639/500000 : ℚ) vp00001001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001111110_0 : Blocks := edgeBlocks% "full/vectors/00001001111110-V-0000.bin"
noncomputable def vp00001001111110 : Blocks := vp00001001111110_0
theorem coverp00001001111110 : Covers (-318761639/500000 : ℚ) vp00001001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000100111111-V-0000.bin"
noncomputable def vp0000100111111 : Blocks := vp0000100111111_0
private theorem bp00001001111110 : Branch 0 (-318761639/1000000 : ℚ) vp0000100111111 := by
  apply branch_left_normalized (c:=vp00001001111110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-318761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-318761639/500000 : ℚ) by norm_num]
  exact coverp00001001111110
private noncomputable def ep00001001111111_0 : Blocks := edgeBlocks% "full/vectors/00001001111111-E-0000.bin"
noncomputable def ep00001001111111 : Blocks := ep00001001111111_0
private theorem idp00001001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111111.list =
    C ((2:ℤ)^74) * horner X vp00001001111111.list + horner X ep00001001111111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001111111 : Branch 1 (-318761639/1000000 : ℚ) vp0000100111111 := by
  apply branch_checked idp00001001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-318761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-319261639/500000 : ℚ) by norm_num]
  exact coverp00001001111111
theorem coverp0000100111111 : Covers (-318761639/1000000 : ℚ) vp0000100111111 := join_branches bp00001001111110 bp00001001111111
private noncomputable def vp00001001111101_0 : Blocks := edgeBlocks% "full/vectors/00001001111101-V-0000.bin"
noncomputable def vp00001001111101 : Blocks := vp00001001111101_0
theorem coverp00001001111101 : Covers (-318261639/500000 : ℚ) vp00001001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001111100_0 : Blocks := edgeBlocks% "full/vectors/00001001111100-V-0000.bin"
noncomputable def vp00001001111100 : Blocks := vp00001001111100_0
theorem coverp00001001111100 : Covers (-317761639/500000 : ℚ) vp00001001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111110_0 : Blocks := edgeBlocks% "full/vectors/0000100111110-V-0000.bin"
noncomputable def vp0000100111110 : Blocks := vp0000100111110_0
private theorem bp00001001111100 : Branch 0 (-317761639/1000000 : ℚ) vp0000100111110 := by
  apply branch_left_normalized (c:=vp00001001111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-317761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-317761639/500000 : ℚ) by norm_num]
  exact coverp00001001111100
private noncomputable def ep00001001111101_0 : Blocks := edgeBlocks% "full/vectors/00001001111101-E-0000.bin"
noncomputable def ep00001001111101 : Blocks := ep00001001111101_0
private theorem idp00001001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111110.list =
    C ((2:ℤ)^74) * horner X vp00001001111101.list + horner X ep00001001111101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001111101 : Branch 1 (-317761639/1000000 : ℚ) vp0000100111110 := by
  apply branch_checked idp00001001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-317761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-318261639/500000 : ℚ) by norm_num]
  exact coverp00001001111101
theorem coverp0000100111110 : Covers (-317761639/1000000 : ℚ) vp0000100111110 := join_branches bp00001001111100 bp00001001111101
private noncomputable def vp000010011111_0 : Blocks := edgeBlocks% "full/vectors/000010011111-V-0000.bin"
noncomputable def vp000010011111 : Blocks := vp000010011111_0
private theorem bp0000100111110 : Branch 0 (-317761639/2000000 : ℚ) vp000010011111 := by
  apply branch_left_normalized (c:=vp0000100111110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-317761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-317761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111110
private noncomputable def ep0000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000100111111-E-0000.bin"
noncomputable def ep0000100111111 : Blocks := ep0000100111111_0
private theorem idp0000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011111.list =
    C ((2:ℤ)^132) * horner X vp0000100111111.list + horner X ep0000100111111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100111111 : Branch 1 (-317761639/2000000 : ℚ) vp000010011111 := by
  apply branch_checked idp0000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-317761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-318761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111111
theorem coverp000010011111 : Covers (-317761639/2000000 : ℚ) vp000010011111 := join_branches bp0000100111110 bp0000100111111
private noncomputable def vp00001001111011_0 : Blocks := edgeBlocks% "full/vectors/00001001111011-V-0000.bin"
noncomputable def vp00001001111011 : Blocks := vp00001001111011_0
theorem coverp00001001111011 : Covers (-317261639/500000 : ℚ) vp00001001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001111010_0 : Blocks := edgeBlocks% "full/vectors/00001001111010-V-0000.bin"
noncomputable def vp00001001111010 : Blocks := vp00001001111010_0
theorem coverp00001001111010 : Covers (-316761639/500000 : ℚ) vp00001001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111101_0 : Blocks := edgeBlocks% "full/vectors/0000100111101-V-0000.bin"
noncomputable def vp0000100111101 : Blocks := vp0000100111101_0
private theorem bp00001001111010 : Branch 0 (-316761639/1000000 : ℚ) vp0000100111101 := by
  apply branch_left_normalized (c:=vp00001001111010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-316761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-316761639/500000 : ℚ) by norm_num]
  exact coverp00001001111010
private noncomputable def ep00001001111011_0 : Blocks := edgeBlocks% "full/vectors/00001001111011-E-0000.bin"
noncomputable def ep00001001111011 : Blocks := ep00001001111011_0
private theorem idp00001001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111101.list =
    C ((2:ℤ)^74) * horner X vp00001001111011.list + horner X ep00001001111011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001111011 : Branch 1 (-316761639/1000000 : ℚ) vp0000100111101 := by
  apply branch_checked idp00001001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-316761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-317261639/500000 : ℚ) by norm_num]
  exact coverp00001001111011
theorem coverp0000100111101 : Covers (-316761639/1000000 : ℚ) vp0000100111101 := join_branches bp00001001111010 bp00001001111011
private noncomputable def vp00001001111001_0 : Blocks := edgeBlocks% "full/vectors/00001001111001-V-0000.bin"
noncomputable def vp00001001111001 : Blocks := vp00001001111001_0
theorem coverp00001001111001 : Covers (-316261639/500000 : ℚ) vp00001001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001111000_0 : Blocks := edgeBlocks% "full/vectors/00001001111000-V-0000.bin"
noncomputable def vp00001001111000 : Blocks := vp00001001111000_0
theorem coverp00001001111000 : Covers (-315761639/500000 : ℚ) vp00001001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111100_0 : Blocks := edgeBlocks% "full/vectors/0000100111100-V-0000.bin"
noncomputable def vp0000100111100 : Blocks := vp0000100111100_0
private theorem bp00001001111000 : Branch 0 (-315761639/1000000 : ℚ) vp0000100111100 := by
  apply branch_left_normalized (c:=vp00001001111000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-315761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-315761639/500000 : ℚ) by norm_num]
  exact coverp00001001111000
private noncomputable def ep00001001111001_0 : Blocks := edgeBlocks% "full/vectors/00001001111001-E-0000.bin"
noncomputable def ep00001001111001 : Blocks := ep00001001111001_0
private theorem idp00001001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111100.list =
    C ((2:ℤ)^74) * horner X vp00001001111001.list + horner X ep00001001111001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001111001 : Branch 1 (-315761639/1000000 : ℚ) vp0000100111100 := by
  apply branch_checked idp00001001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-315761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-316261639/500000 : ℚ) by norm_num]
  exact coverp00001001111001
theorem coverp0000100111100 : Covers (-315761639/1000000 : ℚ) vp0000100111100 := join_branches bp00001001111000 bp00001001111001
private noncomputable def vp000010011110_0 : Blocks := edgeBlocks% "full/vectors/000010011110-V-0000.bin"
noncomputable def vp000010011110 : Blocks := vp000010011110_0
private theorem bp0000100111100 : Branch 0 (-315761639/2000000 : ℚ) vp000010011110 := by
  apply branch_left_normalized (c:=vp0000100111100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-315761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-315761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111100
private noncomputable def ep0000100111101_0 : Blocks := edgeBlocks% "full/vectors/0000100111101-E-0000.bin"
noncomputable def ep0000100111101 : Blocks := ep0000100111101_0
private theorem idp0000100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011110.list =
    C ((2:ℤ)^132) * horner X vp0000100111101.list + horner X ep0000100111101.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100111101 : Branch 1 (-315761639/2000000 : ℚ) vp000010011110 := by
  apply branch_checked idp0000100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-315761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-316761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111101
theorem coverp000010011110 : Covers (-315761639/2000000 : ℚ) vp000010011110 := join_branches bp0000100111100 bp0000100111101
private noncomputable def vp00001001111_0 : Blocks := edgeBlocks% "full/vectors/00001001111-V-0000.bin"
private noncomputable def vp00001001111_1 : Blocks := edgeBlocks% "full/vectors/00001001111-V-0001.bin"
noncomputable def vp00001001111 : Blocks := (Blocks.join vp00001001111_0 vp00001001111_1)
private theorem bp000010011110 : Branch 0 (-315761639/4000000 : ℚ) vp00001001111 := by
  apply branch_left_normalized (c:=vp000010011110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-315761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-315761639/2000000 : ℚ) by norm_num]
  exact coverp000010011110
private noncomputable def ep000010011111_0 : Blocks := edgeBlocks% "full/vectors/000010011111-E-0000.bin"
private noncomputable def ep000010011111_1 : Blocks := edgeBlocks% "full/vectors/000010011111-E-0001.bin"
noncomputable def ep000010011111 : Blocks := (Blocks.join ep000010011111_0 ep000010011111_1)
private theorem idp000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001111.list =
    C ((2:ℤ)^248) * horner X vp000010011111.list + horner X ep000010011111.list := by
  exact edge_identity (B := (2:ℤ)^445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010011111 : Branch 1 (-315761639/4000000 : ℚ) vp00001001111 := by
  apply branch_checked idp000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-315761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-317761639/2000000 : ℚ) by norm_num]
  exact coverp000010011111
theorem coverp00001001111 : Covers (-315761639/4000000 : ℚ) vp00001001111 := join_branches bp000010011110 bp000010011111
private noncomputable def vp00001001110111_0 : Blocks := edgeBlocks% "full/vectors/00001001110111-V-0000.bin"
noncomputable def vp00001001110111 : Blocks := vp00001001110111_0
theorem coverp00001001110111 : Covers (-315261639/500000 : ℚ) vp00001001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001110110_0 : Blocks := edgeBlocks% "full/vectors/00001001110110-V-0000.bin"
noncomputable def vp00001001110110 : Blocks := vp00001001110110_0
theorem coverp00001001110110 : Covers (-314761639/500000 : ℚ) vp00001001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111011_0 : Blocks := edgeBlocks% "full/vectors/0000100111011-V-0000.bin"
noncomputable def vp0000100111011 : Blocks := vp0000100111011_0
private theorem bp00001001110110 : Branch 0 (-314761639/1000000 : ℚ) vp0000100111011 := by
  apply branch_left_normalized (c:=vp00001001110110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-314761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-314761639/500000 : ℚ) by norm_num]
  exact coverp00001001110110
private noncomputable def ep00001001110111_0 : Blocks := edgeBlocks% "full/vectors/00001001110111-E-0000.bin"
noncomputable def ep00001001110111 : Blocks := ep00001001110111_0
private theorem idp00001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111011.list =
    C ((2:ℤ)^73) * horner X vp00001001110111.list + horner X ep00001001110111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001110111 : Branch 1 (-314761639/1000000 : ℚ) vp0000100111011 := by
  apply branch_checked idp00001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-314761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-315261639/500000 : ℚ) by norm_num]
  exact coverp00001001110111
theorem coverp0000100111011 : Covers (-314761639/1000000 : ℚ) vp0000100111011 := join_branches bp00001001110110 bp00001001110111
private noncomputable def vp00001001110101_0 : Blocks := edgeBlocks% "full/vectors/00001001110101-V-0000.bin"
noncomputable def vp00001001110101 : Blocks := vp00001001110101_0
theorem coverp00001001110101 : Covers (-314261639/500000 : ℚ) vp00001001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001110100_0 : Blocks := edgeBlocks% "full/vectors/00001001110100-V-0000.bin"
noncomputable def vp00001001110100 : Blocks := vp00001001110100_0
theorem coverp00001001110100 : Covers (-313761639/500000 : ℚ) vp00001001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111010_0 : Blocks := edgeBlocks% "full/vectors/0000100111010-V-0000.bin"
noncomputable def vp0000100111010 : Blocks := vp0000100111010_0
private theorem bp00001001110100 : Branch 0 (-313761639/1000000 : ℚ) vp0000100111010 := by
  apply branch_left_normalized (c:=vp00001001110100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-313761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-313761639/500000 : ℚ) by norm_num]
  exact coverp00001001110100
private noncomputable def ep00001001110101_0 : Blocks := edgeBlocks% "full/vectors/00001001110101-E-0000.bin"
noncomputable def ep00001001110101 : Blocks := ep00001001110101_0
private theorem idp00001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111010.list =
    C ((2:ℤ)^74) * horner X vp00001001110101.list + horner X ep00001001110101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001110101 : Branch 1 (-313761639/1000000 : ℚ) vp0000100111010 := by
  apply branch_checked idp00001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-313761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-314261639/500000 : ℚ) by norm_num]
  exact coverp00001001110101
theorem coverp0000100111010 : Covers (-313761639/1000000 : ℚ) vp0000100111010 := join_branches bp00001001110100 bp00001001110101
private noncomputable def vp000010011101_0 : Blocks := edgeBlocks% "full/vectors/000010011101-V-0000.bin"
noncomputable def vp000010011101 : Blocks := vp000010011101_0
private theorem bp0000100111010 : Branch 0 (-313761639/2000000 : ℚ) vp000010011101 := by
  apply branch_left_normalized (c:=vp0000100111010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-313761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-313761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111010
private noncomputable def ep0000100111011_0 : Blocks := edgeBlocks% "full/vectors/0000100111011-E-0000.bin"
noncomputable def ep0000100111011 : Blocks := ep0000100111011_0
private theorem idp0000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011101.list =
    C ((2:ℤ)^133) * horner X vp0000100111011.list + horner X ep0000100111011.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100111011 : Branch 1 (-313761639/2000000 : ℚ) vp000010011101 := by
  apply branch_checked idp0000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-313761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-314761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111011
theorem coverp000010011101 : Covers (-313761639/2000000 : ℚ) vp000010011101 := join_branches bp0000100111010 bp0000100111011
private noncomputable def vp00001001110011_0 : Blocks := edgeBlocks% "full/vectors/00001001110011-V-0000.bin"
noncomputable def vp00001001110011 : Blocks := vp00001001110011_0
theorem coverp00001001110011 : Covers (-313261639/500000 : ℚ) vp00001001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001110010_0 : Blocks := edgeBlocks% "full/vectors/00001001110010-V-0000.bin"
noncomputable def vp00001001110010 : Blocks := vp00001001110010_0
theorem coverp00001001110010 : Covers (-312761639/500000 : ℚ) vp00001001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111001_0 : Blocks := edgeBlocks% "full/vectors/0000100111001-V-0000.bin"
noncomputable def vp0000100111001 : Blocks := vp0000100111001_0
private theorem bp00001001110010 : Branch 0 (-312761639/1000000 : ℚ) vp0000100111001 := by
  apply branch_left_normalized (c:=vp00001001110010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-312761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-312761639/500000 : ℚ) by norm_num]
  exact coverp00001001110010
private noncomputable def ep00001001110011_0 : Blocks := edgeBlocks% "full/vectors/00001001110011-E-0000.bin"
noncomputable def ep00001001110011 : Blocks := ep00001001110011_0
private theorem idp00001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111001.list =
    C ((2:ℤ)^73) * horner X vp00001001110011.list + horner X ep00001001110011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001110011 : Branch 1 (-312761639/1000000 : ℚ) vp0000100111001 := by
  apply branch_checked idp00001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-312761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-313261639/500000 : ℚ) by norm_num]
  exact coverp00001001110011
theorem coverp0000100111001 : Covers (-312761639/1000000 : ℚ) vp0000100111001 := join_branches bp00001001110010 bp00001001110011
private noncomputable def vp00001001110001_0 : Blocks := edgeBlocks% "full/vectors/00001001110001-V-0000.bin"
noncomputable def vp00001001110001 : Blocks := vp00001001110001_0
theorem coverp00001001110001 : Covers (-312261639/500000 : ℚ) vp00001001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001110000_0 : Blocks := edgeBlocks% "full/vectors/00001001110000-V-0000.bin"
noncomputable def vp00001001110000 : Blocks := vp00001001110000_0
theorem coverp00001001110000 : Covers (-311761639/500000 : ℚ) vp00001001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100111000_0 : Blocks := edgeBlocks% "full/vectors/0000100111000-V-0000.bin"
noncomputable def vp0000100111000 : Blocks := vp0000100111000_0
private theorem bp00001001110000 : Branch 0 (-311761639/1000000 : ℚ) vp0000100111000 := by
  apply branch_left_normalized (c:=vp00001001110000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-311761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-311761639/500000 : ℚ) by norm_num]
  exact coverp00001001110000
private noncomputable def ep00001001110001_0 : Blocks := edgeBlocks% "full/vectors/00001001110001-E-0000.bin"
noncomputable def ep00001001110001 : Blocks := ep00001001110001_0
private theorem idp00001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111000.list =
    C ((2:ℤ)^73) * horner X vp00001001110001.list + horner X ep00001001110001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001110001 : Branch 1 (-311761639/1000000 : ℚ) vp0000100111000 := by
  apply branch_checked idp00001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-311761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-312261639/500000 : ℚ) by norm_num]
  exact coverp00001001110001
theorem coverp0000100111000 : Covers (-311761639/1000000 : ℚ) vp0000100111000 := join_branches bp00001001110000 bp00001001110001
private noncomputable def vp000010011100_0 : Blocks := edgeBlocks% "full/vectors/000010011100-V-0000.bin"
noncomputable def vp000010011100 : Blocks := vp000010011100_0
private theorem bp0000100111000 : Branch 0 (-311761639/2000000 : ℚ) vp000010011100 := by
  apply branch_left_normalized (c:=vp0000100111000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-311761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-311761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111000
private noncomputable def ep0000100111001_0 : Blocks := edgeBlocks% "full/vectors/0000100111001-E-0000.bin"
noncomputable def ep0000100111001 : Blocks := ep0000100111001_0
private theorem idp0000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011100.list =
    C ((2:ℤ)^133) * horner X vp0000100111001.list + horner X ep0000100111001.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100111001 : Branch 1 (-311761639/2000000 : ℚ) vp000010011100 := by
  apply branch_checked idp0000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-311761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-312761639/1000000 : ℚ) by norm_num]
  exact coverp0000100111001
theorem coverp000010011100 : Covers (-311761639/2000000 : ℚ) vp000010011100 := join_branches bp0000100111000 bp0000100111001
private noncomputable def vp00001001110_0 : Blocks := edgeBlocks% "full/vectors/00001001110-V-0000.bin"
private noncomputable def vp00001001110_1 : Blocks := edgeBlocks% "full/vectors/00001001110-V-0001.bin"
noncomputable def vp00001001110 : Blocks := (Blocks.join vp00001001110_0 vp00001001110_1)
private theorem bp000010011100 : Branch 0 (-311761639/4000000 : ℚ) vp00001001110 := by
  apply branch_left_normalized (c:=vp000010011100) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-311761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-311761639/2000000 : ℚ) by norm_num]
  exact coverp000010011100
private noncomputable def ep000010011101_0 : Blocks := edgeBlocks% "full/vectors/000010011101-E-0000.bin"
private noncomputable def ep000010011101_1 : Blocks := edgeBlocks% "full/vectors/000010011101-E-0001.bin"
noncomputable def ep000010011101 : Blocks := (Blocks.join ep000010011101_0 ep000010011101_1)
private theorem idp000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001110.list =
    C ((2:ℤ)^249) * horner X vp000010011101.list + horner X ep000010011101.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010011101 : Branch 1 (-311761639/4000000 : ℚ) vp00001001110 := by
  apply branch_checked idp000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-311761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-313761639/2000000 : ℚ) by norm_num]
  exact coverp000010011101
theorem coverp00001001110 : Covers (-311761639/4000000 : ℚ) vp00001001110 := join_branches bp000010011100 bp000010011101
private noncomputable def vp0000100111_0 : Blocks := edgeBlocks% "full/vectors/0000100111-V-0000.bin"
private noncomputable def vp0000100111_1 : Blocks := edgeBlocks% "full/vectors/0000100111-V-0001.bin"
private noncomputable def vp0000100111_2 : Blocks := edgeBlocks% "full/vectors/0000100111-V-0002.bin"
private noncomputable def vp0000100111_3 : Blocks := edgeBlocks% "full/vectors/0000100111-V-0003.bin"
noncomputable def vp0000100111 : Blocks := (Blocks.join (Blocks.join vp0000100111_0 vp0000100111_1) (Blocks.join vp0000100111_2 vp0000100111_3))
private theorem bp00001001110 : Branch 0 (-311761639/8000000 : ℚ) vp0000100111 := by
  apply branch_left_normalized (c:=vp00001001110) (k:=0) (m:=237) (by decide +kernel)
  rw [show 2*(-311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-311761639/4000000 : ℚ) by norm_num]
  exact coverp00001001110
private noncomputable def ep00001001111_0 : Blocks := edgeBlocks% "full/vectors/00001001111-E-0000.bin"
private noncomputable def ep00001001111_1 : Blocks := edgeBlocks% "full/vectors/00001001111-E-0001.bin"
private noncomputable def ep00001001111_2 : Blocks := edgeBlocks% "full/vectors/00001001111-E-0002.bin"
private noncomputable def ep00001001111_3 : Blocks := edgeBlocks% "full/vectors/00001001111-E-0003.bin"
noncomputable def ep00001001111 : Blocks := (Blocks.join (Blocks.join ep00001001111_0 ep00001001111_1) (Blocks.join ep00001001111_2 ep00001001111_3))
private theorem idp00001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100111.list =
    C ((2:ℤ)^480) * horner X vp00001001111.list + horner X ep00001001111.list := by
  exact edge_identity (B := (2:ℤ)^784) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001111 : Branch 1 (-311761639/8000000 : ℚ) vp0000100111 := by
  apply branch_checked idp00001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-315761639/4000000 : ℚ) by norm_num]
  exact coverp00001001111
theorem coverp0000100111 : Covers (-311761639/8000000 : ℚ) vp0000100111 := join_branches bp00001001110 bp00001001111
private noncomputable def vp00001001101111_0 : Blocks := edgeBlocks% "full/vectors/00001001101111-V-0000.bin"
noncomputable def vp00001001101111 : Blocks := vp00001001101111_0
theorem coverp00001001101111 : Covers (-311261639/500000 : ℚ) vp00001001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001101110_0 : Blocks := edgeBlocks% "full/vectors/00001001101110-V-0000.bin"
noncomputable def vp00001001101110 : Blocks := vp00001001101110_0
theorem coverp00001001101110 : Covers (-310761639/500000 : ℚ) vp00001001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000100110111-V-0000.bin"
noncomputable def vp0000100110111 : Blocks := vp0000100110111_0
private theorem bp00001001101110 : Branch 0 (-310761639/1000000 : ℚ) vp0000100110111 := by
  apply branch_left_normalized (c:=vp00001001101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-310761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-310761639/500000 : ℚ) by norm_num]
  exact coverp00001001101110
private noncomputable def ep00001001101111_0 : Blocks := edgeBlocks% "full/vectors/00001001101111-E-0000.bin"
noncomputable def ep00001001101111 : Blocks := ep00001001101111_0
private theorem idp00001001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110111.list =
    C ((2:ℤ)^74) * horner X vp00001001101111.list + horner X ep00001001101111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001101111 : Branch 1 (-310761639/1000000 : ℚ) vp0000100110111 := by
  apply branch_checked idp00001001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-310761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-311261639/500000 : ℚ) by norm_num]
  exact coverp00001001101111
theorem coverp0000100110111 : Covers (-310761639/1000000 : ℚ) vp0000100110111 := join_branches bp00001001101110 bp00001001101111
private noncomputable def vp00001001101101_0 : Blocks := edgeBlocks% "full/vectors/00001001101101-V-0000.bin"
noncomputable def vp00001001101101 : Blocks := vp00001001101101_0
theorem coverp00001001101101 : Covers (-310261639/500000 : ℚ) vp00001001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001101100_0 : Blocks := edgeBlocks% "full/vectors/00001001101100-V-0000.bin"
noncomputable def vp00001001101100 : Blocks := vp00001001101100_0
theorem coverp00001001101100 : Covers (-309761639/500000 : ℚ) vp00001001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110110_0 : Blocks := edgeBlocks% "full/vectors/0000100110110-V-0000.bin"
noncomputable def vp0000100110110 : Blocks := vp0000100110110_0
private theorem bp00001001101100 : Branch 0 (-309761639/1000000 : ℚ) vp0000100110110 := by
  apply branch_left_normalized (c:=vp00001001101100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-309761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-309761639/500000 : ℚ) by norm_num]
  exact coverp00001001101100
private noncomputable def ep00001001101101_0 : Blocks := edgeBlocks% "full/vectors/00001001101101-E-0000.bin"
noncomputable def ep00001001101101 : Blocks := ep00001001101101_0
private theorem idp00001001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110110.list =
    C ((2:ℤ)^74) * horner X vp00001001101101.list + horner X ep00001001101101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001101101 : Branch 1 (-309761639/1000000 : ℚ) vp0000100110110 := by
  apply branch_checked idp00001001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-309761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-310261639/500000 : ℚ) by norm_num]
  exact coverp00001001101101
theorem coverp0000100110110 : Covers (-309761639/1000000 : ℚ) vp0000100110110 := join_branches bp00001001101100 bp00001001101101
private noncomputable def vp000010011011_0 : Blocks := edgeBlocks% "full/vectors/000010011011-V-0000.bin"
noncomputable def vp000010011011 : Blocks := vp000010011011_0
private theorem bp0000100110110 : Branch 0 (-309761639/2000000 : ℚ) vp000010011011 := by
  apply branch_left_normalized (c:=vp0000100110110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-309761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-309761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110110
private noncomputable def ep0000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000100110111-E-0000.bin"
noncomputable def ep0000100110111 : Blocks := ep0000100110111_0
private theorem idp0000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011011.list =
    C ((2:ℤ)^134) * horner X vp0000100110111.list + horner X ep0000100110111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100110111 : Branch 1 (-309761639/2000000 : ℚ) vp000010011011 := by
  apply branch_checked idp0000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-309761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-310761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110111
theorem coverp000010011011 : Covers (-309761639/2000000 : ℚ) vp000010011011 := join_branches bp0000100110110 bp0000100110111
private noncomputable def vp00001001101011_0 : Blocks := edgeBlocks% "full/vectors/00001001101011-V-0000.bin"
noncomputable def vp00001001101011 : Blocks := vp00001001101011_0
theorem coverp00001001101011 : Covers (-309261639/500000 : ℚ) vp00001001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001101010_0 : Blocks := edgeBlocks% "full/vectors/00001001101010-V-0000.bin"
noncomputable def vp00001001101010 : Blocks := vp00001001101010_0
theorem coverp00001001101010 : Covers (-308761639/500000 : ℚ) vp00001001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110101_0 : Blocks := edgeBlocks% "full/vectors/0000100110101-V-0000.bin"
noncomputable def vp0000100110101 : Blocks := vp0000100110101_0
private theorem bp00001001101010 : Branch 0 (-308761639/1000000 : ℚ) vp0000100110101 := by
  apply branch_left_normalized (c:=vp00001001101010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-308761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-308761639/500000 : ℚ) by norm_num]
  exact coverp00001001101010
private noncomputable def ep00001001101011_0 : Blocks := edgeBlocks% "full/vectors/00001001101011-E-0000.bin"
noncomputable def ep00001001101011 : Blocks := ep00001001101011_0
private theorem idp00001001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110101.list =
    C ((2:ℤ)^74) * horner X vp00001001101011.list + horner X ep00001001101011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001101011 : Branch 1 (-308761639/1000000 : ℚ) vp0000100110101 := by
  apply branch_checked idp00001001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-308761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-309261639/500000 : ℚ) by norm_num]
  exact coverp00001001101011
theorem coverp0000100110101 : Covers (-308761639/1000000 : ℚ) vp0000100110101 := join_branches bp00001001101010 bp00001001101011
private noncomputable def vp00001001101001_0 : Blocks := edgeBlocks% "full/vectors/00001001101001-V-0000.bin"
noncomputable def vp00001001101001 : Blocks := vp00001001101001_0
theorem coverp00001001101001 : Covers (-308261639/500000 : ℚ) vp00001001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001101000_0 : Blocks := edgeBlocks% "full/vectors/00001001101000-V-0000.bin"
noncomputable def vp00001001101000 : Blocks := vp00001001101000_0
theorem coverp00001001101000 : Covers (-307761639/500000 : ℚ) vp00001001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110100_0 : Blocks := edgeBlocks% "full/vectors/0000100110100-V-0000.bin"
noncomputable def vp0000100110100 : Blocks := vp0000100110100_0
private theorem bp00001001101000 : Branch 0 (-307761639/1000000 : ℚ) vp0000100110100 := by
  apply branch_left_normalized (c:=vp00001001101000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-307761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-307761639/500000 : ℚ) by norm_num]
  exact coverp00001001101000
private noncomputable def ep00001001101001_0 : Blocks := edgeBlocks% "full/vectors/00001001101001-E-0000.bin"
noncomputable def ep00001001101001 : Blocks := ep00001001101001_0
private theorem idp00001001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110100.list =
    C ((2:ℤ)^75) * horner X vp00001001101001.list + horner X ep00001001101001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001101001 : Branch 1 (-307761639/1000000 : ℚ) vp0000100110100 := by
  apply branch_checked idp00001001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-307761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-308261639/500000 : ℚ) by norm_num]
  exact coverp00001001101001
theorem coverp0000100110100 : Covers (-307761639/1000000 : ℚ) vp0000100110100 := join_branches bp00001001101000 bp00001001101001
private noncomputable def vp000010011010_0 : Blocks := edgeBlocks% "full/vectors/000010011010-V-0000.bin"
noncomputable def vp000010011010 : Blocks := vp000010011010_0
private theorem bp0000100110100 : Branch 0 (-307761639/2000000 : ℚ) vp000010011010 := by
  apply branch_left_normalized (c:=vp0000100110100) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-307761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-307761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110100
private noncomputable def ep0000100110101_0 : Blocks := edgeBlocks% "full/vectors/0000100110101-E-0000.bin"
noncomputable def ep0000100110101 : Blocks := ep0000100110101_0
private theorem idp0000100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011010.list =
    C ((2:ℤ)^134) * horner X vp0000100110101.list + horner X ep0000100110101.list := by
  exact edge_identity (B := (2:ℤ)^278) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100110101 : Branch 1 (-307761639/2000000 : ℚ) vp000010011010 := by
  apply branch_checked idp0000100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-307761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-308761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110101
theorem coverp000010011010 : Covers (-307761639/2000000 : ℚ) vp000010011010 := join_branches bp0000100110100 bp0000100110101
private noncomputable def vp00001001101_0 : Blocks := edgeBlocks% "full/vectors/00001001101-V-0000.bin"
private noncomputable def vp00001001101_1 : Blocks := edgeBlocks% "full/vectors/00001001101-V-0001.bin"
noncomputable def vp00001001101 : Blocks := (Blocks.join vp00001001101_0 vp00001001101_1)
private theorem bp000010011010 : Branch 0 (-307761639/4000000 : ℚ) vp00001001101 := by
  apply branch_left_normalized (c:=vp000010011010) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-307761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-307761639/2000000 : ℚ) by norm_num]
  exact coverp000010011010
private noncomputable def ep000010011011_0 : Blocks := edgeBlocks% "full/vectors/000010011011-E-0000.bin"
private noncomputable def ep000010011011_1 : Blocks := edgeBlocks% "full/vectors/000010011011-E-0001.bin"
noncomputable def ep000010011011 : Blocks := (Blocks.join ep000010011011_0 ep000010011011_1)
private theorem idp000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001101.list =
    C ((2:ℤ)^252) * horner X vp000010011011.list + horner X ep000010011011.list := by
  exact edge_identity (B := (2:ℤ)^449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010011011 : Branch 1 (-307761639/4000000 : ℚ) vp00001001101 := by
  apply branch_checked idp000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-307761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-309761639/2000000 : ℚ) by norm_num]
  exact coverp000010011011
theorem coverp00001001101 : Covers (-307761639/4000000 : ℚ) vp00001001101 := join_branches bp000010011010 bp000010011011
private noncomputable def vp00001001100111_0 : Blocks := edgeBlocks% "full/vectors/00001001100111-V-0000.bin"
noncomputable def vp00001001100111 : Blocks := vp00001001100111_0
theorem coverp00001001100111 : Covers (-307261639/500000 : ℚ) vp00001001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001100110_0 : Blocks := edgeBlocks% "full/vectors/00001001100110-V-0000.bin"
noncomputable def vp00001001100110 : Blocks := vp00001001100110_0
theorem coverp00001001100110 : Covers (-306761639/500000 : ℚ) vp00001001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110011_0 : Blocks := edgeBlocks% "full/vectors/0000100110011-V-0000.bin"
noncomputable def vp0000100110011 : Blocks := vp0000100110011_0
private theorem bp00001001100110 : Branch 0 (-306761639/1000000 : ℚ) vp0000100110011 := by
  apply branch_left_normalized (c:=vp00001001100110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-306761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-306761639/500000 : ℚ) by norm_num]
  exact coverp00001001100110
private noncomputable def ep00001001100111_0 : Blocks := edgeBlocks% "full/vectors/00001001100111-E-0000.bin"
noncomputable def ep00001001100111 : Blocks := ep00001001100111_0
private theorem idp00001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110011.list =
    C ((2:ℤ)^76) * horner X vp00001001100111.list + horner X ep00001001100111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001100111 : Branch 1 (-306761639/1000000 : ℚ) vp0000100110011 := by
  apply branch_checked idp00001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-306761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-307261639/500000 : ℚ) by norm_num]
  exact coverp00001001100111
theorem coverp0000100110011 : Covers (-306761639/1000000 : ℚ) vp0000100110011 := join_branches bp00001001100110 bp00001001100111
private noncomputable def vp00001001100101_0 : Blocks := edgeBlocks% "full/vectors/00001001100101-V-0000.bin"
noncomputable def vp00001001100101 : Blocks := vp00001001100101_0
theorem coverp00001001100101 : Covers (-306261639/500000 : ℚ) vp00001001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001100100_0 : Blocks := edgeBlocks% "full/vectors/00001001100100-V-0000.bin"
noncomputable def vp00001001100100 : Blocks := vp00001001100100_0
theorem coverp00001001100100 : Covers (-305761639/500000 : ℚ) vp00001001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110010_0 : Blocks := edgeBlocks% "full/vectors/0000100110010-V-0000.bin"
noncomputable def vp0000100110010 : Blocks := vp0000100110010_0
private theorem bp00001001100100 : Branch 0 (-305761639/1000000 : ℚ) vp0000100110010 := by
  apply branch_left_normalized (c:=vp00001001100100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-305761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-305761639/500000 : ℚ) by norm_num]
  exact coverp00001001100100
private noncomputable def ep00001001100101_0 : Blocks := edgeBlocks% "full/vectors/00001001100101-E-0000.bin"
noncomputable def ep00001001100101 : Blocks := ep00001001100101_0
private theorem idp00001001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110010.list =
    C ((2:ℤ)^76) * horner X vp00001001100101.list + horner X ep00001001100101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001100101 : Branch 1 (-305761639/1000000 : ℚ) vp0000100110010 := by
  apply branch_checked idp00001001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-305761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-306261639/500000 : ℚ) by norm_num]
  exact coverp00001001100101
theorem coverp0000100110010 : Covers (-305761639/1000000 : ℚ) vp0000100110010 := join_branches bp00001001100100 bp00001001100101
private noncomputable def vp000010011001_0 : Blocks := edgeBlocks% "full/vectors/000010011001-V-0000.bin"
private noncomputable def vp000010011001_1 : Blocks := edgeBlocks% "full/vectors/000010011001-V-0001.bin"
noncomputable def vp000010011001 : Blocks := (Blocks.join vp000010011001_0 vp000010011001_1)
private theorem bp0000100110010 : Branch 0 (-305761639/2000000 : ℚ) vp000010011001 := by
  apply branch_left_normalized (c:=vp0000100110010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-305761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-305761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110010
private noncomputable def ep0000100110011_0 : Blocks := edgeBlocks% "full/vectors/0000100110011-E-0000.bin"
private noncomputable def ep0000100110011_1 : Blocks := edgeBlocks% "full/vectors/0000100110011-E-0001.bin"
noncomputable def ep0000100110011 : Blocks := (Blocks.join ep0000100110011_0 ep0000100110011_1)
private theorem idp0000100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011001.list =
    C ((2:ℤ)^136) * horner X vp0000100110011.list + horner X ep0000100110011.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100110011 : Branch 1 (-305761639/2000000 : ℚ) vp000010011001 := by
  apply branch_checked idp0000100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-305761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-306761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110011
theorem coverp000010011001 : Covers (-305761639/2000000 : ℚ) vp000010011001 := join_branches bp0000100110010 bp0000100110011
private noncomputable def vp00001001100011_0 : Blocks := edgeBlocks% "full/vectors/00001001100011-V-0000.bin"
noncomputable def vp00001001100011 : Blocks := vp00001001100011_0
theorem coverp00001001100011 : Covers (-305261639/500000 : ℚ) vp00001001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001100010_0 : Blocks := edgeBlocks% "full/vectors/00001001100010-V-0000.bin"
noncomputable def vp00001001100010 : Blocks := vp00001001100010_0
theorem coverp00001001100010 : Covers (-304761639/500000 : ℚ) vp00001001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110001_0 : Blocks := edgeBlocks% "full/vectors/0000100110001-V-0000.bin"
noncomputable def vp0000100110001 : Blocks := vp0000100110001_0
private theorem bp00001001100010 : Branch 0 (-304761639/1000000 : ℚ) vp0000100110001 := by
  apply branch_left_normalized (c:=vp00001001100010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-304761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-304761639/500000 : ℚ) by norm_num]
  exact coverp00001001100010
private noncomputable def ep00001001100011_0 : Blocks := edgeBlocks% "full/vectors/00001001100011-E-0000.bin"
noncomputable def ep00001001100011 : Blocks := ep00001001100011_0
private theorem idp00001001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110001.list =
    C ((2:ℤ)^77) * horner X vp00001001100011.list + horner X ep00001001100011.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001100011 : Branch 1 (-304761639/1000000 : ℚ) vp0000100110001 := by
  apply branch_checked idp00001001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-304761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-305261639/500000 : ℚ) by norm_num]
  exact coverp00001001100011
theorem coverp0000100110001 : Covers (-304761639/1000000 : ℚ) vp0000100110001 := join_branches bp00001001100010 bp00001001100011
private noncomputable def vp00001001100001_0 : Blocks := edgeBlocks% "full/vectors/00001001100001-V-0000.bin"
noncomputable def vp00001001100001 : Blocks := vp00001001100001_0
theorem coverp00001001100001 : Covers (-304261639/500000 : ℚ) vp00001001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001100000_0 : Blocks := edgeBlocks% "full/vectors/00001001100000-V-0000.bin"
noncomputable def vp00001001100000 : Blocks := vp00001001100000_0
theorem coverp00001001100000 : Covers (-303761639/500000 : ℚ) vp00001001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100110000_0 : Blocks := edgeBlocks% "full/vectors/0000100110000-V-0000.bin"
noncomputable def vp0000100110000 : Blocks := vp0000100110000_0
private theorem bp00001001100000 : Branch 0 (-303761639/1000000 : ℚ) vp0000100110000 := by
  apply branch_left_normalized (c:=vp00001001100000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-303761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-303761639/500000 : ℚ) by norm_num]
  exact coverp00001001100000
private noncomputable def ep00001001100001_0 : Blocks := edgeBlocks% "full/vectors/00001001100001-E-0000.bin"
noncomputable def ep00001001100001 : Blocks := ep00001001100001_0
private theorem idp00001001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110000.list =
    C ((2:ℤ)^78) * horner X vp00001001100001.list + horner X ep00001001100001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001100001 : Branch 1 (-303761639/1000000 : ℚ) vp0000100110000 := by
  apply branch_checked idp00001001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-303761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-304261639/500000 : ℚ) by norm_num]
  exact coverp00001001100001
theorem coverp0000100110000 : Covers (-303761639/1000000 : ℚ) vp0000100110000 := join_branches bp00001001100000 bp00001001100001
private noncomputable def vp000010011000_0 : Blocks := edgeBlocks% "full/vectors/000010011000-V-0000.bin"
private noncomputable def vp000010011000_1 : Blocks := edgeBlocks% "full/vectors/000010011000-V-0001.bin"
noncomputable def vp000010011000 : Blocks := (Blocks.join vp000010011000_0 vp000010011000_1)
private theorem bp0000100110000 : Branch 0 (-303761639/2000000 : ℚ) vp000010011000 := by
  apply branch_left_normalized (c:=vp0000100110000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-303761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-303761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110000
private noncomputable def ep0000100110001_0 : Blocks := edgeBlocks% "full/vectors/0000100110001-E-0000.bin"
private noncomputable def ep0000100110001_1 : Blocks := edgeBlocks% "full/vectors/0000100110001-E-0001.bin"
noncomputable def ep0000100110001 : Blocks := (Blocks.join ep0000100110001_0 ep0000100110001_1)
private theorem idp0000100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011000.list =
    C ((2:ℤ)^138) * horner X vp0000100110001.list + horner X ep0000100110001.list := by
  exact edge_identity (B := (2:ℤ)^285) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100110001 : Branch 1 (-303761639/2000000 : ℚ) vp000010011000 := by
  apply branch_checked idp0000100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-303761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-304761639/1000000 : ℚ) by norm_num]
  exact coverp0000100110001
theorem coverp000010011000 : Covers (-303761639/2000000 : ℚ) vp000010011000 := join_branches bp0000100110000 bp0000100110001
private noncomputable def vp00001001100_0 : Blocks := edgeBlocks% "full/vectors/00001001100-V-0000.bin"
private noncomputable def vp00001001100_1 : Blocks := edgeBlocks% "full/vectors/00001001100-V-0001.bin"
noncomputable def vp00001001100 : Blocks := (Blocks.join vp00001001100_0 vp00001001100_1)
private theorem bp000010011000 : Branch 0 (-303761639/4000000 : ℚ) vp00001001100 := by
  apply branch_left_normalized (c:=vp000010011000) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-303761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-303761639/2000000 : ℚ) by norm_num]
  exact coverp000010011000
private noncomputable def ep000010011001_0 : Blocks := edgeBlocks% "full/vectors/000010011001-E-0000.bin"
private noncomputable def ep000010011001_1 : Blocks := edgeBlocks% "full/vectors/000010011001-E-0001.bin"
noncomputable def ep000010011001 : Blocks := (Blocks.join ep000010011001_0 ep000010011001_1)
private theorem idp000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001100.list =
    C ((2:ℤ)^257) * horner X vp000010011001.list + horner X ep000010011001.list := by
  exact edge_identity (B := (2:ℤ)^457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010011001 : Branch 1 (-303761639/4000000 : ℚ) vp00001001100 := by
  apply branch_checked idp000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-303761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-305761639/2000000 : ℚ) by norm_num]
  exact coverp000010011001
theorem coverp00001001100 : Covers (-303761639/4000000 : ℚ) vp00001001100 := join_branches bp000010011000 bp000010011001
private noncomputable def vp0000100110_0 : Blocks := edgeBlocks% "full/vectors/0000100110-V-0000.bin"
private noncomputable def vp0000100110_1 : Blocks := edgeBlocks% "full/vectors/0000100110-V-0001.bin"
private noncomputable def vp0000100110_2 : Blocks := edgeBlocks% "full/vectors/0000100110-V-0002.bin"
private noncomputable def vp0000100110_3 : Blocks := edgeBlocks% "full/vectors/0000100110-V-0003.bin"
noncomputable def vp0000100110 : Blocks := (Blocks.join (Blocks.join vp0000100110_0 vp0000100110_1) (Blocks.join vp0000100110_2 vp0000100110_3))
private theorem bp00001001100 : Branch 0 (-303761639/8000000 : ℚ) vp0000100110 := by
  apply branch_left_normalized (c:=vp00001001100) (k:=0) (m:=242) (by decide +kernel)
  rw [show 2*(-303761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-303761639/4000000 : ℚ) by norm_num]
  exact coverp00001001100
private noncomputable def ep00001001101_0 : Blocks := edgeBlocks% "full/vectors/00001001101-E-0000.bin"
private noncomputable def ep00001001101_1 : Blocks := edgeBlocks% "full/vectors/00001001101-E-0001.bin"
private noncomputable def ep00001001101_2 : Blocks := edgeBlocks% "full/vectors/00001001101-E-0002.bin"
private noncomputable def ep00001001101_3 : Blocks := edgeBlocks% "full/vectors/00001001101-E-0003.bin"
noncomputable def ep00001001101 : Blocks := (Blocks.join (Blocks.join ep00001001101_0 ep00001001101_1) (Blocks.join ep00001001101_2 ep00001001101_3))
private theorem idp00001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100110.list =
    C ((2:ℤ)^494) * horner X vp00001001101.list + horner X ep00001001101.list := by
  exact edge_identity (B := (2:ℤ)^801) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001101 : Branch 1 (-303761639/8000000 : ℚ) vp0000100110 := by
  apply branch_checked idp00001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-303761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-307761639/4000000 : ℚ) by norm_num]
  exact coverp00001001101
theorem coverp0000100110 : Covers (-303761639/8000000 : ℚ) vp0000100110 := join_branches bp00001001100 bp00001001101
private noncomputable def vp000010011_0 : Blocks := edgeBlocks% "full/vectors/000010011-V-0000.bin"
private noncomputable def vp000010011_1 : Blocks := edgeBlocks% "full/vectors/000010011-V-0001.bin"
private noncomputable def vp000010011_2 : Blocks := edgeBlocks% "full/vectors/000010011-V-0002.bin"
private noncomputable def vp000010011_3 : Blocks := edgeBlocks% "full/vectors/000010011-V-0003.bin"
private noncomputable def vp000010011_4 : Blocks := edgeBlocks% "full/vectors/000010011-V-0004.bin"
private noncomputable def vp000010011_5 : Blocks := edgeBlocks% "full/vectors/000010011-V-0005.bin"
private noncomputable def vp000010011_6 : Blocks := edgeBlocks% "full/vectors/000010011-V-0006.bin"
private noncomputable def vp000010011_7 : Blocks := edgeBlocks% "full/vectors/000010011-V-0007.bin"
noncomputable def vp000010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000010011_0 vp000010011_1) (Blocks.join vp000010011_2 vp000010011_3)) (Blocks.join (Blocks.join vp000010011_4 vp000010011_5) (Blocks.join vp000010011_6 vp000010011_7)))
private theorem bp0000100110 : Branch 0 (-303761639/16000000 : ℚ) vp000010011 := by
  apply branch_left_normalized (c:=vp0000100110) (k:=0) (m:=466) (by decide +kernel)
  rw [show 2*(-303761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-303761639/8000000 : ℚ) by norm_num]
  exact coverp0000100110
private noncomputable def ep0000100111_0 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0000.bin"
private noncomputable def ep0000100111_1 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0001.bin"
private noncomputable def ep0000100111_2 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0002.bin"
private noncomputable def ep0000100111_3 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0003.bin"
private noncomputable def ep0000100111_4 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0004.bin"
private noncomputable def ep0000100111_5 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0005.bin"
private noncomputable def ep0000100111_6 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0006.bin"
private noncomputable def ep0000100111_7 : Blocks := edgeBlocks% "full/vectors/0000100111-E-0007.bin"
noncomputable def ep0000100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000100111_0 ep0000100111_1) (Blocks.join ep0000100111_2 ep0000100111_3)) (Blocks.join (Blocks.join ep0000100111_4 ep0000100111_5) (Blocks.join ep0000100111_6 ep0000100111_7)))
private theorem idp0000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010011.list =
    C ((2:ℤ)^960) * horner X vp0000100111.list + horner X ep0000100111.list := by
  exact edge_identity (B := (2:ℤ)^1480) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100111 : Branch 1 (-303761639/16000000 : ℚ) vp000010011 := by
  apply branch_checked idp0000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-303761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-311761639/8000000 : ℚ) by norm_num]
  exact coverp0000100111
theorem coverp000010011 : Covers (-303761639/16000000 : ℚ) vp000010011 := join_branches bp0000100110 bp0000100111
private noncomputable def vp00001001011111_0 : Blocks := edgeBlocks% "full/vectors/00001001011111-V-0000.bin"
noncomputable def vp00001001011111 : Blocks := vp00001001011111_0
theorem coverp00001001011111 : Covers (-303261639/500000 : ℚ) vp00001001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001011110_0 : Blocks := edgeBlocks% "full/vectors/00001001011110-V-0000.bin"
noncomputable def vp00001001011110 : Blocks := vp00001001011110_0
theorem coverp00001001011110 : Covers (-302761639/500000 : ℚ) vp00001001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000100101111-V-0000.bin"
noncomputable def vp0000100101111 : Blocks := vp0000100101111_0
private theorem bp00001001011110 : Branch 0 (-302761639/1000000 : ℚ) vp0000100101111 := by
  apply branch_left_normalized (c:=vp00001001011110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-302761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-302761639/500000 : ℚ) by norm_num]
  exact coverp00001001011110
private noncomputable def ep00001001011111_0 : Blocks := edgeBlocks% "full/vectors/00001001011111-E-0000.bin"
noncomputable def ep00001001011111 : Blocks := ep00001001011111_0
private theorem idp00001001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101111.list =
    C ((2:ℤ)^79) * horner X vp00001001011111.list + horner X ep00001001011111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001011111 : Branch 1 (-302761639/1000000 : ℚ) vp0000100101111 := by
  apply branch_checked idp00001001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-302761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-303261639/500000 : ℚ) by norm_num]
  exact coverp00001001011111
theorem coverp0000100101111 : Covers (-302761639/1000000 : ℚ) vp0000100101111 := join_branches bp00001001011110 bp00001001011111
private noncomputable def vp00001001011101_0 : Blocks := edgeBlocks% "full/vectors/00001001011101-V-0000.bin"
noncomputable def vp00001001011101 : Blocks := vp00001001011101_0
theorem coverp00001001011101 : Covers (-302261639/500000 : ℚ) vp00001001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001011100_0 : Blocks := edgeBlocks% "full/vectors/00001001011100-V-0000.bin"
noncomputable def vp00001001011100 : Blocks := vp00001001011100_0
theorem coverp00001001011100 : Covers (-301761639/500000 : ℚ) vp00001001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100101110_0 : Blocks := edgeBlocks% "full/vectors/0000100101110-V-0000.bin"
noncomputable def vp0000100101110 : Blocks := vp0000100101110_0
private theorem bp00001001011100 : Branch 0 (-301761639/1000000 : ℚ) vp0000100101110 := by
  apply branch_left_normalized (c:=vp00001001011100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-301761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-301761639/500000 : ℚ) by norm_num]
  exact coverp00001001011100
private noncomputable def ep00001001011101_0 : Blocks := edgeBlocks% "full/vectors/00001001011101-E-0000.bin"
noncomputable def ep00001001011101 : Blocks := ep00001001011101_0
private theorem idp00001001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101110.list =
    C ((2:ℤ)^80) * horner X vp00001001011101.list + horner X ep00001001011101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001011101 : Branch 1 (-301761639/1000000 : ℚ) vp0000100101110 := by
  apply branch_checked idp00001001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-301761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-302261639/500000 : ℚ) by norm_num]
  exact coverp00001001011101
theorem coverp0000100101110 : Covers (-301761639/1000000 : ℚ) vp0000100101110 := join_branches bp00001001011100 bp00001001011101
private noncomputable def vp000010010111_0 : Blocks := edgeBlocks% "full/vectors/000010010111-V-0000.bin"
private noncomputable def vp000010010111_1 : Blocks := edgeBlocks% "full/vectors/000010010111-V-0001.bin"
noncomputable def vp000010010111 : Blocks := (Blocks.join vp000010010111_0 vp000010010111_1)
private theorem bp0000100101110 : Branch 0 (-301761639/2000000 : ℚ) vp000010010111 := by
  apply branch_left_normalized (c:=vp0000100101110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-301761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-301761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101110
private noncomputable def ep0000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000100101111-E-0000.bin"
private noncomputable def ep0000100101111_1 : Blocks := edgeBlocks% "full/vectors/0000100101111-E-0001.bin"
noncomputable def ep0000100101111 : Blocks := (Blocks.join ep0000100101111_0 ep0000100101111_1)
private theorem idp0000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010111.list =
    C ((2:ℤ)^142) * horner X vp0000100101111.list + horner X ep0000100101111.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100101111 : Branch 1 (-301761639/2000000 : ℚ) vp000010010111 := by
  apply branch_checked idp0000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-301761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-302761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101111
theorem coverp000010010111 : Covers (-301761639/2000000 : ℚ) vp000010010111 := join_branches bp0000100101110 bp0000100101111
private noncomputable def vp00001001011011_0 : Blocks := edgeBlocks% "full/vectors/00001001011011-V-0000.bin"
noncomputable def vp00001001011011 : Blocks := vp00001001011011_0
theorem coverp00001001011011 : Covers (-301261639/500000 : ℚ) vp00001001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001011010_0 : Blocks := edgeBlocks% "full/vectors/00001001011010-V-0000.bin"
noncomputable def vp00001001011010 : Blocks := vp00001001011010_0
theorem coverp00001001011010 : Covers (-300761639/500000 : ℚ) vp00001001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100101101_0 : Blocks := edgeBlocks% "full/vectors/0000100101101-V-0000.bin"
noncomputable def vp0000100101101 : Blocks := vp0000100101101_0
private theorem bp00001001011010 : Branch 0 (-300761639/1000000 : ℚ) vp0000100101101 := by
  apply branch_left_normalized (c:=vp00001001011010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-300761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-300761639/500000 : ℚ) by norm_num]
  exact coverp00001001011010
private noncomputable def ep00001001011011_0 : Blocks := edgeBlocks% "full/vectors/00001001011011-E-0000.bin"
noncomputable def ep00001001011011 : Blocks := ep00001001011011_0
private theorem idp00001001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101101.list =
    C ((2:ℤ)^81) * horner X vp00001001011011.list + horner X ep00001001011011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001011011 : Branch 1 (-300761639/1000000 : ℚ) vp0000100101101 := by
  apply branch_checked idp00001001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-300761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-301261639/500000 : ℚ) by norm_num]
  exact coverp00001001011011
theorem coverp0000100101101 : Covers (-300761639/1000000 : ℚ) vp0000100101101 := join_branches bp00001001011010 bp00001001011011
private noncomputable def vp00001001011001_0 : Blocks := edgeBlocks% "full/vectors/00001001011001-V-0000.bin"
noncomputable def vp00001001011001 : Blocks := vp00001001011001_0
theorem coverp00001001011001 : Covers (-300261639/500000 : ℚ) vp00001001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010110001_0 : Blocks := edgeBlocks% "full/vectors/000010010110001-V-0000.bin"
noncomputable def vp000010010110001 : Blocks := vp000010010110001_0
theorem coverp000010010110001 : Covers (-300011639/250000 : ℚ) vp000010010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010110000_0 : Blocks := edgeBlocks% "full/vectors/000010010110000-V-0000.bin"
noncomputable def vp000010010110000 : Blocks := vp000010010110000_0
theorem coverp000010010110000 : Covers (-299761639/250000 : ℚ) vp000010010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001011000_0 : Blocks := edgeBlocks% "full/vectors/00001001011000-V-0000.bin"
noncomputable def vp00001001011000 : Blocks := vp00001001011000_0
private theorem bp000010010110000 : Branch 0 (-299761639/500000 : ℚ) vp00001001011000 := by
  apply branch_left_normalized (c:=vp000010010110000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-299761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-299761639/250000 : ℚ) by norm_num]
  exact coverp000010010110000
private noncomputable def ep000010010110001_0 : Blocks := edgeBlocks% "full/vectors/000010010110001-E-0000.bin"
noncomputable def ep000010010110001 : Blocks := ep000010010110001_0
private theorem idp000010010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001011000.list =
    C ((2:ℤ)^51) * horner X vp000010010110001.list + horner X ep000010010110001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010110001 : Branch 1 (-299761639/500000 : ℚ) vp00001001011000 := by
  apply branch_checked idp000010010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-299761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-300011639/250000 : ℚ) by norm_num]
  exact coverp000010010110001
theorem coverp00001001011000 : Covers (-299761639/500000 : ℚ) vp00001001011000 := join_branches bp000010010110000 bp000010010110001
private noncomputable def vp0000100101100_0 : Blocks := edgeBlocks% "full/vectors/0000100101100-V-0000.bin"
noncomputable def vp0000100101100 : Blocks := vp0000100101100_0
private theorem bp00001001011000 : Branch 0 (-299761639/1000000 : ℚ) vp0000100101100 := by
  apply branch_left_normalized (c:=vp00001001011000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-299761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-299761639/500000 : ℚ) by norm_num]
  exact coverp00001001011000
private noncomputable def ep00001001011001_0 : Blocks := edgeBlocks% "full/vectors/00001001011001-E-0000.bin"
noncomputable def ep00001001011001 : Blocks := ep00001001011001_0
private theorem idp00001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101100.list =
    C ((2:ℤ)^81) * horner X vp00001001011001.list + horner X ep00001001011001.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001011001 : Branch 1 (-299761639/1000000 : ℚ) vp0000100101100 := by
  apply branch_checked idp00001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-299761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-300261639/500000 : ℚ) by norm_num]
  exact coverp00001001011001
theorem coverp0000100101100 : Covers (-299761639/1000000 : ℚ) vp0000100101100 := join_branches bp00001001011000 bp00001001011001
private noncomputable def vp000010010110_0 : Blocks := edgeBlocks% "full/vectors/000010010110-V-0000.bin"
private noncomputable def vp000010010110_1 : Blocks := edgeBlocks% "full/vectors/000010010110-V-0001.bin"
noncomputable def vp000010010110 : Blocks := (Blocks.join vp000010010110_0 vp000010010110_1)
private theorem bp0000100101100 : Branch 0 (-299761639/2000000 : ℚ) vp000010010110 := by
  apply branch_left_normalized (c:=vp0000100101100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-299761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-299761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101100
private noncomputable def ep0000100101101_0 : Blocks := edgeBlocks% "full/vectors/0000100101101-E-0000.bin"
private noncomputable def ep0000100101101_1 : Blocks := edgeBlocks% "full/vectors/0000100101101-E-0001.bin"
noncomputable def ep0000100101101 : Blocks := (Blocks.join ep0000100101101_0 ep0000100101101_1)
private theorem idp0000100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010110.list =
    C ((2:ℤ)^145) * horner X vp0000100101101.list + horner X ep0000100101101.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100101101 : Branch 1 (-299761639/2000000 : ℚ) vp000010010110 := by
  apply branch_checked idp0000100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-299761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-300761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101101
theorem coverp000010010110 : Covers (-299761639/2000000 : ℚ) vp000010010110 := join_branches bp0000100101100 bp0000100101101
private noncomputable def vp00001001011_0 : Blocks := edgeBlocks% "full/vectors/00001001011-V-0000.bin"
private noncomputable def vp00001001011_1 : Blocks := edgeBlocks% "full/vectors/00001001011-V-0001.bin"
noncomputable def vp00001001011 : Blocks := (Blocks.join vp00001001011_0 vp00001001011_1)
private theorem bp000010010110 : Branch 0 (-299761639/4000000 : ℚ) vp00001001011 := by
  apply branch_left_normalized (c:=vp000010010110) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-299761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-299761639/2000000 : ℚ) by norm_num]
  exact coverp000010010110
private noncomputable def ep000010010111_0 : Blocks := edgeBlocks% "full/vectors/000010010111-E-0000.bin"
private noncomputable def ep000010010111_1 : Blocks := edgeBlocks% "full/vectors/000010010111-E-0001.bin"
noncomputable def ep000010010111 : Blocks := (Blocks.join ep000010010111_0 ep000010010111_1)
private theorem idp000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001011.list =
    C ((2:ℤ)^266) * horner X vp000010010111.list + horner X ep000010010111.list := by
  exact edge_identity (B := (2:ℤ)^473) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010111 : Branch 1 (-299761639/4000000 : ℚ) vp00001001011 := by
  apply branch_checked idp000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-299761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-301761639/2000000 : ℚ) by norm_num]
  exact coverp000010010111
theorem coverp00001001011 : Covers (-299761639/4000000 : ℚ) vp00001001011 := join_branches bp000010010110 bp000010010111
private noncomputable def vp000010010101111_0 : Blocks := edgeBlocks% "full/vectors/000010010101111-V-0000.bin"
noncomputable def vp000010010101111 : Blocks := vp000010010101111_0
theorem coverp000010010101111 : Covers (-299511639/250000 : ℚ) vp000010010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010101110_0 : Blocks := edgeBlocks% "full/vectors/000010010101110-V-0000.bin"
noncomputable def vp000010010101110 : Blocks := vp000010010101110_0
theorem coverp000010010101110 : Covers (-299261639/250000 : ℚ) vp000010010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010111_0 : Blocks := edgeBlocks% "full/vectors/00001001010111-V-0000.bin"
noncomputable def vp00001001010111 : Blocks := vp00001001010111_0
private theorem bp000010010101110 : Branch 0 (-299261639/500000 : ℚ) vp00001001010111 := by
  apply branch_left_normalized (c:=vp000010010101110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-299261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-299261639/250000 : ℚ) by norm_num]
  exact coverp000010010101110
private noncomputable def ep000010010101111_0 : Blocks := edgeBlocks% "full/vectors/000010010101111-E-0000.bin"
noncomputable def ep000010010101111 : Blocks := ep000010010101111_0
private theorem idp000010010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010111.list =
    C ((2:ℤ)^50) * horner X vp000010010101111.list + horner X ep000010010101111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010101111 : Branch 1 (-299261639/500000 : ℚ) vp00001001010111 := by
  apply branch_checked idp000010010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-299261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-299511639/250000 : ℚ) by norm_num]
  exact coverp000010010101111
theorem coverp00001001010111 : Covers (-299261639/500000 : ℚ) vp00001001010111 := join_branches bp000010010101110 bp000010010101111
private noncomputable def vp000010010101101_0 : Blocks := edgeBlocks% "full/vectors/000010010101101-V-0000.bin"
noncomputable def vp000010010101101 : Blocks := vp000010010101101_0
theorem coverp000010010101101 : Covers (-299011639/250000 : ℚ) vp000010010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010101100_0 : Blocks := edgeBlocks% "full/vectors/000010010101100-V-0000.bin"
noncomputable def vp000010010101100 : Blocks := vp000010010101100_0
theorem coverp000010010101100 : Covers (-298761639/250000 : ℚ) vp000010010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010110_0 : Blocks := edgeBlocks% "full/vectors/00001001010110-V-0000.bin"
noncomputable def vp00001001010110 : Blocks := vp00001001010110_0
private theorem bp000010010101100 : Branch 0 (-298761639/500000 : ℚ) vp00001001010110 := by
  apply branch_left_normalized (c:=vp000010010101100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-298761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-298761639/250000 : ℚ) by norm_num]
  exact coverp000010010101100
private noncomputable def ep000010010101101_0 : Blocks := edgeBlocks% "full/vectors/000010010101101-E-0000.bin"
noncomputable def ep000010010101101 : Blocks := ep000010010101101_0
private theorem idp000010010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010110.list =
    C ((2:ℤ)^49) * horner X vp000010010101101.list + horner X ep000010010101101.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010101101 : Branch 1 (-298761639/500000 : ℚ) vp00001001010110 := by
  apply branch_checked idp000010010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-298761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-299011639/250000 : ℚ) by norm_num]
  exact coverp000010010101101
theorem coverp00001001010110 : Covers (-298761639/500000 : ℚ) vp00001001010110 := join_branches bp000010010101100 bp000010010101101
private noncomputable def vp0000100101011_0 : Blocks := edgeBlocks% "full/vectors/0000100101011-V-0000.bin"
noncomputable def vp0000100101011 : Blocks := vp0000100101011_0
private theorem bp00001001010110 : Branch 0 (-298761639/1000000 : ℚ) vp0000100101011 := by
  apply branch_left_normalized (c:=vp00001001010110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-298761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-298761639/500000 : ℚ) by norm_num]
  exact coverp00001001010110
private noncomputable def ep00001001010111_0 : Blocks := edgeBlocks% "full/vectors/00001001010111-E-0000.bin"
noncomputable def ep00001001010111 : Blocks := ep00001001010111_0
private theorem idp00001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101011.list =
    C ((2:ℤ)^82) * horner X vp00001001010111.list + horner X ep00001001010111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001010111 : Branch 1 (-298761639/1000000 : ℚ) vp0000100101011 := by
  apply branch_checked idp00001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-298761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-299261639/500000 : ℚ) by norm_num]
  exact coverp00001001010111
theorem coverp0000100101011 : Covers (-298761639/1000000 : ℚ) vp0000100101011 := join_branches bp00001001010110 bp00001001010111
private noncomputable def vp000010010101011_0 : Blocks := edgeBlocks% "full/vectors/000010010101011-V-0000.bin"
noncomputable def vp000010010101011 : Blocks := vp000010010101011_0
theorem coverp000010010101011 : Covers (-298511639/250000 : ℚ) vp000010010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010101010_0 : Blocks := edgeBlocks% "full/vectors/000010010101010-V-0000.bin"
noncomputable def vp000010010101010 : Blocks := vp000010010101010_0
theorem coverp000010010101010 : Covers (-298261639/250000 : ℚ) vp000010010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010101_0 : Blocks := edgeBlocks% "full/vectors/00001001010101-V-0000.bin"
noncomputable def vp00001001010101 : Blocks := vp00001001010101_0
private theorem bp000010010101010 : Branch 0 (-298261639/500000 : ℚ) vp00001001010101 := by
  apply branch_left_normalized (c:=vp000010010101010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-298261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-298261639/250000 : ℚ) by norm_num]
  exact coverp000010010101010
private noncomputable def ep000010010101011_0 : Blocks := edgeBlocks% "full/vectors/000010010101011-E-0000.bin"
noncomputable def ep000010010101011 : Blocks := ep000010010101011_0
private theorem idp000010010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010101.list =
    C ((2:ℤ)^50) * horner X vp000010010101011.list + horner X ep000010010101011.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010101011 : Branch 1 (-298261639/500000 : ℚ) vp00001001010101 := by
  apply branch_checked idp000010010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-298261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-298511639/250000 : ℚ) by norm_num]
  exact coverp000010010101011
theorem coverp00001001010101 : Covers (-298261639/500000 : ℚ) vp00001001010101 := join_branches bp000010010101010 bp000010010101011
private noncomputable def vp000010010101001_0 : Blocks := edgeBlocks% "full/vectors/000010010101001-V-0000.bin"
noncomputable def vp000010010101001 : Blocks := vp000010010101001_0
theorem coverp000010010101001 : Covers (-298011639/250000 : ℚ) vp000010010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010101000_0 : Blocks := edgeBlocks% "full/vectors/000010010101000-V-0000.bin"
noncomputable def vp000010010101000 : Blocks := vp000010010101000_0
theorem coverp000010010101000 : Covers (-297761639/250000 : ℚ) vp000010010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010100_0 : Blocks := edgeBlocks% "full/vectors/00001001010100-V-0000.bin"
noncomputable def vp00001001010100 : Blocks := vp00001001010100_0
private theorem bp000010010101000 : Branch 0 (-297761639/500000 : ℚ) vp00001001010100 := by
  apply branch_left_normalized (c:=vp000010010101000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-297761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-297761639/250000 : ℚ) by norm_num]
  exact coverp000010010101000
private noncomputable def ep000010010101001_0 : Blocks := edgeBlocks% "full/vectors/000010010101001-E-0000.bin"
noncomputable def ep000010010101001 : Blocks := ep000010010101001_0
private theorem idp000010010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010100.list =
    C ((2:ℤ)^51) * horner X vp000010010101001.list + horner X ep000010010101001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010101001 : Branch 1 (-297761639/500000 : ℚ) vp00001001010100 := by
  apply branch_checked idp000010010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-297761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-298011639/250000 : ℚ) by norm_num]
  exact coverp000010010101001
theorem coverp00001001010100 : Covers (-297761639/500000 : ℚ) vp00001001010100 := join_branches bp000010010101000 bp000010010101001
private noncomputable def vp0000100101010_0 : Blocks := edgeBlocks% "full/vectors/0000100101010-V-0000.bin"
noncomputable def vp0000100101010 : Blocks := vp0000100101010_0
private theorem bp00001001010100 : Branch 0 (-297761639/1000000 : ℚ) vp0000100101010 := by
  apply branch_left_normalized (c:=vp00001001010100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-297761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-297761639/500000 : ℚ) by norm_num]
  exact coverp00001001010100
private noncomputable def ep00001001010101_0 : Blocks := edgeBlocks% "full/vectors/00001001010101-E-0000.bin"
noncomputable def ep00001001010101 : Blocks := ep00001001010101_0
private theorem idp00001001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101010.list =
    C ((2:ℤ)^81) * horner X vp00001001010101.list + horner X ep00001001010101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001010101 : Branch 1 (-297761639/1000000 : ℚ) vp0000100101010 := by
  apply branch_checked idp00001001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-297761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-298261639/500000 : ℚ) by norm_num]
  exact coverp00001001010101
theorem coverp0000100101010 : Covers (-297761639/1000000 : ℚ) vp0000100101010 := join_branches bp00001001010100 bp00001001010101
private noncomputable def vp000010010101_0 : Blocks := edgeBlocks% "full/vectors/000010010101-V-0000.bin"
private noncomputable def vp000010010101_1 : Blocks := edgeBlocks% "full/vectors/000010010101-V-0001.bin"
noncomputable def vp000010010101 : Blocks := (Blocks.join vp000010010101_0 vp000010010101_1)
private theorem bp0000100101010 : Branch 0 (-297761639/2000000 : ℚ) vp000010010101 := by
  apply branch_left_normalized (c:=vp0000100101010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-297761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-297761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101010
private noncomputable def ep0000100101011_0 : Blocks := edgeBlocks% "full/vectors/0000100101011-E-0000.bin"
private noncomputable def ep0000100101011_1 : Blocks := edgeBlocks% "full/vectors/0000100101011-E-0001.bin"
noncomputable def ep0000100101011 : Blocks := (Blocks.join ep0000100101011_0 ep0000100101011_1)
private theorem idp0000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010101.list =
    C ((2:ℤ)^143) * horner X vp0000100101011.list + horner X ep0000100101011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100101011 : Branch 1 (-297761639/2000000 : ℚ) vp000010010101 := by
  apply branch_checked idp0000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-297761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-298761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101011
theorem coverp000010010101 : Covers (-297761639/2000000 : ℚ) vp000010010101 := join_branches bp0000100101010 bp0000100101011
private noncomputable def vp000010010100111_0 : Blocks := edgeBlocks% "full/vectors/000010010100111-V-0000.bin"
noncomputable def vp000010010100111 : Blocks := vp000010010100111_0
theorem coverp000010010100111 : Covers (-297511639/250000 : ℚ) vp000010010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010100110_0 : Blocks := edgeBlocks% "full/vectors/000010010100110-V-0000.bin"
noncomputable def vp000010010100110 : Blocks := vp000010010100110_0
theorem coverp000010010100110 : Covers (-297261639/250000 : ℚ) vp000010010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010011_0 : Blocks := edgeBlocks% "full/vectors/00001001010011-V-0000.bin"
noncomputable def vp00001001010011 : Blocks := vp00001001010011_0
private theorem bp000010010100110 : Branch 0 (-297261639/500000 : ℚ) vp00001001010011 := by
  apply branch_left_normalized (c:=vp000010010100110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-297261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-297261639/250000 : ℚ) by norm_num]
  exact coverp000010010100110
private noncomputable def ep000010010100111_0 : Blocks := edgeBlocks% "full/vectors/000010010100111-E-0000.bin"
noncomputable def ep000010010100111 : Blocks := ep000010010100111_0
private theorem idp000010010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010011.list =
    C ((2:ℤ)^51) * horner X vp000010010100111.list + horner X ep000010010100111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010100111 : Branch 1 (-297261639/500000 : ℚ) vp00001001010011 := by
  apply branch_checked idp000010010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-297261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-297511639/250000 : ℚ) by norm_num]
  exact coverp000010010100111
theorem coverp00001001010011 : Covers (-297261639/500000 : ℚ) vp00001001010011 := join_branches bp000010010100110 bp000010010100111
private noncomputable def vp000010010100101_0 : Blocks := edgeBlocks% "full/vectors/000010010100101-V-0000.bin"
noncomputable def vp000010010100101 : Blocks := vp000010010100101_0
theorem coverp000010010100101 : Covers (-297011639/250000 : ℚ) vp000010010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010100100_0 : Blocks := edgeBlocks% "full/vectors/000010010100100-V-0000.bin"
noncomputable def vp000010010100100 : Blocks := vp000010010100100_0
theorem coverp000010010100100 : Covers (-296761639/250000 : ℚ) vp000010010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010010_0 : Blocks := edgeBlocks% "full/vectors/00001001010010-V-0000.bin"
noncomputable def vp00001001010010 : Blocks := vp00001001010010_0
private theorem bp000010010100100 : Branch 0 (-296761639/500000 : ℚ) vp00001001010010 := by
  apply branch_left_normalized (c:=vp000010010100100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-296761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-296761639/250000 : ℚ) by norm_num]
  exact coverp000010010100100
private noncomputable def ep000010010100101_0 : Blocks := edgeBlocks% "full/vectors/000010010100101-E-0000.bin"
noncomputable def ep000010010100101 : Blocks := ep000010010100101_0
private theorem idp000010010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010010.list =
    C ((2:ℤ)^50) * horner X vp000010010100101.list + horner X ep000010010100101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010100101 : Branch 1 (-296761639/500000 : ℚ) vp00001001010010 := by
  apply branch_checked idp000010010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-296761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-297011639/250000 : ℚ) by norm_num]
  exact coverp000010010100101
theorem coverp00001001010010 : Covers (-296761639/500000 : ℚ) vp00001001010010 := join_branches bp000010010100100 bp000010010100101
private noncomputable def vp0000100101001_0 : Blocks := edgeBlocks% "full/vectors/0000100101001-V-0000.bin"
noncomputable def vp0000100101001 : Blocks := vp0000100101001_0
private theorem bp00001001010010 : Branch 0 (-296761639/1000000 : ℚ) vp0000100101001 := by
  apply branch_left_normalized (c:=vp00001001010010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-296761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-296761639/500000 : ℚ) by norm_num]
  exact coverp00001001010010
private noncomputable def ep00001001010011_0 : Blocks := edgeBlocks% "full/vectors/00001001010011-E-0000.bin"
noncomputable def ep00001001010011 : Blocks := ep00001001010011_0
private theorem idp00001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101001.list =
    C ((2:ℤ)^82) * horner X vp00001001010011.list + horner X ep00001001010011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001010011 : Branch 1 (-296761639/1000000 : ℚ) vp0000100101001 := by
  apply branch_checked idp00001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-296761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-297261639/500000 : ℚ) by norm_num]
  exact coverp00001001010011
theorem coverp0000100101001 : Covers (-296761639/1000000 : ℚ) vp0000100101001 := join_branches bp00001001010010 bp00001001010011
private noncomputable def vp000010010100011_0 : Blocks := edgeBlocks% "full/vectors/000010010100011-V-0000.bin"
noncomputable def vp000010010100011 : Blocks := vp000010010100011_0
theorem coverp000010010100011 : Covers (-296511639/250000 : ℚ) vp000010010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010100010_0 : Blocks := edgeBlocks% "full/vectors/000010010100010-V-0000.bin"
noncomputable def vp000010010100010 : Blocks := vp000010010100010_0
theorem coverp000010010100010 : Covers (-296261639/250000 : ℚ) vp000010010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010001_0 : Blocks := edgeBlocks% "full/vectors/00001001010001-V-0000.bin"
noncomputable def vp00001001010001 : Blocks := vp00001001010001_0
private theorem bp000010010100010 : Branch 0 (-296261639/500000 : ℚ) vp00001001010001 := by
  apply branch_left_normalized (c:=vp000010010100010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-296261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-296261639/250000 : ℚ) by norm_num]
  exact coverp000010010100010
private noncomputable def ep000010010100011_0 : Blocks := edgeBlocks% "full/vectors/000010010100011-E-0000.bin"
noncomputable def ep000010010100011 : Blocks := ep000010010100011_0
private theorem idp000010010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010001.list =
    C ((2:ℤ)^50) * horner X vp000010010100011.list + horner X ep000010010100011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010100011 : Branch 1 (-296261639/500000 : ℚ) vp00001001010001 := by
  apply branch_checked idp000010010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-296261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-296511639/250000 : ℚ) by norm_num]
  exact coverp000010010100011
theorem coverp00001001010001 : Covers (-296261639/500000 : ℚ) vp00001001010001 := join_branches bp000010010100010 bp000010010100011
private noncomputable def vp000010010100001_0 : Blocks := edgeBlocks% "full/vectors/000010010100001-V-0000.bin"
noncomputable def vp000010010100001 : Blocks := vp000010010100001_0
theorem coverp000010010100001 : Covers (-296011639/250000 : ℚ) vp000010010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010100000_0 : Blocks := edgeBlocks% "full/vectors/000010010100000-V-0000.bin"
noncomputable def vp000010010100000 : Blocks := vp000010010100000_0
theorem coverp000010010100000 : Covers (-295761639/250000 : ℚ) vp000010010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001010000_0 : Blocks := edgeBlocks% "full/vectors/00001001010000-V-0000.bin"
noncomputable def vp00001001010000 : Blocks := vp00001001010000_0
private theorem bp000010010100000 : Branch 0 (-295761639/500000 : ℚ) vp00001001010000 := by
  apply branch_left_normalized (c:=vp000010010100000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-295761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-295761639/250000 : ℚ) by norm_num]
  exact coverp000010010100000
private noncomputable def ep000010010100001_0 : Blocks := edgeBlocks% "full/vectors/000010010100001-E-0000.bin"
noncomputable def ep000010010100001 : Blocks := ep000010010100001_0
private theorem idp000010010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010000.list =
    C ((2:ℤ)^50) * horner X vp000010010100001.list + horner X ep000010010100001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010100001 : Branch 1 (-295761639/500000 : ℚ) vp00001001010000 := by
  apply branch_checked idp000010010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-295761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-296011639/250000 : ℚ) by norm_num]
  exact coverp000010010100001
theorem coverp00001001010000 : Covers (-295761639/500000 : ℚ) vp00001001010000 := join_branches bp000010010100000 bp000010010100001
private noncomputable def vp0000100101000_0 : Blocks := edgeBlocks% "full/vectors/0000100101000-V-0000.bin"
noncomputable def vp0000100101000 : Blocks := vp0000100101000_0
private theorem bp00001001010000 : Branch 0 (-295761639/1000000 : ℚ) vp0000100101000 := by
  apply branch_left_normalized (c:=vp00001001010000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-295761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-295761639/500000 : ℚ) by norm_num]
  exact coverp00001001010000
private noncomputable def ep00001001010001_0 : Blocks := edgeBlocks% "full/vectors/00001001010001-E-0000.bin"
noncomputable def ep00001001010001 : Blocks := ep00001001010001_0
private theorem idp00001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101000.list =
    C ((2:ℤ)^82) * horner X vp00001001010001.list + horner X ep00001001010001.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001010001 : Branch 1 (-295761639/1000000 : ℚ) vp0000100101000 := by
  apply branch_checked idp00001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-295761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-296261639/500000 : ℚ) by norm_num]
  exact coverp00001001010001
theorem coverp0000100101000 : Covers (-295761639/1000000 : ℚ) vp0000100101000 := join_branches bp00001001010000 bp00001001010001
private noncomputable def vp000010010100_0 : Blocks := edgeBlocks% "full/vectors/000010010100-V-0000.bin"
private noncomputable def vp000010010100_1 : Blocks := edgeBlocks% "full/vectors/000010010100-V-0001.bin"
noncomputable def vp000010010100 : Blocks := (Blocks.join vp000010010100_0 vp000010010100_1)
private theorem bp0000100101000 : Branch 0 (-295761639/2000000 : ℚ) vp000010010100 := by
  apply branch_left_normalized (c:=vp0000100101000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-295761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-295761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101000
private noncomputable def ep0000100101001_0 : Blocks := edgeBlocks% "full/vectors/0000100101001-E-0000.bin"
private noncomputable def ep0000100101001_1 : Blocks := edgeBlocks% "full/vectors/0000100101001-E-0001.bin"
noncomputable def ep0000100101001 : Blocks := (Blocks.join ep0000100101001_0 ep0000100101001_1)
private theorem idp0000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010100.list =
    C ((2:ℤ)^143) * horner X vp0000100101001.list + horner X ep0000100101001.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100101001 : Branch 1 (-295761639/2000000 : ℚ) vp000010010100 := by
  apply branch_checked idp0000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-295761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-296761639/1000000 : ℚ) by norm_num]
  exact coverp0000100101001
theorem coverp000010010100 : Covers (-295761639/2000000 : ℚ) vp000010010100 := join_branches bp0000100101000 bp0000100101001
private noncomputable def vp00001001010_0 : Blocks := edgeBlocks% "full/vectors/00001001010-V-0000.bin"
private noncomputable def vp00001001010_1 : Blocks := edgeBlocks% "full/vectors/00001001010-V-0001.bin"
noncomputable def vp00001001010 : Blocks := (Blocks.join vp00001001010_0 vp00001001010_1)
private theorem bp000010010100 : Branch 0 (-295761639/4000000 : ℚ) vp00001001010 := by
  apply branch_left_normalized (c:=vp000010010100) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-295761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-295761639/2000000 : ℚ) by norm_num]
  exact coverp000010010100
private noncomputable def ep000010010101_0 : Blocks := edgeBlocks% "full/vectors/000010010101-E-0000.bin"
private noncomputable def ep000010010101_1 : Blocks := edgeBlocks% "full/vectors/000010010101-E-0001.bin"
noncomputable def ep000010010101 : Blocks := (Blocks.join ep000010010101_0 ep000010010101_1)
private theorem idp000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001010.list =
    C ((2:ℤ)^264) * horner X vp000010010101.list + horner X ep000010010101.list := by
  exact edge_identity (B := (2:ℤ)^476) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010101 : Branch 1 (-295761639/4000000 : ℚ) vp00001001010 := by
  apply branch_checked idp000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-295761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-297761639/2000000 : ℚ) by norm_num]
  exact coverp000010010101
theorem coverp00001001010 : Covers (-295761639/4000000 : ℚ) vp00001001010 := join_branches bp000010010100 bp000010010101
private noncomputable def vp0000100101_0 : Blocks := edgeBlocks% "full/vectors/0000100101-V-0000.bin"
private noncomputable def vp0000100101_1 : Blocks := edgeBlocks% "full/vectors/0000100101-V-0001.bin"
private noncomputable def vp0000100101_2 : Blocks := edgeBlocks% "full/vectors/0000100101-V-0002.bin"
private noncomputable def vp0000100101_3 : Blocks := edgeBlocks% "full/vectors/0000100101-V-0003.bin"
noncomputable def vp0000100101 : Blocks := (Blocks.join (Blocks.join vp0000100101_0 vp0000100101_1) (Blocks.join vp0000100101_2 vp0000100101_3))
private theorem bp00001001010 : Branch 0 (-295761639/8000000 : ℚ) vp0000100101 := by
  apply branch_left_normalized (c:=vp00001001010) (k:=0) (m:=251) (by decide +kernel)
  rw [show 2*(-295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-295761639/4000000 : ℚ) by norm_num]
  exact coverp00001001010
private noncomputable def ep00001001011_0 : Blocks := edgeBlocks% "full/vectors/00001001011-E-0000.bin"
private noncomputable def ep00001001011_1 : Blocks := edgeBlocks% "full/vectors/00001001011-E-0001.bin"
private noncomputable def ep00001001011_2 : Blocks := edgeBlocks% "full/vectors/00001001011-E-0002.bin"
private noncomputable def ep00001001011_3 : Blocks := edgeBlocks% "full/vectors/00001001011-E-0003.bin"
noncomputable def ep00001001011 : Blocks := (Blocks.join (Blocks.join ep00001001011_0 ep00001001011_1) (Blocks.join ep00001001011_2 ep00001001011_3))
private theorem idp00001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100101.list =
    C ((2:ℤ)^501) * horner X vp00001001011.list + horner X ep00001001011.list := by
  exact edge_identity (B := (2:ℤ)^823) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001011 : Branch 1 (-295761639/8000000 : ℚ) vp0000100101 := by
  apply branch_checked idp00001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-299761639/4000000 : ℚ) by norm_num]
  exact coverp00001001011
theorem coverp0000100101 : Covers (-295761639/8000000 : ℚ) vp0000100101 := join_branches bp00001001010 bp00001001011
private noncomputable def vp000010010011111_0 : Blocks := edgeBlocks% "full/vectors/000010010011111-V-0000.bin"
noncomputable def vp000010010011111 : Blocks := vp000010010011111_0
theorem coverp000010010011111 : Covers (-295511639/250000 : ℚ) vp000010010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010011110_0 : Blocks := edgeBlocks% "full/vectors/000010010011110-V-0000.bin"
noncomputable def vp000010010011110 : Blocks := vp000010010011110_0
theorem coverp000010010011110 : Covers (-295261639/250000 : ℚ) vp000010010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001111_0 : Blocks := edgeBlocks% "full/vectors/00001001001111-V-0000.bin"
noncomputable def vp00001001001111 : Blocks := vp00001001001111_0
private theorem bp000010010011110 : Branch 0 (-295261639/500000 : ℚ) vp00001001001111 := by
  apply branch_left_normalized (c:=vp000010010011110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-295261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-295261639/250000 : ℚ) by norm_num]
  exact coverp000010010011110
private noncomputable def ep000010010011111_0 : Blocks := edgeBlocks% "full/vectors/000010010011111-E-0000.bin"
noncomputable def ep000010010011111 : Blocks := ep000010010011111_0
private theorem idp000010010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001111.list =
    C ((2:ℤ)^51) * horner X vp000010010011111.list + horner X ep000010010011111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010011111 : Branch 1 (-295261639/500000 : ℚ) vp00001001001111 := by
  apply branch_checked idp000010010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-295261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-295511639/250000 : ℚ) by norm_num]
  exact coverp000010010011111
theorem coverp00001001001111 : Covers (-295261639/500000 : ℚ) vp00001001001111 := join_branches bp000010010011110 bp000010010011111
private noncomputable def vp000010010011101_0 : Blocks := edgeBlocks% "full/vectors/000010010011101-V-0000.bin"
noncomputable def vp000010010011101 : Blocks := vp000010010011101_0
theorem coverp000010010011101 : Covers (-295011639/250000 : ℚ) vp000010010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010011100_0 : Blocks := edgeBlocks% "full/vectors/000010010011100-V-0000.bin"
noncomputable def vp000010010011100 : Blocks := vp000010010011100_0
theorem coverp000010010011100 : Covers (-294761639/250000 : ℚ) vp000010010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001110_0 : Blocks := edgeBlocks% "full/vectors/00001001001110-V-0000.bin"
noncomputable def vp00001001001110 : Blocks := vp00001001001110_0
private theorem bp000010010011100 : Branch 0 (-294761639/500000 : ℚ) vp00001001001110 := by
  apply branch_left_normalized (c:=vp000010010011100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-294761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-294761639/250000 : ℚ) by norm_num]
  exact coverp000010010011100
private noncomputable def ep000010010011101_0 : Blocks := edgeBlocks% "full/vectors/000010010011101-E-0000.bin"
noncomputable def ep000010010011101 : Blocks := ep000010010011101_0
private theorem idp000010010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001110.list =
    C ((2:ℤ)^49) * horner X vp000010010011101.list + horner X ep000010010011101.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010011101 : Branch 1 (-294761639/500000 : ℚ) vp00001001001110 := by
  apply branch_checked idp000010010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-294761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-295011639/250000 : ℚ) by norm_num]
  exact coverp000010010011101
theorem coverp00001001001110 : Covers (-294761639/500000 : ℚ) vp00001001001110 := join_branches bp000010010011100 bp000010010011101
private noncomputable def vp0000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000100100111-V-0000.bin"
noncomputable def vp0000100100111 : Blocks := vp0000100100111_0
private theorem bp00001001001110 : Branch 0 (-294761639/1000000 : ℚ) vp0000100100111 := by
  apply branch_left_normalized (c:=vp00001001001110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-294761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-294761639/500000 : ℚ) by norm_num]
  exact coverp00001001001110
private noncomputable def ep00001001001111_0 : Blocks := edgeBlocks% "full/vectors/00001001001111-E-0000.bin"
noncomputable def ep00001001001111 : Blocks := ep00001001001111_0
private theorem idp00001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100111.list =
    C ((2:ℤ)^81) * horner X vp00001001001111.list + horner X ep00001001001111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001001111 : Branch 1 (-294761639/1000000 : ℚ) vp0000100100111 := by
  apply branch_checked idp00001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-294761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-295261639/500000 : ℚ) by norm_num]
  exact coverp00001001001111
theorem coverp0000100100111 : Covers (-294761639/1000000 : ℚ) vp0000100100111 := join_branches bp00001001001110 bp00001001001111
private noncomputable def vp000010010011011_0 : Blocks := edgeBlocks% "full/vectors/000010010011011-V-0000.bin"
noncomputable def vp000010010011011 : Blocks := vp000010010011011_0
theorem coverp000010010011011 : Covers (-294511639/250000 : ℚ) vp000010010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010011010_0 : Blocks := edgeBlocks% "full/vectors/000010010011010-V-0000.bin"
noncomputable def vp000010010011010 : Blocks := vp000010010011010_0
theorem coverp000010010011010 : Covers (-294261639/250000 : ℚ) vp000010010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001101_0 : Blocks := edgeBlocks% "full/vectors/00001001001101-V-0000.bin"
noncomputable def vp00001001001101 : Blocks := vp00001001001101_0
private theorem bp000010010011010 : Branch 0 (-294261639/500000 : ℚ) vp00001001001101 := by
  apply branch_left_normalized (c:=vp000010010011010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-294261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-294261639/250000 : ℚ) by norm_num]
  exact coverp000010010011010
private noncomputable def ep000010010011011_0 : Blocks := edgeBlocks% "full/vectors/000010010011011-E-0000.bin"
noncomputable def ep000010010011011 : Blocks := ep000010010011011_0
private theorem idp000010010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001101.list =
    C ((2:ℤ)^50) * horner X vp000010010011011.list + horner X ep000010010011011.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010011011 : Branch 1 (-294261639/500000 : ℚ) vp00001001001101 := by
  apply branch_checked idp000010010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-294261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-294511639/250000 : ℚ) by norm_num]
  exact coverp000010010011011
theorem coverp00001001001101 : Covers (-294261639/500000 : ℚ) vp00001001001101 := join_branches bp000010010011010 bp000010010011011
private noncomputable def vp000010010011001_0 : Blocks := edgeBlocks% "full/vectors/000010010011001-V-0000.bin"
noncomputable def vp000010010011001 : Blocks := vp000010010011001_0
theorem coverp000010010011001 : Covers (-294011639/250000 : ℚ) vp000010010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010011000_0 : Blocks := edgeBlocks% "full/vectors/000010010011000-V-0000.bin"
noncomputable def vp000010010011000 : Blocks := vp000010010011000_0
theorem coverp000010010011000 : Covers (-293761639/250000 : ℚ) vp000010010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001100_0 : Blocks := edgeBlocks% "full/vectors/00001001001100-V-0000.bin"
noncomputable def vp00001001001100 : Blocks := vp00001001001100_0
private theorem bp000010010011000 : Branch 0 (-293761639/500000 : ℚ) vp00001001001100 := by
  apply branch_left_normalized (c:=vp000010010011000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-293761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-293761639/250000 : ℚ) by norm_num]
  exact coverp000010010011000
private noncomputable def ep000010010011001_0 : Blocks := edgeBlocks% "full/vectors/000010010011001-E-0000.bin"
noncomputable def ep000010010011001 : Blocks := ep000010010011001_0
private theorem idp000010010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001100.list =
    C ((2:ℤ)^50) * horner X vp000010010011001.list + horner X ep000010010011001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010011001 : Branch 1 (-293761639/500000 : ℚ) vp00001001001100 := by
  apply branch_checked idp000010010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-293761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-294011639/250000 : ℚ) by norm_num]
  exact coverp000010010011001
theorem coverp00001001001100 : Covers (-293761639/500000 : ℚ) vp00001001001100 := join_branches bp000010010011000 bp000010010011001
private noncomputable def vp0000100100110_0 : Blocks := edgeBlocks% "full/vectors/0000100100110-V-0000.bin"
noncomputable def vp0000100100110 : Blocks := vp0000100100110_0
private theorem bp00001001001100 : Branch 0 (-293761639/1000000 : ℚ) vp0000100100110 := by
  apply branch_left_normalized (c:=vp00001001001100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-293761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-293761639/500000 : ℚ) by norm_num]
  exact coverp00001001001100
private noncomputable def ep00001001001101_0 : Blocks := edgeBlocks% "full/vectors/00001001001101-E-0000.bin"
noncomputable def ep00001001001101 : Blocks := ep00001001001101_0
private theorem idp00001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100110.list =
    C ((2:ℤ)^82) * horner X vp00001001001101.list + horner X ep00001001001101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001001101 : Branch 1 (-293761639/1000000 : ℚ) vp0000100100110 := by
  apply branch_checked idp00001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-293761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-294261639/500000 : ℚ) by norm_num]
  exact coverp00001001001101
theorem coverp0000100100110 : Covers (-293761639/1000000 : ℚ) vp0000100100110 := join_branches bp00001001001100 bp00001001001101
private noncomputable def vp000010010011_0 : Blocks := edgeBlocks% "full/vectors/000010010011-V-0000.bin"
private noncomputable def vp000010010011_1 : Blocks := edgeBlocks% "full/vectors/000010010011-V-0001.bin"
noncomputable def vp000010010011 : Blocks := (Blocks.join vp000010010011_0 vp000010010011_1)
private theorem bp0000100100110 : Branch 0 (-293761639/2000000 : ℚ) vp000010010011 := by
  apply branch_left_normalized (c:=vp0000100100110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-293761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-293761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100110
private noncomputable def ep0000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000100100111-E-0000.bin"
private noncomputable def ep0000100100111_1 : Blocks := edgeBlocks% "full/vectors/0000100100111-E-0001.bin"
noncomputable def ep0000100100111 : Blocks := (Blocks.join ep0000100100111_0 ep0000100100111_1)
private theorem idp0000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010011.list =
    C ((2:ℤ)^144) * horner X vp0000100100111.list + horner X ep0000100100111.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100100111 : Branch 1 (-293761639/2000000 : ℚ) vp000010010011 := by
  apply branch_checked idp0000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-293761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-294761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100111
theorem coverp000010010011 : Covers (-293761639/2000000 : ℚ) vp000010010011 := join_branches bp0000100100110 bp0000100100111
private noncomputable def vp000010010010111_0 : Blocks := edgeBlocks% "full/vectors/000010010010111-V-0000.bin"
noncomputable def vp000010010010111 : Blocks := vp000010010010111_0
theorem coverp000010010010111 : Covers (-293511639/250000 : ℚ) vp000010010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010010110_0 : Blocks := edgeBlocks% "full/vectors/000010010010110-V-0000.bin"
noncomputable def vp000010010010110 : Blocks := vp000010010010110_0
theorem coverp000010010010110 : Covers (-293261639/250000 : ℚ) vp000010010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001011_0 : Blocks := edgeBlocks% "full/vectors/00001001001011-V-0000.bin"
noncomputable def vp00001001001011 : Blocks := vp00001001001011_0
private theorem bp000010010010110 : Branch 0 (-293261639/500000 : ℚ) vp00001001001011 := by
  apply branch_left_normalized (c:=vp000010010010110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-293261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-293261639/250000 : ℚ) by norm_num]
  exact coverp000010010010110
private noncomputable def ep000010010010111_0 : Blocks := edgeBlocks% "full/vectors/000010010010111-E-0000.bin"
noncomputable def ep000010010010111 : Blocks := ep000010010010111_0
private theorem idp000010010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001011.list =
    C ((2:ℤ)^50) * horner X vp000010010010111.list + horner X ep000010010010111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010010111 : Branch 1 (-293261639/500000 : ℚ) vp00001001001011 := by
  apply branch_checked idp000010010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-293261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-293511639/250000 : ℚ) by norm_num]
  exact coverp000010010010111
theorem coverp00001001001011 : Covers (-293261639/500000 : ℚ) vp00001001001011 := join_branches bp000010010010110 bp000010010010111
private noncomputable def vp000010010010101_0 : Blocks := edgeBlocks% "full/vectors/000010010010101-V-0000.bin"
noncomputable def vp000010010010101 : Blocks := vp000010010010101_0
theorem coverp000010010010101 : Covers (-293011639/250000 : ℚ) vp000010010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010010100_0 : Blocks := edgeBlocks% "full/vectors/000010010010100-V-0000.bin"
noncomputable def vp000010010010100 : Blocks := vp000010010010100_0
theorem coverp000010010010100 : Covers (-292761639/250000 : ℚ) vp000010010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001010_0 : Blocks := edgeBlocks% "full/vectors/00001001001010-V-0000.bin"
noncomputable def vp00001001001010 : Blocks := vp00001001001010_0
private theorem bp000010010010100 : Branch 0 (-292761639/500000 : ℚ) vp00001001001010 := by
  apply branch_left_normalized (c:=vp000010010010100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-292761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-292761639/250000 : ℚ) by norm_num]
  exact coverp000010010010100
private noncomputable def ep000010010010101_0 : Blocks := edgeBlocks% "full/vectors/000010010010101-E-0000.bin"
noncomputable def ep000010010010101 : Blocks := ep000010010010101_0
private theorem idp000010010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001010.list =
    C ((2:ℤ)^50) * horner X vp000010010010101.list + horner X ep000010010010101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010010101 : Branch 1 (-292761639/500000 : ℚ) vp00001001001010 := by
  apply branch_checked idp000010010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-292761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-293011639/250000 : ℚ) by norm_num]
  exact coverp000010010010101
theorem coverp00001001001010 : Covers (-292761639/500000 : ℚ) vp00001001001010 := join_branches bp000010010010100 bp000010010010101
private noncomputable def vp0000100100101_0 : Blocks := edgeBlocks% "full/vectors/0000100100101-V-0000.bin"
noncomputable def vp0000100100101 : Blocks := vp0000100100101_0
private theorem bp00001001001010 : Branch 0 (-292761639/1000000 : ℚ) vp0000100100101 := by
  apply branch_left_normalized (c:=vp00001001001010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-292761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-292761639/500000 : ℚ) by norm_num]
  exact coverp00001001001010
private noncomputable def ep00001001001011_0 : Blocks := edgeBlocks% "full/vectors/00001001001011-E-0000.bin"
noncomputable def ep00001001001011 : Blocks := ep00001001001011_0
private theorem idp00001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100101.list =
    C ((2:ℤ)^83) * horner X vp00001001001011.list + horner X ep00001001001011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001001011 : Branch 1 (-292761639/1000000 : ℚ) vp0000100100101 := by
  apply branch_checked idp00001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-292761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-293261639/500000 : ℚ) by norm_num]
  exact coverp00001001001011
theorem coverp0000100100101 : Covers (-292761639/1000000 : ℚ) vp0000100100101 := join_branches bp00001001001010 bp00001001001011
private noncomputable def vp000010010010011_0 : Blocks := edgeBlocks% "full/vectors/000010010010011-V-0000.bin"
noncomputable def vp000010010010011 : Blocks := vp000010010010011_0
theorem coverp000010010010011 : Covers (-292511639/250000 : ℚ) vp000010010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010010010_0 : Blocks := edgeBlocks% "full/vectors/000010010010010-V-0000.bin"
noncomputable def vp000010010010010 : Blocks := vp000010010010010_0
theorem coverp000010010010010 : Covers (-292261639/250000 : ℚ) vp000010010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001001_0 : Blocks := edgeBlocks% "full/vectors/00001001001001-V-0000.bin"
noncomputable def vp00001001001001 : Blocks := vp00001001001001_0
private theorem bp000010010010010 : Branch 0 (-292261639/500000 : ℚ) vp00001001001001 := by
  apply branch_left_normalized (c:=vp000010010010010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-292261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-292261639/250000 : ℚ) by norm_num]
  exact coverp000010010010010
private noncomputable def ep000010010010011_0 : Blocks := edgeBlocks% "full/vectors/000010010010011-E-0000.bin"
noncomputable def ep000010010010011 : Blocks := ep000010010010011_0
private theorem idp000010010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001001.list =
    C ((2:ℤ)^50) * horner X vp000010010010011.list + horner X ep000010010010011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010010011 : Branch 1 (-292261639/500000 : ℚ) vp00001001001001 := by
  apply branch_checked idp000010010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-292261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-292511639/250000 : ℚ) by norm_num]
  exact coverp000010010010011
theorem coverp00001001001001 : Covers (-292261639/500000 : ℚ) vp00001001001001 := join_branches bp000010010010010 bp000010010010011
private noncomputable def vp000010010010001_0 : Blocks := edgeBlocks% "full/vectors/000010010010001-V-0000.bin"
noncomputable def vp000010010010001 : Blocks := vp000010010010001_0
theorem coverp000010010010001 : Covers (-292011639/250000 : ℚ) vp000010010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010010000_0 : Blocks := edgeBlocks% "full/vectors/000010010010000-V-0000.bin"
noncomputable def vp000010010010000 : Blocks := vp000010010010000_0
theorem coverp000010010010000 : Covers (-291761639/250000 : ℚ) vp000010010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001001000_0 : Blocks := edgeBlocks% "full/vectors/00001001001000-V-0000.bin"
noncomputable def vp00001001001000 : Blocks := vp00001001001000_0
private theorem bp000010010010000 : Branch 0 (-291761639/500000 : ℚ) vp00001001001000 := by
  apply branch_left_normalized (c:=vp000010010010000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-291761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-291761639/250000 : ℚ) by norm_num]
  exact coverp000010010010000
private noncomputable def ep000010010010001_0 : Blocks := edgeBlocks% "full/vectors/000010010010001-E-0000.bin"
noncomputable def ep000010010010001 : Blocks := ep000010010010001_0
private theorem idp000010010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001000.list =
    C ((2:ℤ)^50) * horner X vp000010010010001.list + horner X ep000010010010001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010010001 : Branch 1 (-291761639/500000 : ℚ) vp00001001001000 := by
  apply branch_checked idp000010010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-291761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-292011639/250000 : ℚ) by norm_num]
  exact coverp000010010010001
theorem coverp00001001001000 : Covers (-291761639/500000 : ℚ) vp00001001001000 := join_branches bp000010010010000 bp000010010010001
private noncomputable def vp0000100100100_0 : Blocks := edgeBlocks% "full/vectors/0000100100100-V-0000.bin"
noncomputable def vp0000100100100 : Blocks := vp0000100100100_0
private theorem bp00001001001000 : Branch 0 (-291761639/1000000 : ℚ) vp0000100100100 := by
  apply branch_left_normalized (c:=vp00001001001000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-291761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-291761639/500000 : ℚ) by norm_num]
  exact coverp00001001001000
private noncomputable def ep00001001001001_0 : Blocks := edgeBlocks% "full/vectors/00001001001001-E-0000.bin"
noncomputable def ep00001001001001 : Blocks := ep00001001001001_0
private theorem idp00001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100100.list =
    C ((2:ℤ)^82) * horner X vp00001001001001.list + horner X ep00001001001001.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001001001 : Branch 1 (-291761639/1000000 : ℚ) vp0000100100100 := by
  apply branch_checked idp00001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-291761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-292261639/500000 : ℚ) by norm_num]
  exact coverp00001001001001
theorem coverp0000100100100 : Covers (-291761639/1000000 : ℚ) vp0000100100100 := join_branches bp00001001001000 bp00001001001001
private noncomputable def vp000010010010_0 : Blocks := edgeBlocks% "full/vectors/000010010010-V-0000.bin"
private noncomputable def vp000010010010_1 : Blocks := edgeBlocks% "full/vectors/000010010010-V-0001.bin"
noncomputable def vp000010010010 : Blocks := (Blocks.join vp000010010010_0 vp000010010010_1)
private theorem bp0000100100100 : Branch 0 (-291761639/2000000 : ℚ) vp000010010010 := by
  apply branch_left_normalized (c:=vp0000100100100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-291761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-291761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100100
private noncomputable def ep0000100100101_0 : Blocks := edgeBlocks% "full/vectors/0000100100101-E-0000.bin"
private noncomputable def ep0000100100101_1 : Blocks := edgeBlocks% "full/vectors/0000100100101-E-0001.bin"
noncomputable def ep0000100100101 : Blocks := (Blocks.join ep0000100100101_0 ep0000100100101_1)
private theorem idp0000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010010.list =
    C ((2:ℤ)^144) * horner X vp0000100100101.list + horner X ep0000100100101.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100100101 : Branch 1 (-291761639/2000000 : ℚ) vp000010010010 := by
  apply branch_checked idp0000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-291761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-292761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100101
theorem coverp000010010010 : Covers (-291761639/2000000 : ℚ) vp000010010010 := join_branches bp0000100100100 bp0000100100101
private noncomputable def vp00001001001_0 : Blocks := edgeBlocks% "full/vectors/00001001001-V-0000.bin"
private noncomputable def vp00001001001_1 : Blocks := edgeBlocks% "full/vectors/00001001001-V-0001.bin"
noncomputable def vp00001001001 : Blocks := (Blocks.join vp00001001001_0 vp00001001001_1)
private theorem bp000010010010 : Branch 0 (-291761639/4000000 : ℚ) vp00001001001 := by
  apply branch_left_normalized (c:=vp000010010010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-291761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-291761639/2000000 : ℚ) by norm_num]
  exact coverp000010010010
private noncomputable def ep000010010011_0 : Blocks := edgeBlocks% "full/vectors/000010010011-E-0000.bin"
private noncomputable def ep000010010011_1 : Blocks := edgeBlocks% "full/vectors/000010010011-E-0001.bin"
noncomputable def ep000010010011 : Blocks := (Blocks.join ep000010010011_0 ep000010010011_1)
private theorem idp000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001001.list =
    C ((2:ℤ)^265) * horner X vp000010010011.list + horner X ep000010010011.list := by
  exact edge_identity (B := (2:ℤ)^477) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010011 : Branch 1 (-291761639/4000000 : ℚ) vp00001001001 := by
  apply branch_checked idp000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-291761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-293761639/2000000 : ℚ) by norm_num]
  exact coverp000010010011
theorem coverp00001001001 : Covers (-291761639/4000000 : ℚ) vp00001001001 := join_branches bp000010010010 bp000010010011
private noncomputable def vp000010010001111_0 : Blocks := edgeBlocks% "full/vectors/000010010001111-V-0000.bin"
noncomputable def vp000010010001111 : Blocks := vp000010010001111_0
theorem coverp000010010001111 : Covers (-291511639/250000 : ℚ) vp000010010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010001110_0 : Blocks := edgeBlocks% "full/vectors/000010010001110-V-0000.bin"
noncomputable def vp000010010001110 : Blocks := vp000010010001110_0
theorem coverp000010010001110 : Covers (-291261639/250000 : ℚ) vp000010010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000111_0 : Blocks := edgeBlocks% "full/vectors/00001001000111-V-0000.bin"
noncomputable def vp00001001000111 : Blocks := vp00001001000111_0
private theorem bp000010010001110 : Branch 0 (-291261639/500000 : ℚ) vp00001001000111 := by
  apply branch_left_normalized (c:=vp000010010001110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-291261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-291261639/250000 : ℚ) by norm_num]
  exact coverp000010010001110
private noncomputable def ep000010010001111_0 : Blocks := edgeBlocks% "full/vectors/000010010001111-E-0000.bin"
noncomputable def ep000010010001111 : Blocks := ep000010010001111_0
private theorem idp000010010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000111.list =
    C ((2:ℤ)^50) * horner X vp000010010001111.list + horner X ep000010010001111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010001111 : Branch 1 (-291261639/500000 : ℚ) vp00001001000111 := by
  apply branch_checked idp000010010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-291261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-291511639/250000 : ℚ) by norm_num]
  exact coverp000010010001111
theorem coverp00001001000111 : Covers (-291261639/500000 : ℚ) vp00001001000111 := join_branches bp000010010001110 bp000010010001111
private noncomputable def vp000010010001101_0 : Blocks := edgeBlocks% "full/vectors/000010010001101-V-0000.bin"
noncomputable def vp000010010001101 : Blocks := vp000010010001101_0
theorem coverp000010010001101 : Covers (-291011639/250000 : ℚ) vp000010010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010001100_0 : Blocks := edgeBlocks% "full/vectors/000010010001100-V-0000.bin"
noncomputable def vp000010010001100 : Blocks := vp000010010001100_0
theorem coverp000010010001100 : Covers (-290761639/250000 : ℚ) vp000010010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000110_0 : Blocks := edgeBlocks% "full/vectors/00001001000110-V-0000.bin"
noncomputable def vp00001001000110 : Blocks := vp00001001000110_0
private theorem bp000010010001100 : Branch 0 (-290761639/500000 : ℚ) vp00001001000110 := by
  apply branch_left_normalized (c:=vp000010010001100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-290761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-290761639/250000 : ℚ) by norm_num]
  exact coverp000010010001100
private noncomputable def ep000010010001101_0 : Blocks := edgeBlocks% "full/vectors/000010010001101-E-0000.bin"
noncomputable def ep000010010001101 : Blocks := ep000010010001101_0
private theorem idp000010010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000110.list =
    C ((2:ℤ)^51) * horner X vp000010010001101.list + horner X ep000010010001101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010001101 : Branch 1 (-290761639/500000 : ℚ) vp00001001000110 := by
  apply branch_checked idp000010010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-290761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-291011639/250000 : ℚ) by norm_num]
  exact coverp000010010001101
theorem coverp00001001000110 : Covers (-290761639/500000 : ℚ) vp00001001000110 := join_branches bp000010010001100 bp000010010001101
private noncomputable def vp0000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000100100011-V-0000.bin"
noncomputable def vp0000100100011 : Blocks := vp0000100100011_0
private theorem bp00001001000110 : Branch 0 (-290761639/1000000 : ℚ) vp0000100100011 := by
  apply branch_left_normalized (c:=vp00001001000110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-290761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-290761639/500000 : ℚ) by norm_num]
  exact coverp00001001000110
private noncomputable def ep00001001000111_0 : Blocks := edgeBlocks% "full/vectors/00001001000111-E-0000.bin"
noncomputable def ep00001001000111 : Blocks := ep00001001000111_0
private theorem idp00001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100011.list =
    C ((2:ℤ)^83) * horner X vp00001001000111.list + horner X ep00001001000111.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001000111 : Branch 1 (-290761639/1000000 : ℚ) vp0000100100011 := by
  apply branch_checked idp00001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-290761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-291261639/500000 : ℚ) by norm_num]
  exact coverp00001001000111
theorem coverp0000100100011 : Covers (-290761639/1000000 : ℚ) vp0000100100011 := join_branches bp00001001000110 bp00001001000111
private noncomputable def vp000010010001011_0 : Blocks := edgeBlocks% "full/vectors/000010010001011-V-0000.bin"
noncomputable def vp000010010001011 : Blocks := vp000010010001011_0
theorem coverp000010010001011 : Covers (-290511639/250000 : ℚ) vp000010010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010001010_0 : Blocks := edgeBlocks% "full/vectors/000010010001010-V-0000.bin"
noncomputable def vp000010010001010 : Blocks := vp000010010001010_0
theorem coverp000010010001010 : Covers (-290261639/250000 : ℚ) vp000010010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000101_0 : Blocks := edgeBlocks% "full/vectors/00001001000101-V-0000.bin"
noncomputable def vp00001001000101 : Blocks := vp00001001000101_0
private theorem bp000010010001010 : Branch 0 (-290261639/500000 : ℚ) vp00001001000101 := by
  apply branch_left_normalized (c:=vp000010010001010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-290261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-290261639/250000 : ℚ) by norm_num]
  exact coverp000010010001010
private noncomputable def ep000010010001011_0 : Blocks := edgeBlocks% "full/vectors/000010010001011-E-0000.bin"
noncomputable def ep000010010001011 : Blocks := ep000010010001011_0
private theorem idp000010010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000101.list =
    C ((2:ℤ)^51) * horner X vp000010010001011.list + horner X ep000010010001011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010001011 : Branch 1 (-290261639/500000 : ℚ) vp00001001000101 := by
  apply branch_checked idp000010010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-290261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-290511639/250000 : ℚ) by norm_num]
  exact coverp000010010001011
theorem coverp00001001000101 : Covers (-290261639/500000 : ℚ) vp00001001000101 := join_branches bp000010010001010 bp000010010001011
private noncomputable def vp000010010001001_0 : Blocks := edgeBlocks% "full/vectors/000010010001001-V-0000.bin"
noncomputable def vp000010010001001 : Blocks := vp000010010001001_0
theorem coverp000010010001001 : Covers (-290011639/250000 : ℚ) vp000010010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010001000_0 : Blocks := edgeBlocks% "full/vectors/000010010001000-V-0000.bin"
noncomputable def vp000010010001000 : Blocks := vp000010010001000_0
theorem coverp000010010001000 : Covers (-289761639/250000 : ℚ) vp000010010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000100_0 : Blocks := edgeBlocks% "full/vectors/00001001000100-V-0000.bin"
noncomputable def vp00001001000100 : Blocks := vp00001001000100_0
private theorem bp000010010001000 : Branch 0 (-289761639/500000 : ℚ) vp00001001000100 := by
  apply branch_left_normalized (c:=vp000010010001000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-289761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-289761639/250000 : ℚ) by norm_num]
  exact coverp000010010001000
private noncomputable def ep000010010001001_0 : Blocks := edgeBlocks% "full/vectors/000010010001001-E-0000.bin"
noncomputable def ep000010010001001 : Blocks := ep000010010001001_0
private theorem idp000010010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000100.list =
    C ((2:ℤ)^51) * horner X vp000010010001001.list + horner X ep000010010001001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010001001 : Branch 1 (-289761639/500000 : ℚ) vp00001001000100 := by
  apply branch_checked idp000010010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-289761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-290011639/250000 : ℚ) by norm_num]
  exact coverp000010010001001
theorem coverp00001001000100 : Covers (-289761639/500000 : ℚ) vp00001001000100 := join_branches bp000010010001000 bp000010010001001
private noncomputable def vp0000100100010_0 : Blocks := edgeBlocks% "full/vectors/0000100100010-V-0000.bin"
noncomputable def vp0000100100010 : Blocks := vp0000100100010_0
private theorem bp00001001000100 : Branch 0 (-289761639/1000000 : ℚ) vp0000100100010 := by
  apply branch_left_normalized (c:=vp00001001000100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-289761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-289761639/500000 : ℚ) by norm_num]
  exact coverp00001001000100
private noncomputable def ep00001001000101_0 : Blocks := edgeBlocks% "full/vectors/00001001000101-E-0000.bin"
noncomputable def ep00001001000101 : Blocks := ep00001001000101_0
private theorem idp00001001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100010.list =
    C ((2:ℤ)^83) * horner X vp00001001000101.list + horner X ep00001001000101.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001000101 : Branch 1 (-289761639/1000000 : ℚ) vp0000100100010 := by
  apply branch_checked idp00001001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-289761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-290261639/500000 : ℚ) by norm_num]
  exact coverp00001001000101
theorem coverp0000100100010 : Covers (-289761639/1000000 : ℚ) vp0000100100010 := join_branches bp00001001000100 bp00001001000101
private noncomputable def vp000010010001_0 : Blocks := edgeBlocks% "full/vectors/000010010001-V-0000.bin"
private noncomputable def vp000010010001_1 : Blocks := edgeBlocks% "full/vectors/000010010001-V-0001.bin"
noncomputable def vp000010010001 : Blocks := (Blocks.join vp000010010001_0 vp000010010001_1)
private theorem bp0000100100010 : Branch 0 (-289761639/2000000 : ℚ) vp000010010001 := by
  apply branch_left_normalized (c:=vp0000100100010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-289761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-289761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100010
private noncomputable def ep0000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000100100011-E-0000.bin"
private noncomputable def ep0000100100011_1 : Blocks := edgeBlocks% "full/vectors/0000100100011-E-0001.bin"
noncomputable def ep0000100100011 : Blocks := (Blocks.join ep0000100100011_0 ep0000100100011_1)
private theorem idp0000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010001.list =
    C ((2:ℤ)^145) * horner X vp0000100100011.list + horner X ep0000100100011.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100100011 : Branch 1 (-289761639/2000000 : ℚ) vp000010010001 := by
  apply branch_checked idp0000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-289761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-290761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100011
theorem coverp000010010001 : Covers (-289761639/2000000 : ℚ) vp000010010001 := join_branches bp0000100100010 bp0000100100011
private noncomputable def vp000010010000111_0 : Blocks := edgeBlocks% "full/vectors/000010010000111-V-0000.bin"
noncomputable def vp000010010000111 : Blocks := vp000010010000111_0
theorem coverp000010010000111 : Covers (-289511639/250000 : ℚ) vp000010010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010000110_0 : Blocks := edgeBlocks% "full/vectors/000010010000110-V-0000.bin"
noncomputable def vp000010010000110 : Blocks := vp000010010000110_0
theorem coverp000010010000110 : Covers (-289261639/250000 : ℚ) vp000010010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000011_0 : Blocks := edgeBlocks% "full/vectors/00001001000011-V-0000.bin"
noncomputable def vp00001001000011 : Blocks := vp00001001000011_0
private theorem bp000010010000110 : Branch 0 (-289261639/500000 : ℚ) vp00001001000011 := by
  apply branch_left_normalized (c:=vp000010010000110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-289261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-289261639/250000 : ℚ) by norm_num]
  exact coverp000010010000110
private noncomputable def ep000010010000111_0 : Blocks := edgeBlocks% "full/vectors/000010010000111-E-0000.bin"
noncomputable def ep000010010000111 : Blocks := ep000010010000111_0
private theorem idp000010010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000011.list =
    C ((2:ℤ)^50) * horner X vp000010010000111.list + horner X ep000010010000111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010000111 : Branch 1 (-289261639/500000 : ℚ) vp00001001000011 := by
  apply branch_checked idp000010010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-289261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-289511639/250000 : ℚ) by norm_num]
  exact coverp000010010000111
theorem coverp00001001000011 : Covers (-289261639/500000 : ℚ) vp00001001000011 := join_branches bp000010010000110 bp000010010000111
private noncomputable def vp000010010000101_0 : Blocks := edgeBlocks% "full/vectors/000010010000101-V-0000.bin"
noncomputable def vp000010010000101 : Blocks := vp000010010000101_0
theorem coverp000010010000101 : Covers (-289011639/250000 : ℚ) vp000010010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010000100_0 : Blocks := edgeBlocks% "full/vectors/000010010000100-V-0000.bin"
noncomputable def vp000010010000100 : Blocks := vp000010010000100_0
theorem coverp000010010000100 : Covers (-288761639/250000 : ℚ) vp000010010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000010_0 : Blocks := edgeBlocks% "full/vectors/00001001000010-V-0000.bin"
noncomputable def vp00001001000010 : Blocks := vp00001001000010_0
private theorem bp000010010000100 : Branch 0 (-288761639/500000 : ℚ) vp00001001000010 := by
  apply branch_left_normalized (c:=vp000010010000100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-288761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-288761639/250000 : ℚ) by norm_num]
  exact coverp000010010000100
private noncomputable def ep000010010000101_0 : Blocks := edgeBlocks% "full/vectors/000010010000101-E-0000.bin"
noncomputable def ep000010010000101 : Blocks := ep000010010000101_0
private theorem idp000010010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000010.list =
    C ((2:ℤ)^50) * horner X vp000010010000101.list + horner X ep000010010000101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010000101 : Branch 1 (-288761639/500000 : ℚ) vp00001001000010 := by
  apply branch_checked idp000010010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-288761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-289011639/250000 : ℚ) by norm_num]
  exact coverp000010010000101
theorem coverp00001001000010 : Covers (-288761639/500000 : ℚ) vp00001001000010 := join_branches bp000010010000100 bp000010010000101
private noncomputable def vp0000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000100100001-V-0000.bin"
noncomputable def vp0000100100001 : Blocks := vp0000100100001_0
private theorem bp00001001000010 : Branch 0 (-288761639/1000000 : ℚ) vp0000100100001 := by
  apply branch_left_normalized (c:=vp00001001000010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-288761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-288761639/500000 : ℚ) by norm_num]
  exact coverp00001001000010
private noncomputable def ep00001001000011_0 : Blocks := edgeBlocks% "full/vectors/00001001000011-E-0000.bin"
noncomputable def ep00001001000011 : Blocks := ep00001001000011_0
private theorem idp00001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100001.list =
    C ((2:ℤ)^82) * horner X vp00001001000011.list + horner X ep00001001000011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001000011 : Branch 1 (-288761639/1000000 : ℚ) vp0000100100001 := by
  apply branch_checked idp00001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-288761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-289261639/500000 : ℚ) by norm_num]
  exact coverp00001001000011
theorem coverp0000100100001 : Covers (-288761639/1000000 : ℚ) vp0000100100001 := join_branches bp00001001000010 bp00001001000011
private noncomputable def vp000010010000011_0 : Blocks := edgeBlocks% "full/vectors/000010010000011-V-0000.bin"
noncomputable def vp000010010000011 : Blocks := vp000010010000011_0
theorem coverp000010010000011 : Covers (-288511639/250000 : ℚ) vp000010010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010000010_0 : Blocks := edgeBlocks% "full/vectors/000010010000010-V-0000.bin"
noncomputable def vp000010010000010 : Blocks := vp000010010000010_0
theorem coverp000010010000010 : Covers (-288261639/250000 : ℚ) vp000010010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000001_0 : Blocks := edgeBlocks% "full/vectors/00001001000001-V-0000.bin"
noncomputable def vp00001001000001 : Blocks := vp00001001000001_0
private theorem bp000010010000010 : Branch 0 (-288261639/500000 : ℚ) vp00001001000001 := by
  apply branch_left_normalized (c:=vp000010010000010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-288261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-288261639/250000 : ℚ) by norm_num]
  exact coverp000010010000010
private noncomputable def ep000010010000011_0 : Blocks := edgeBlocks% "full/vectors/000010010000011-E-0000.bin"
noncomputable def ep000010010000011 : Blocks := ep000010010000011_0
private theorem idp000010010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000001.list =
    C ((2:ℤ)^50) * horner X vp000010010000011.list + horner X ep000010010000011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010000011 : Branch 1 (-288261639/500000 : ℚ) vp00001001000001 := by
  apply branch_checked idp000010010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-288261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-288511639/250000 : ℚ) by norm_num]
  exact coverp000010010000011
theorem coverp00001001000001 : Covers (-288261639/500000 : ℚ) vp00001001000001 := join_branches bp000010010000010 bp000010010000011
private noncomputable def vp000010010000001_0 : Blocks := edgeBlocks% "full/vectors/000010010000001-V-0000.bin"
noncomputable def vp000010010000001 : Blocks := vp000010010000001_0
theorem coverp000010010000001 : Covers (-288011639/250000 : ℚ) vp000010010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010010000000_0 : Blocks := edgeBlocks% "full/vectors/000010010000000-V-0000.bin"
noncomputable def vp000010010000000 : Blocks := vp000010010000000_0
theorem coverp000010010000000 : Covers (-287761639/250000 : ℚ) vp000010010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001001000000_0 : Blocks := edgeBlocks% "full/vectors/00001001000000-V-0000.bin"
noncomputable def vp00001001000000 : Blocks := vp00001001000000_0
private theorem bp000010010000000 : Branch 0 (-287761639/500000 : ℚ) vp00001001000000 := by
  apply branch_left_normalized (c:=vp000010010000000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-287761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/250000 : ℚ) by norm_num]
  exact coverp000010010000000
private noncomputable def ep000010010000001_0 : Blocks := edgeBlocks% "full/vectors/000010010000001-E-0000.bin"
noncomputable def ep000010010000001 : Blocks := ep000010010000001_0
private theorem idp000010010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000000.list =
    C ((2:ℤ)^50) * horner X vp000010010000001.list + horner X ep000010010000001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010000001 : Branch 1 (-287761639/500000 : ℚ) vp00001001000000 := by
  apply branch_checked idp000010010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-288011639/250000 : ℚ) by norm_num]
  exact coverp000010010000001
theorem coverp00001001000000 : Covers (-287761639/500000 : ℚ) vp00001001000000 := join_branches bp000010010000000 bp000010010000001
private noncomputable def vp0000100100000_0 : Blocks := edgeBlocks% "full/vectors/0000100100000-V-0000.bin"
noncomputable def vp0000100100000 : Blocks := vp0000100100000_0
private theorem bp00001001000000 : Branch 0 (-287761639/1000000 : ℚ) vp0000100100000 := by
  apply branch_left_normalized (c:=vp00001001000000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-287761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/500000 : ℚ) by norm_num]
  exact coverp00001001000000
private noncomputable def ep00001001000001_0 : Blocks := edgeBlocks% "full/vectors/00001001000001-E-0000.bin"
noncomputable def ep00001001000001 : Blocks := ep00001001000001_0
private theorem idp00001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100000.list =
    C ((2:ℤ)^83) * horner X vp00001001000001.list + horner X ep00001001000001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001000001 : Branch 1 (-287761639/1000000 : ℚ) vp0000100100000 := by
  apply branch_checked idp00001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-288261639/500000 : ℚ) by norm_num]
  exact coverp00001001000001
theorem coverp0000100100000 : Covers (-287761639/1000000 : ℚ) vp0000100100000 := join_branches bp00001001000000 bp00001001000001
private noncomputable def vp000010010000_0 : Blocks := edgeBlocks% "full/vectors/000010010000-V-0000.bin"
private noncomputable def vp000010010000_1 : Blocks := edgeBlocks% "full/vectors/000010010000-V-0001.bin"
noncomputable def vp000010010000 : Blocks := (Blocks.join vp000010010000_0 vp000010010000_1)
private theorem bp0000100100000 : Branch 0 (-287761639/2000000 : ℚ) vp000010010000 := by
  apply branch_left_normalized (c:=vp0000100100000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-287761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100000
private noncomputable def ep0000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000100100001-E-0000.bin"
private noncomputable def ep0000100100001_1 : Blocks := edgeBlocks% "full/vectors/0000100100001-E-0001.bin"
noncomputable def ep0000100100001 : Blocks := (Blocks.join ep0000100100001_0 ep0000100100001_1)
private theorem idp0000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010000.list =
    C ((2:ℤ)^145) * horner X vp0000100100001.list + horner X ep0000100100001.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100100001 : Branch 1 (-287761639/2000000 : ℚ) vp000010010000 := by
  apply branch_checked idp0000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-288761639/1000000 : ℚ) by norm_num]
  exact coverp0000100100001
theorem coverp000010010000 : Covers (-287761639/2000000 : ℚ) vp000010010000 := join_branches bp0000100100000 bp0000100100001
private noncomputable def vp00001001000_0 : Blocks := edgeBlocks% "full/vectors/00001001000-V-0000.bin"
private noncomputable def vp00001001000_1 : Blocks := edgeBlocks% "full/vectors/00001001000-V-0001.bin"
noncomputable def vp00001001000 : Blocks := (Blocks.join vp00001001000_0 vp00001001000_1)
private theorem bp000010010000 : Branch 0 (-287761639/4000000 : ℚ) vp00001001000 := by
  apply branch_left_normalized (c:=vp000010010000) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-287761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/2000000 : ℚ) by norm_num]
  exact coverp000010010000
private noncomputable def ep000010010001_0 : Blocks := edgeBlocks% "full/vectors/000010010001-E-0000.bin"
private noncomputable def ep000010010001_1 : Blocks := edgeBlocks% "full/vectors/000010010001-E-0001.bin"
noncomputable def ep000010010001 : Blocks := (Blocks.join ep000010010001_0 ep000010010001_1)
private theorem idp000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001000.list =
    C ((2:ℤ)^266) * horner X vp000010010001.list + horner X ep000010010001.list := by
  exact edge_identity (B := (2:ℤ)^480) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010010001 : Branch 1 (-287761639/4000000 : ℚ) vp00001001000 := by
  apply branch_checked idp000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-289761639/2000000 : ℚ) by norm_num]
  exact coverp000010010001
theorem coverp00001001000 : Covers (-287761639/4000000 : ℚ) vp00001001000 := join_branches bp000010010000 bp000010010001
private noncomputable def vp0000100100_0 : Blocks := edgeBlocks% "full/vectors/0000100100-V-0000.bin"
private noncomputable def vp0000100100_1 : Blocks := edgeBlocks% "full/vectors/0000100100-V-0001.bin"
private noncomputable def vp0000100100_2 : Blocks := edgeBlocks% "full/vectors/0000100100-V-0002.bin"
private noncomputable def vp0000100100_3 : Blocks := edgeBlocks% "full/vectors/0000100100-V-0003.bin"
noncomputable def vp0000100100 : Blocks := (Blocks.join (Blocks.join vp0000100100_0 vp0000100100_1) (Blocks.join vp0000100100_2 vp0000100100_3))
private theorem bp00001001000 : Branch 0 (-287761639/8000000 : ℚ) vp0000100100 := by
  apply branch_left_normalized (c:=vp00001001000) (k:=0) (m:=254) (by decide +kernel)
  rw [show 2*(-287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/4000000 : ℚ) by norm_num]
  exact coverp00001001000
private noncomputable def ep00001001001_0 : Blocks := edgeBlocks% "full/vectors/00001001001-E-0000.bin"
private noncomputable def ep00001001001_1 : Blocks := edgeBlocks% "full/vectors/00001001001-E-0001.bin"
private noncomputable def ep00001001001_2 : Blocks := edgeBlocks% "full/vectors/00001001001-E-0002.bin"
private noncomputable def ep00001001001_3 : Blocks := edgeBlocks% "full/vectors/00001001001-E-0003.bin"
noncomputable def ep00001001001 : Blocks := (Blocks.join (Blocks.join ep00001001001_0 ep00001001001_1) (Blocks.join ep00001001001_2 ep00001001001_3))
private theorem idp00001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100100.list =
    C ((2:ℤ)^508) * horner X vp00001001001.list + horner X ep00001001001.list := by
  exact edge_identity (B := (2:ℤ)^833) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001001001 : Branch 1 (-287761639/8000000 : ℚ) vp0000100100 := by
  apply branch_checked idp00001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-291761639/4000000 : ℚ) by norm_num]
  exact coverp00001001001
theorem coverp0000100100 : Covers (-287761639/8000000 : ℚ) vp0000100100 := join_branches bp00001001000 bp00001001001
private noncomputable def vp000010010_0 : Blocks := edgeBlocks% "full/vectors/000010010-V-0000.bin"
private noncomputable def vp000010010_1 : Blocks := edgeBlocks% "full/vectors/000010010-V-0001.bin"
private noncomputable def vp000010010_2 : Blocks := edgeBlocks% "full/vectors/000010010-V-0002.bin"
private noncomputable def vp000010010_3 : Blocks := edgeBlocks% "full/vectors/000010010-V-0003.bin"
private noncomputable def vp000010010_4 : Blocks := edgeBlocks% "full/vectors/000010010-V-0004.bin"
private noncomputable def vp000010010_5 : Blocks := edgeBlocks% "full/vectors/000010010-V-0005.bin"
private noncomputable def vp000010010_6 : Blocks := edgeBlocks% "full/vectors/000010010-V-0006.bin"
private noncomputable def vp000010010_7 : Blocks := edgeBlocks% "full/vectors/000010010-V-0007.bin"
noncomputable def vp000010010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000010010_0 vp000010010_1) (Blocks.join vp000010010_2 vp000010010_3)) (Blocks.join (Blocks.join vp000010010_4 vp000010010_5) (Blocks.join vp000010010_6 vp000010010_7)))
private theorem bp0000100100 : Branch 0 (-287761639/16000000 : ℚ) vp000010010 := by
  apply branch_left_normalized (c:=vp0000100100) (k:=0) (m:=484) (by decide +kernel)
  rw [show 2*(-287761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/8000000 : ℚ) by norm_num]
  exact coverp0000100100
private noncomputable def ep0000100101_0 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0000.bin"
private noncomputable def ep0000100101_1 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0001.bin"
private noncomputable def ep0000100101_2 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0002.bin"
private noncomputable def ep0000100101_3 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0003.bin"
private noncomputable def ep0000100101_4 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0004.bin"
private noncomputable def ep0000100101_5 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0005.bin"
private noncomputable def ep0000100101_6 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0006.bin"
private noncomputable def ep0000100101_7 : Blocks := edgeBlocks% "full/vectors/0000100101-E-0007.bin"
noncomputable def ep0000100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000100101_0 ep0000100101_1) (Blocks.join ep0000100101_2 ep0000100101_3)) (Blocks.join (Blocks.join ep0000100101_4 ep0000100101_5) (Blocks.join ep0000100101_6 ep0000100101_7)))
private theorem idp0000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010010.list =
    C ((2:ℤ)^985) * horner X vp0000100101.list + horner X ep0000100101.list := by
  exact edge_identity (B := (2:ℤ)^1531) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100101 : Branch 1 (-287761639/16000000 : ℚ) vp000010010 := by
  apply branch_checked idp0000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-295761639/8000000 : ℚ) by norm_num]
  exact coverp0000100101
theorem coverp000010010 : Covers (-287761639/16000000 : ℚ) vp000010010 := join_branches bp0000100100 bp0000100101
private noncomputable def vp00001001_0 : Blocks := edgeBlocks% "full/vectors/00001001-V-0000.bin"
private noncomputable def vp00001001_1 : Blocks := edgeBlocks% "full/vectors/00001001-V-0001.bin"
private noncomputable def vp00001001_2 : Blocks := edgeBlocks% "full/vectors/00001001-V-0002.bin"
private noncomputable def vp00001001_3 : Blocks := edgeBlocks% "full/vectors/00001001-V-0003.bin"
private noncomputable def vp00001001_4 : Blocks := edgeBlocks% "full/vectors/00001001-V-0004.bin"
private noncomputable def vp00001001_5 : Blocks := edgeBlocks% "full/vectors/00001001-V-0005.bin"
private noncomputable def vp00001001_6 : Blocks := edgeBlocks% "full/vectors/00001001-V-0006.bin"
private noncomputable def vp00001001_7 : Blocks := edgeBlocks% "full/vectors/00001001-V-0007.bin"
private noncomputable def vp00001001_8 : Blocks := edgeBlocks% "full/vectors/00001001-V-0008.bin"
private noncomputable def vp00001001_9 : Blocks := edgeBlocks% "full/vectors/00001001-V-0009.bin"
private noncomputable def vp00001001_10 : Blocks := edgeBlocks% "full/vectors/00001001-V-0010.bin"
private noncomputable def vp00001001_11 : Blocks := edgeBlocks% "full/vectors/00001001-V-0011.bin"
private noncomputable def vp00001001_12 : Blocks := edgeBlocks% "full/vectors/00001001-V-0012.bin"
private noncomputable def vp00001001_13 : Blocks := edgeBlocks% "full/vectors/00001001-V-0013.bin"
private noncomputable def vp00001001_14 : Blocks := edgeBlocks% "full/vectors/00001001-V-0014.bin"
noncomputable def vp00001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001001_0 (Blocks.join vp00001001_1 vp00001001_2)) (Blocks.join (Blocks.join vp00001001_3 vp00001001_4) (Blocks.join vp00001001_5 vp00001001_6))) (Blocks.join (Blocks.join (Blocks.join vp00001001_7 vp00001001_8) (Blocks.join vp00001001_9 vp00001001_10)) (Blocks.join (Blocks.join vp00001001_11 vp00001001_12) (Blocks.join vp00001001_13 vp00001001_14))))
private theorem bp000010010 : Branch 0 (-287761639/32000000 : ℚ) vp00001001 := by
  apply branch_left_normalized (c:=vp000010010) (k:=0) (m:=938) (by decide +kernel)
  rw [show 2*(-287761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-287761639/16000000 : ℚ) by norm_num]
  exact coverp000010010
private noncomputable def ep000010011_0 : Blocks := edgeBlocks% "full/vectors/000010011-E-0000.bin"
private noncomputable def ep000010011_1 : Blocks := edgeBlocks% "full/vectors/000010011-E-0001.bin"
private noncomputable def ep000010011_2 : Blocks := edgeBlocks% "full/vectors/000010011-E-0002.bin"
private noncomputable def ep000010011_3 : Blocks := edgeBlocks% "full/vectors/000010011-E-0003.bin"
private noncomputable def ep000010011_4 : Blocks := edgeBlocks% "full/vectors/000010011-E-0004.bin"
private noncomputable def ep000010011_5 : Blocks := edgeBlocks% "full/vectors/000010011-E-0005.bin"
private noncomputable def ep000010011_6 : Blocks := edgeBlocks% "full/vectors/000010011-E-0006.bin"
private noncomputable def ep000010011_7 : Blocks := edgeBlocks% "full/vectors/000010011-E-0007.bin"
private noncomputable def ep000010011_8 : Blocks := edgeBlocks% "full/vectors/000010011-E-0008.bin"
private noncomputable def ep000010011_9 : Blocks := edgeBlocks% "full/vectors/000010011-E-0009.bin"
private noncomputable def ep000010011_10 : Blocks := edgeBlocks% "full/vectors/000010011-E-0010.bin"
private noncomputable def ep000010011_11 : Blocks := edgeBlocks% "full/vectors/000010011-E-0011.bin"
private noncomputable def ep000010011_12 : Blocks := edgeBlocks% "full/vectors/000010011-E-0012.bin"
private noncomputable def ep000010011_13 : Blocks := edgeBlocks% "full/vectors/000010011-E-0013.bin"
private noncomputable def ep000010011_14 : Blocks := edgeBlocks% "full/vectors/000010011-E-0014.bin"
noncomputable def ep000010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000010011_0 (Blocks.join ep000010011_1 ep000010011_2)) (Blocks.join (Blocks.join ep000010011_3 ep000010011_4) (Blocks.join ep000010011_5 ep000010011_6))) (Blocks.join (Blocks.join (Blocks.join ep000010011_7 ep000010011_8) (Blocks.join ep000010011_9 ep000010011_10)) (Blocks.join (Blocks.join ep000010011_11 ep000010011_12) (Blocks.join ep000010011_13 ep000010011_14))))
private theorem idp000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001001.list =
    C ((2:ℤ)^1926) * horner X vp000010011.list + horner X ep000010011.list := by
  exact edge_identity (B := (2:ℤ)^2903) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010011 : Branch 1 (-287761639/32000000 : ℚ) vp00001001 := by
  apply branch_checked idp000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-287761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-303761639/16000000 : ℚ) by norm_num]
  exact coverp000010011
theorem coverp00001001 : Covers (-287761639/32000000 : ℚ) vp00001001 := join_branches bp000010010 bp000010011
private noncomputable def vp0000100_0 : Blocks := edgeBlocks% "full/vectors/0000100-V-0000.bin"
private noncomputable def vp0000100_1 : Blocks := edgeBlocks% "full/vectors/0000100-V-0001.bin"
private noncomputable def vp0000100_2 : Blocks := edgeBlocks% "full/vectors/0000100-V-0002.bin"
private noncomputable def vp0000100_3 : Blocks := edgeBlocks% "full/vectors/0000100-V-0003.bin"
private noncomputable def vp0000100_4 : Blocks := edgeBlocks% "full/vectors/0000100-V-0004.bin"
private noncomputable def vp0000100_5 : Blocks := edgeBlocks% "full/vectors/0000100-V-0005.bin"
private noncomputable def vp0000100_6 : Blocks := edgeBlocks% "full/vectors/0000100-V-0006.bin"
private noncomputable def vp0000100_7 : Blocks := edgeBlocks% "full/vectors/0000100-V-0007.bin"
private noncomputable def vp0000100_8 : Blocks := edgeBlocks% "full/vectors/0000100-V-0008.bin"
private noncomputable def vp0000100_9 : Blocks := edgeBlocks% "full/vectors/0000100-V-0009.bin"
private noncomputable def vp0000100_10 : Blocks := edgeBlocks% "full/vectors/0000100-V-0010.bin"
private noncomputable def vp0000100_11 : Blocks := edgeBlocks% "full/vectors/0000100-V-0011.bin"
private noncomputable def vp0000100_12 : Blocks := edgeBlocks% "full/vectors/0000100-V-0012.bin"
private noncomputable def vp0000100_13 : Blocks := edgeBlocks% "full/vectors/0000100-V-0013.bin"
private noncomputable def vp0000100_14 : Blocks := edgeBlocks% "full/vectors/0000100-V-0014.bin"
private noncomputable def vp0000100_15 : Blocks := edgeBlocks% "full/vectors/0000100-V-0015.bin"
private noncomputable def vp0000100_16 : Blocks := edgeBlocks% "full/vectors/0000100-V-0016.bin"
private noncomputable def vp0000100_17 : Blocks := edgeBlocks% "full/vectors/0000100-V-0017.bin"
private noncomputable def vp0000100_18 : Blocks := edgeBlocks% "full/vectors/0000100-V-0018.bin"
private noncomputable def vp0000100_19 : Blocks := edgeBlocks% "full/vectors/0000100-V-0019.bin"
private noncomputable def vp0000100_20 : Blocks := edgeBlocks% "full/vectors/0000100-V-0020.bin"
private noncomputable def vp0000100_21 : Blocks := edgeBlocks% "full/vectors/0000100-V-0021.bin"
private noncomputable def vp0000100_22 : Blocks := edgeBlocks% "full/vectors/0000100-V-0022.bin"
private noncomputable def vp0000100_23 : Blocks := edgeBlocks% "full/vectors/0000100-V-0023.bin"
private noncomputable def vp0000100_24 : Blocks := edgeBlocks% "full/vectors/0000100-V-0024.bin"
private noncomputable def vp0000100_25 : Blocks := edgeBlocks% "full/vectors/0000100-V-0025.bin"
private noncomputable def vp0000100_26 : Blocks := edgeBlocks% "full/vectors/0000100-V-0026.bin"
private noncomputable def vp0000100_27 : Blocks := edgeBlocks% "full/vectors/0000100-V-0027.bin"
private noncomputable def vp0000100_28 : Blocks := edgeBlocks% "full/vectors/0000100-V-0028.bin"
private noncomputable def vp0000100_29 : Blocks := edgeBlocks% "full/vectors/0000100-V-0029.bin"
noncomputable def vp0000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000100_0 (Blocks.join vp0000100_1 vp0000100_2)) (Blocks.join (Blocks.join vp0000100_3 vp0000100_4) (Blocks.join vp0000100_5 vp0000100_6))) (Blocks.join (Blocks.join (Blocks.join vp0000100_7 vp0000100_8) (Blocks.join vp0000100_9 vp0000100_10)) (Blocks.join (Blocks.join vp0000100_11 vp0000100_12) (Blocks.join vp0000100_13 vp0000100_14)))) (Blocks.join (Blocks.join (Blocks.join vp0000100_15 (Blocks.join vp0000100_16 vp0000100_17)) (Blocks.join (Blocks.join vp0000100_18 vp0000100_19) (Blocks.join vp0000100_20 vp0000100_21))) (Blocks.join (Blocks.join (Blocks.join vp0000100_22 vp0000100_23) (Blocks.join vp0000100_24 vp0000100_25)) (Blocks.join (Blocks.join vp0000100_26 vp0000100_27) (Blocks.join vp0000100_28 vp0000100_29)))))
private theorem bp00001000 : Branch 0 (-255761639/64000000 : ℚ) vp0000100 := by
  apply branch_left_normalized (c:=vp00001000) (k:=0) (m:=1924) (by decide +kernel)
  rw [show 2*(-255761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/32000000 : ℚ) by norm_num]
  exact coverp00001000
private noncomputable def ep00001001_0 : Blocks := edgeBlocks% "full/vectors/00001001-E-0000.bin"
private noncomputable def ep00001001_1 : Blocks := edgeBlocks% "full/vectors/00001001-E-0001.bin"
private noncomputable def ep00001001_2 : Blocks := edgeBlocks% "full/vectors/00001001-E-0002.bin"
private noncomputable def ep00001001_3 : Blocks := edgeBlocks% "full/vectors/00001001-E-0003.bin"
private noncomputable def ep00001001_4 : Blocks := edgeBlocks% "full/vectors/00001001-E-0004.bin"
private noncomputable def ep00001001_5 : Blocks := edgeBlocks% "full/vectors/00001001-E-0005.bin"
private noncomputable def ep00001001_6 : Blocks := edgeBlocks% "full/vectors/00001001-E-0006.bin"
private noncomputable def ep00001001_7 : Blocks := edgeBlocks% "full/vectors/00001001-E-0007.bin"
private noncomputable def ep00001001_8 : Blocks := edgeBlocks% "full/vectors/00001001-E-0008.bin"
private noncomputable def ep00001001_9 : Blocks := edgeBlocks% "full/vectors/00001001-E-0009.bin"
private noncomputable def ep00001001_10 : Blocks := edgeBlocks% "full/vectors/00001001-E-0010.bin"
private noncomputable def ep00001001_11 : Blocks := edgeBlocks% "full/vectors/00001001-E-0011.bin"
private noncomputable def ep00001001_12 : Blocks := edgeBlocks% "full/vectors/00001001-E-0012.bin"
private noncomputable def ep00001001_13 : Blocks := edgeBlocks% "full/vectors/00001001-E-0013.bin"
private noncomputable def ep00001001_14 : Blocks := edgeBlocks% "full/vectors/00001001-E-0014.bin"
private noncomputable def ep00001001_15 : Blocks := edgeBlocks% "full/vectors/00001001-E-0015.bin"
private noncomputable def ep00001001_16 : Blocks := edgeBlocks% "full/vectors/00001001-E-0016.bin"
private noncomputable def ep00001001_17 : Blocks := edgeBlocks% "full/vectors/00001001-E-0017.bin"
private noncomputable def ep00001001_18 : Blocks := edgeBlocks% "full/vectors/00001001-E-0018.bin"
private noncomputable def ep00001001_19 : Blocks := edgeBlocks% "full/vectors/00001001-E-0019.bin"
private noncomputable def ep00001001_20 : Blocks := edgeBlocks% "full/vectors/00001001-E-0020.bin"
private noncomputable def ep00001001_21 : Blocks := edgeBlocks% "full/vectors/00001001-E-0021.bin"
private noncomputable def ep00001001_22 : Blocks := edgeBlocks% "full/vectors/00001001-E-0022.bin"
private noncomputable def ep00001001_23 : Blocks := edgeBlocks% "full/vectors/00001001-E-0023.bin"
private noncomputable def ep00001001_24 : Blocks := edgeBlocks% "full/vectors/00001001-E-0024.bin"
private noncomputable def ep00001001_25 : Blocks := edgeBlocks% "full/vectors/00001001-E-0025.bin"
private noncomputable def ep00001001_26 : Blocks := edgeBlocks% "full/vectors/00001001-E-0026.bin"
private noncomputable def ep00001001_27 : Blocks := edgeBlocks% "full/vectors/00001001-E-0027.bin"
private noncomputable def ep00001001_28 : Blocks := edgeBlocks% "full/vectors/00001001-E-0028.bin"
private noncomputable def ep00001001_29 : Blocks := edgeBlocks% "full/vectors/00001001-E-0029.bin"
noncomputable def ep00001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00001001_0 (Blocks.join ep00001001_1 ep00001001_2)) (Blocks.join (Blocks.join ep00001001_3 ep00001001_4) (Blocks.join ep00001001_5 ep00001001_6))) (Blocks.join (Blocks.join (Blocks.join ep00001001_7 ep00001001_8) (Blocks.join ep00001001_9 ep00001001_10)) (Blocks.join (Blocks.join ep00001001_11 ep00001001_12) (Blocks.join ep00001001_13 ep00001001_14)))) (Blocks.join (Blocks.join (Blocks.join ep00001001_15 (Blocks.join ep00001001_16 ep00001001_17)) (Blocks.join (Blocks.join ep00001001_18 ep00001001_19) (Blocks.join ep00001001_20 ep00001001_21))) (Blocks.join (Blocks.join (Blocks.join ep00001001_22 ep00001001_23) (Blocks.join ep00001001_24 ep00001001_25)) (Blocks.join (Blocks.join ep00001001_26 ep00001001_27) (Blocks.join ep00001001_28 ep00001001_29)))))
private def ptsp00001001 : List ℤ := [((2:ℤ)^3228+0),((2:ℤ)^3228+1)]
private theorem boundp00001001 : 2^vp0000100.size*absSum vp0000100.list + ((2:ℤ)^3890*absSum vp00001001.list+absSum ep00001001.list) < (2:ℤ)^5851 := by decide +kernel
private theorem pointp00001001_0 : fastHom 1 ((2:ℤ)^3228+0) vp0000100 = ((2:ℤ)^3890)*vp00001001.subst ((2:ℤ)^3228+0)+ep00001001.subst ((2:ℤ)^3228+0) := by decide +kernel
private theorem pointp00001001_1 : fastHom 1 ((2:ℤ)^3228+1) vp0000100 = ((2:ℤ)^3890)*vp00001001.subst ((2:ℤ)^3228+1)+ep00001001.subst ((2:ℤ)^3228+1) := by decide +kernel
private theorem checkp00001001 (x:ℤ) (hx:x ∈ ptsp00001001) : fastHom 1 x vp0000100 = ((2:ℤ)^3890)*vp00001001.subst x+ep00001001.subst x := by
  simp only [ptsp00001001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp00001001_0
  · exact pointp00001001_1
private theorem idp00001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100.list =
    C ((2:ℤ)^3890) * horner X vp00001001.list + horner X ep00001001.list := by
  apply edge_identity (B := (2:ℤ)^5851) (by decide) (by positivity) (by positivity) boundp00001001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00001001 (by decide +kernel)
  · have h : ptsp00001001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00001001.trans_le (by decide +kernel)
  · exact checkp00001001
private theorem bp00001001 : Branch 1 (-255761639/64000000 : ℚ) vp0000100 := by
  apply branch_checked idp00001001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-287761639/32000000 : ℚ) by norm_num]
  exact coverp00001001
theorem coverp0000100 : Covers (-255761639/64000000 : ℚ) vp0000100 := join_branches bp00001000 bp00001001
end NextProof.EdgeFull

