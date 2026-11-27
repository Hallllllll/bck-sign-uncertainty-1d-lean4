import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00072

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001011011111_0 : Blocks := edgeBlocks% "full/vectors/0001011011111-V-0000.bin"
noncomputable def vp0001011011111 : Blocks := vp0001011011111_0
theorem coverp0001011011111 : Covers (-734761639/1000000 : ℚ) vp0001011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011011110_0 : Blocks := edgeBlocks% "full/vectors/0001011011110-V-0000.bin"
noncomputable def vp0001011011110 : Blocks := vp0001011011110_0
theorem coverp0001011011110 : Covers (-733761639/1000000 : ℚ) vp0001011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101101111_0 : Blocks := edgeBlocks% "full/vectors/000101101111-V-0000.bin"
noncomputable def vp000101101111 : Blocks := vp000101101111_0
private theorem bp0001011011110 : Branch 0 (-733761639/2000000 : ℚ) vp000101101111 := by
  apply branch_left_normalized (c:=vp0001011011110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-733761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-733761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011110
private noncomputable def ep0001011011111_0 : Blocks := edgeBlocks% "full/vectors/0001011011111-E-0000.bin"
noncomputable def ep0001011011111 : Blocks := ep0001011011111_0
private theorem idp0001011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101111.list =
    C ((2:ℤ)^99) * horner X vp0001011011111.list + horner X ep0001011011111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011011111 : Branch 1 (-733761639/2000000 : ℚ) vp000101101111 := by
  apply branch_checked idp0001011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-733761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-734761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011111
theorem coverp000101101111 : Covers (-733761639/2000000 : ℚ) vp000101101111 := join_branches bp0001011011110 bp0001011011111
private noncomputable def vp0001011011101_0 : Blocks := edgeBlocks% "full/vectors/0001011011101-V-0000.bin"
noncomputable def vp0001011011101 : Blocks := vp0001011011101_0
theorem coverp0001011011101 : Covers (-732761639/1000000 : ℚ) vp0001011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110111001_0 : Blocks := edgeBlocks% "full/vectors/00010110111001-V-0000.bin"
noncomputable def vp00010110111001 : Blocks := vp00010110111001_0
theorem coverp00010110111001 : Covers (-732261639/500000 : ℚ) vp00010110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110111000_0 : Blocks := edgeBlocks% "full/vectors/00010110111000-V-0000.bin"
noncomputable def vp00010110111000 : Blocks := vp00010110111000_0
theorem coverp00010110111000 : Covers (-731761639/500000 : ℚ) vp00010110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011011100_0 : Blocks := edgeBlocks% "full/vectors/0001011011100-V-0000.bin"
noncomputable def vp0001011011100 : Blocks := vp0001011011100_0
private theorem bp00010110111000 : Branch 0 (-731761639/1000000 : ℚ) vp0001011011100 := by
  apply branch_left_normalized (c:=vp00010110111000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-731761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-731761639/500000 : ℚ) by norm_num]
  exact coverp00010110111000
private noncomputable def ep00010110111001_0 : Blocks := edgeBlocks% "full/vectors/00010110111001-E-0000.bin"
noncomputable def ep00010110111001 : Blocks := ep00010110111001_0
private theorem idp00010110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011011100.list =
    C ((2:ℤ)^59) * horner X vp00010110111001.list + horner X ep00010110111001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110111001 : Branch 1 (-731761639/1000000 : ℚ) vp0001011011100 := by
  apply branch_checked idp00010110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-731761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-732261639/500000 : ℚ) by norm_num]
  exact coverp00010110111001
theorem coverp0001011011100 : Covers (-731761639/1000000 : ℚ) vp0001011011100 := join_branches bp00010110111000 bp00010110111001
private noncomputable def vp000101101110_0 : Blocks := edgeBlocks% "full/vectors/000101101110-V-0000.bin"
noncomputable def vp000101101110 : Blocks := vp000101101110_0
private theorem bp0001011011100 : Branch 0 (-731761639/2000000 : ℚ) vp000101101110 := by
  apply branch_left_normalized (c:=vp0001011011100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-731761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-731761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011100
private noncomputable def ep0001011011101_0 : Blocks := edgeBlocks% "full/vectors/0001011011101-E-0000.bin"
noncomputable def ep0001011011101 : Blocks := ep0001011011101_0
private theorem idp0001011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101110.list =
    C ((2:ℤ)^100) * horner X vp0001011011101.list + horner X ep0001011011101.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011011101 : Branch 1 (-731761639/2000000 : ℚ) vp000101101110 := by
  apply branch_checked idp0001011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-731761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-732761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011101
theorem coverp000101101110 : Covers (-731761639/2000000 : ℚ) vp000101101110 := join_branches bp0001011011100 bp0001011011101
private noncomputable def vp00010110111_0 : Blocks := edgeBlocks% "full/vectors/00010110111-V-0000.bin"
private noncomputable def vp00010110111_1 : Blocks := edgeBlocks% "full/vectors/00010110111-V-0001.bin"
noncomputable def vp00010110111 : Blocks := (Blocks.join vp00010110111_0 vp00010110111_1)
private theorem bp000101101110 : Branch 0 (-731761639/4000000 : ℚ) vp00010110111 := by
  apply branch_left_normalized (c:=vp000101101110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-731761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-731761639/2000000 : ℚ) by norm_num]
  exact coverp000101101110
private noncomputable def ep000101101111_0 : Blocks := edgeBlocks% "full/vectors/000101101111-E-0000.bin"
private noncomputable def ep000101101111_1 : Blocks := edgeBlocks% "full/vectors/000101101111-E-0001.bin"
noncomputable def ep000101101111 : Blocks := (Blocks.join ep000101101111_0 ep000101101111_1)
private theorem idp000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110111.list =
    C ((2:ℤ)^183) * horner X vp000101101111.list + horner X ep000101101111.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101101111 : Branch 1 (-731761639/4000000 : ℚ) vp00010110111 := by
  apply branch_checked idp000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-731761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-733761639/2000000 : ℚ) by norm_num]
  exact coverp000101101111
theorem coverp00010110111 : Covers (-731761639/4000000 : ℚ) vp00010110111 := join_branches bp000101101110 bp000101101111
private noncomputable def vp00010110110111_0 : Blocks := edgeBlocks% "full/vectors/00010110110111-V-0000.bin"
noncomputable def vp00010110110111 : Blocks := vp00010110110111_0
theorem coverp00010110110111 : Covers (-731261639/500000 : ℚ) vp00010110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110110110_0 : Blocks := edgeBlocks% "full/vectors/00010110110110-V-0000.bin"
noncomputable def vp00010110110110 : Blocks := vp00010110110110_0
theorem coverp00010110110110 : Covers (-730761639/500000 : ℚ) vp00010110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011011011_0 : Blocks := edgeBlocks% "full/vectors/0001011011011-V-0000.bin"
noncomputable def vp0001011011011 : Blocks := vp0001011011011_0
private theorem bp00010110110110 : Branch 0 (-730761639/1000000 : ℚ) vp0001011011011 := by
  apply branch_left_normalized (c:=vp00010110110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-730761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-730761639/500000 : ℚ) by norm_num]
  exact coverp00010110110110
private noncomputable def ep00010110110111_0 : Blocks := edgeBlocks% "full/vectors/00010110110111-E-0000.bin"
noncomputable def ep00010110110111 : Blocks := ep00010110110111_0
private theorem idp00010110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011011011.list =
    C ((2:ℤ)^57) * horner X vp00010110110111.list + horner X ep00010110110111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110110111 : Branch 1 (-730761639/1000000 : ℚ) vp0001011011011 := by
  apply branch_checked idp00010110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-730761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-731261639/500000 : ℚ) by norm_num]
  exact coverp00010110110111
theorem coverp0001011011011 : Covers (-730761639/1000000 : ℚ) vp0001011011011 := join_branches bp00010110110110 bp00010110110111
private noncomputable def vp00010110110101_0 : Blocks := edgeBlocks% "full/vectors/00010110110101-V-0000.bin"
noncomputable def vp00010110110101 : Blocks := vp00010110110101_0
theorem coverp00010110110101 : Covers (-730261639/500000 : ℚ) vp00010110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110110100_0 : Blocks := edgeBlocks% "full/vectors/00010110110100-V-0000.bin"
noncomputable def vp00010110110100 : Blocks := vp00010110110100_0
theorem coverp00010110110100 : Covers (-729761639/500000 : ℚ) vp00010110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011011010_0 : Blocks := edgeBlocks% "full/vectors/0001011011010-V-0000.bin"
noncomputable def vp0001011011010 : Blocks := vp0001011011010_0
private theorem bp00010110110100 : Branch 0 (-729761639/1000000 : ℚ) vp0001011011010 := by
  apply branch_left_normalized (c:=vp00010110110100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-729761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-729761639/500000 : ℚ) by norm_num]
  exact coverp00010110110100
private noncomputable def ep00010110110101_0 : Blocks := edgeBlocks% "full/vectors/00010110110101-E-0000.bin"
noncomputable def ep00010110110101 : Blocks := ep00010110110101_0
private theorem idp00010110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011011010.list =
    C ((2:ℤ)^58) * horner X vp00010110110101.list + horner X ep00010110110101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110110101 : Branch 1 (-729761639/1000000 : ℚ) vp0001011011010 := by
  apply branch_checked idp00010110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-729761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-730261639/500000 : ℚ) by norm_num]
  exact coverp00010110110101
theorem coverp0001011011010 : Covers (-729761639/1000000 : ℚ) vp0001011011010 := join_branches bp00010110110100 bp00010110110101
private noncomputable def vp000101101101_0 : Blocks := edgeBlocks% "full/vectors/000101101101-V-0000.bin"
noncomputable def vp000101101101 : Blocks := vp000101101101_0
private theorem bp0001011011010 : Branch 0 (-729761639/2000000 : ℚ) vp000101101101 := by
  apply branch_left_normalized (c:=vp0001011011010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-729761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-729761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011010
private noncomputable def ep0001011011011_0 : Blocks := edgeBlocks% "full/vectors/0001011011011-E-0000.bin"
noncomputable def ep0001011011011 : Blocks := ep0001011011011_0
private theorem idp0001011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101101.list =
    C ((2:ℤ)^100) * horner X vp0001011011011.list + horner X ep0001011011011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011011011 : Branch 1 (-729761639/2000000 : ℚ) vp000101101101 := by
  apply branch_checked idp0001011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-729761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-730761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011011
theorem coverp000101101101 : Covers (-729761639/2000000 : ℚ) vp000101101101 := join_branches bp0001011011010 bp0001011011011
private noncomputable def vp0001011011001_0 : Blocks := edgeBlocks% "full/vectors/0001011011001-V-0000.bin"
noncomputable def vp0001011011001 : Blocks := vp0001011011001_0
theorem coverp0001011011001 : Covers (-728761639/1000000 : ℚ) vp0001011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011011000_0 : Blocks := edgeBlocks% "full/vectors/0001011011000-V-0000.bin"
noncomputable def vp0001011011000 : Blocks := vp0001011011000_0
theorem coverp0001011011000 : Covers (-727761639/1000000 : ℚ) vp0001011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101101100_0 : Blocks := edgeBlocks% "full/vectors/000101101100-V-0000.bin"
noncomputable def vp000101101100 : Blocks := vp000101101100_0
private theorem bp0001011011000 : Branch 0 (-727761639/2000000 : ℚ) vp000101101100 := by
  apply branch_left_normalized (c:=vp0001011011000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-727761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-727761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011000
private noncomputable def ep0001011011001_0 : Blocks := edgeBlocks% "full/vectors/0001011011001-E-0000.bin"
noncomputable def ep0001011011001 : Blocks := ep0001011011001_0
private theorem idp0001011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101100.list =
    C ((2:ℤ)^100) * horner X vp0001011011001.list + horner X ep0001011011001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011011001 : Branch 1 (-727761639/2000000 : ℚ) vp000101101100 := by
  apply branch_checked idp0001011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-727761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-728761639/1000000 : ℚ) by norm_num]
  exact coverp0001011011001
theorem coverp000101101100 : Covers (-727761639/2000000 : ℚ) vp000101101100 := join_branches bp0001011011000 bp0001011011001
private noncomputable def vp00010110110_0 : Blocks := edgeBlocks% "full/vectors/00010110110-V-0000.bin"
private noncomputable def vp00010110110_1 : Blocks := edgeBlocks% "full/vectors/00010110110-V-0001.bin"
noncomputable def vp00010110110 : Blocks := (Blocks.join vp00010110110_0 vp00010110110_1)
private theorem bp000101101100 : Branch 0 (-727761639/4000000 : ℚ) vp00010110110 := by
  apply branch_left_normalized (c:=vp000101101100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-727761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-727761639/2000000 : ℚ) by norm_num]
  exact coverp000101101100
private noncomputable def ep000101101101_0 : Blocks := edgeBlocks% "full/vectors/000101101101-E-0000.bin"
private noncomputable def ep000101101101_1 : Blocks := edgeBlocks% "full/vectors/000101101101-E-0001.bin"
noncomputable def ep000101101101 : Blocks := (Blocks.join ep000101101101_0 ep000101101101_1)
private theorem idp000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110110.list =
    C ((2:ℤ)^180) * horner X vp000101101101.list + horner X ep000101101101.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101101101 : Branch 1 (-727761639/4000000 : ℚ) vp00010110110 := by
  apply branch_checked idp000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-727761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-729761639/2000000 : ℚ) by norm_num]
  exact coverp000101101101
theorem coverp00010110110 : Covers (-727761639/4000000 : ℚ) vp00010110110 := join_branches bp000101101100 bp000101101101
private noncomputable def vp0001011011_0 : Blocks := edgeBlocks% "full/vectors/0001011011-V-0000.bin"
private noncomputable def vp0001011011_1 : Blocks := edgeBlocks% "full/vectors/0001011011-V-0001.bin"
private noncomputable def vp0001011011_2 : Blocks := edgeBlocks% "full/vectors/0001011011-V-0002.bin"
noncomputable def vp0001011011 : Blocks := (Blocks.join vp0001011011_0 (Blocks.join vp0001011011_1 vp0001011011_2))
private theorem bp00010110110 : Branch 0 (-727761639/8000000 : ℚ) vp0001011011 := by
  apply branch_left_normalized (c:=vp00010110110) (k:=0) (m:=167) (by decide +kernel)
  rw [show 2*(-727761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-727761639/4000000 : ℚ) by norm_num]
  exact coverp00010110110
private noncomputable def ep00010110111_0 : Blocks := edgeBlocks% "full/vectors/00010110111-E-0000.bin"
private noncomputable def ep00010110111_1 : Blocks := edgeBlocks% "full/vectors/00010110111-E-0001.bin"
private noncomputable def ep00010110111_2 : Blocks := edgeBlocks% "full/vectors/00010110111-E-0002.bin"
noncomputable def ep00010110111 : Blocks := (Blocks.join ep00010110111_0 (Blocks.join ep00010110111_1 ep00010110111_2))
private theorem idp00010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011011.list =
    C ((2:ℤ)^335) * horner X vp00010110111.list + horner X ep00010110111.list := by
  exact edge_identity (B := (2:ℤ)^567) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110111 : Branch 1 (-727761639/8000000 : ℚ) vp0001011011 := by
  apply branch_checked idp00010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-727761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-731761639/4000000 : ℚ) by norm_num]
  exact coverp00010110111
theorem coverp0001011011 : Covers (-727761639/8000000 : ℚ) vp0001011011 := join_branches bp00010110110 bp00010110111
private noncomputable def vp00010110101111_0 : Blocks := edgeBlocks% "full/vectors/00010110101111-V-0000.bin"
noncomputable def vp00010110101111 : Blocks := vp00010110101111_0
theorem coverp00010110101111 : Covers (-727261639/500000 : ℚ) vp00010110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110101110_0 : Blocks := edgeBlocks% "full/vectors/00010110101110-V-0000.bin"
noncomputable def vp00010110101110 : Blocks := vp00010110101110_0
theorem coverp00010110101110 : Covers (-726761639/500000 : ℚ) vp00010110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010111_0 : Blocks := edgeBlocks% "full/vectors/0001011010111-V-0000.bin"
noncomputable def vp0001011010111 : Blocks := vp0001011010111_0
private theorem bp00010110101110 : Branch 0 (-726761639/1000000 : ℚ) vp0001011010111 := by
  apply branch_left_normalized (c:=vp00010110101110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-726761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-726761639/500000 : ℚ) by norm_num]
  exact coverp00010110101110
private noncomputable def ep00010110101111_0 : Blocks := edgeBlocks% "full/vectors/00010110101111-E-0000.bin"
noncomputable def ep00010110101111 : Blocks := ep00010110101111_0
private theorem idp00010110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010111.list =
    C ((2:ℤ)^60) * horner X vp00010110101111.list + horner X ep00010110101111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110101111 : Branch 1 (-726761639/1000000 : ℚ) vp0001011010111 := by
  apply branch_checked idp00010110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-726761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-727261639/500000 : ℚ) by norm_num]
  exact coverp00010110101111
theorem coverp0001011010111 : Covers (-726761639/1000000 : ℚ) vp0001011010111 := join_branches bp00010110101110 bp00010110101111
private noncomputable def vp00010110101101_0 : Blocks := edgeBlocks% "full/vectors/00010110101101-V-0000.bin"
noncomputable def vp00010110101101 : Blocks := vp00010110101101_0
theorem coverp00010110101101 : Covers (-726261639/500000 : ℚ) vp00010110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110101100_0 : Blocks := edgeBlocks% "full/vectors/00010110101100-V-0000.bin"
noncomputable def vp00010110101100 : Blocks := vp00010110101100_0
theorem coverp00010110101100 : Covers (-725761639/500000 : ℚ) vp00010110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010110_0 : Blocks := edgeBlocks% "full/vectors/0001011010110-V-0000.bin"
noncomputable def vp0001011010110 : Blocks := vp0001011010110_0
private theorem bp00010110101100 : Branch 0 (-725761639/1000000 : ℚ) vp0001011010110 := by
  apply branch_left_normalized (c:=vp00010110101100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-725761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-725761639/500000 : ℚ) by norm_num]
  exact coverp00010110101100
private noncomputable def ep00010110101101_0 : Blocks := edgeBlocks% "full/vectors/00010110101101-E-0000.bin"
noncomputable def ep00010110101101 : Blocks := ep00010110101101_0
private theorem idp00010110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010110.list =
    C ((2:ℤ)^61) * horner X vp00010110101101.list + horner X ep00010110101101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110101101 : Branch 1 (-725761639/1000000 : ℚ) vp0001011010110 := by
  apply branch_checked idp00010110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-725761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-726261639/500000 : ℚ) by norm_num]
  exact coverp00010110101101
theorem coverp0001011010110 : Covers (-725761639/1000000 : ℚ) vp0001011010110 := join_branches bp00010110101100 bp00010110101101
private noncomputable def vp000101101011_0 : Blocks := edgeBlocks% "full/vectors/000101101011-V-0000.bin"
noncomputable def vp000101101011 : Blocks := vp000101101011_0
private theorem bp0001011010110 : Branch 0 (-725761639/2000000 : ℚ) vp000101101011 := by
  apply branch_left_normalized (c:=vp0001011010110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-725761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-725761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010110
private noncomputable def ep0001011010111_0 : Blocks := edgeBlocks% "full/vectors/0001011010111-E-0000.bin"
noncomputable def ep0001011010111 : Blocks := ep0001011010111_0
private theorem idp0001011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101011.list =
    C ((2:ℤ)^102) * horner X vp0001011010111.list + horner X ep0001011010111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011010111 : Branch 1 (-725761639/2000000 : ℚ) vp000101101011 := by
  apply branch_checked idp0001011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-725761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-726761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010111
theorem coverp000101101011 : Covers (-725761639/2000000 : ℚ) vp000101101011 := join_branches bp0001011010110 bp0001011010111
private noncomputable def vp00010110101011_0 : Blocks := edgeBlocks% "full/vectors/00010110101011-V-0000.bin"
noncomputable def vp00010110101011 : Blocks := vp00010110101011_0
theorem coverp00010110101011 : Covers (-725261639/500000 : ℚ) vp00010110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110101010_0 : Blocks := edgeBlocks% "full/vectors/00010110101010-V-0000.bin"
noncomputable def vp00010110101010 : Blocks := vp00010110101010_0
theorem coverp00010110101010 : Covers (-724761639/500000 : ℚ) vp00010110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010101_0 : Blocks := edgeBlocks% "full/vectors/0001011010101-V-0000.bin"
noncomputable def vp0001011010101 : Blocks := vp0001011010101_0
private theorem bp00010110101010 : Branch 0 (-724761639/1000000 : ℚ) vp0001011010101 := by
  apply branch_left_normalized (c:=vp00010110101010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-724761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-724761639/500000 : ℚ) by norm_num]
  exact coverp00010110101010
private noncomputable def ep00010110101011_0 : Blocks := edgeBlocks% "full/vectors/00010110101011-E-0000.bin"
noncomputable def ep00010110101011 : Blocks := ep00010110101011_0
private theorem idp00010110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010101.list =
    C ((2:ℤ)^59) * horner X vp00010110101011.list + horner X ep00010110101011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110101011 : Branch 1 (-724761639/1000000 : ℚ) vp0001011010101 := by
  apply branch_checked idp00010110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-724761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-725261639/500000 : ℚ) by norm_num]
  exact coverp00010110101011
theorem coverp0001011010101 : Covers (-724761639/1000000 : ℚ) vp0001011010101 := join_branches bp00010110101010 bp00010110101011
private noncomputable def vp00010110101001_0 : Blocks := edgeBlocks% "full/vectors/00010110101001-V-0000.bin"
noncomputable def vp00010110101001 : Blocks := vp00010110101001_0
theorem coverp00010110101001 : Covers (-724261639/500000 : ℚ) vp00010110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110101000_0 : Blocks := edgeBlocks% "full/vectors/00010110101000-V-0000.bin"
noncomputable def vp00010110101000 : Blocks := vp00010110101000_0
theorem coverp00010110101000 : Covers (-723761639/500000 : ℚ) vp00010110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010100_0 : Blocks := edgeBlocks% "full/vectors/0001011010100-V-0000.bin"
noncomputable def vp0001011010100 : Blocks := vp0001011010100_0
private theorem bp00010110101000 : Branch 0 (-723761639/1000000 : ℚ) vp0001011010100 := by
  apply branch_left_normalized (c:=vp00010110101000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-723761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-723761639/500000 : ℚ) by norm_num]
  exact coverp00010110101000
private noncomputable def ep00010110101001_0 : Blocks := edgeBlocks% "full/vectors/00010110101001-E-0000.bin"
noncomputable def ep00010110101001 : Blocks := ep00010110101001_0
private theorem idp00010110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010100.list =
    C ((2:ℤ)^59) * horner X vp00010110101001.list + horner X ep00010110101001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110101001 : Branch 1 (-723761639/1000000 : ℚ) vp0001011010100 := by
  apply branch_checked idp00010110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-723761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-724261639/500000 : ℚ) by norm_num]
  exact coverp00010110101001
theorem coverp0001011010100 : Covers (-723761639/1000000 : ℚ) vp0001011010100 := join_branches bp00010110101000 bp00010110101001
private noncomputable def vp000101101010_0 : Blocks := edgeBlocks% "full/vectors/000101101010-V-0000.bin"
noncomputable def vp000101101010 : Blocks := vp000101101010_0
private theorem bp0001011010100 : Branch 0 (-723761639/2000000 : ℚ) vp000101101010 := by
  apply branch_left_normalized (c:=vp0001011010100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-723761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-723761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010100
private noncomputable def ep0001011010101_0 : Blocks := edgeBlocks% "full/vectors/0001011010101-E-0000.bin"
noncomputable def ep0001011010101 : Blocks := ep0001011010101_0
private theorem idp0001011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101010.list =
    C ((2:ℤ)^100) * horner X vp0001011010101.list + horner X ep0001011010101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011010101 : Branch 1 (-723761639/2000000 : ℚ) vp000101101010 := by
  apply branch_checked idp0001011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-723761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-724761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010101
theorem coverp000101101010 : Covers (-723761639/2000000 : ℚ) vp000101101010 := join_branches bp0001011010100 bp0001011010101
private noncomputable def vp00010110101_0 : Blocks := edgeBlocks% "full/vectors/00010110101-V-0000.bin"
private noncomputable def vp00010110101_1 : Blocks := edgeBlocks% "full/vectors/00010110101-V-0001.bin"
noncomputable def vp00010110101 : Blocks := (Blocks.join vp00010110101_0 vp00010110101_1)
private theorem bp000101101010 : Branch 0 (-723761639/4000000 : ℚ) vp00010110101 := by
  apply branch_left_normalized (c:=vp000101101010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-723761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-723761639/2000000 : ℚ) by norm_num]
  exact coverp000101101010
private noncomputable def ep000101101011_0 : Blocks := edgeBlocks% "full/vectors/000101101011-E-0000.bin"
private noncomputable def ep000101101011_1 : Blocks := edgeBlocks% "full/vectors/000101101011-E-0001.bin"
noncomputable def ep000101101011 : Blocks := (Blocks.join ep000101101011_0 ep000101101011_1)
private theorem idp000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110101.list =
    C ((2:ℤ)^179) * horner X vp000101101011.list + horner X ep000101101011.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101101011 : Branch 1 (-723761639/4000000 : ℚ) vp00010110101 := by
  apply branch_checked idp000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-723761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-725761639/2000000 : ℚ) by norm_num]
  exact coverp000101101011
theorem coverp00010110101 : Covers (-723761639/4000000 : ℚ) vp00010110101 := join_branches bp000101101010 bp000101101011
private noncomputable def vp00010110100111_0 : Blocks := edgeBlocks% "full/vectors/00010110100111-V-0000.bin"
noncomputable def vp00010110100111 : Blocks := vp00010110100111_0
theorem coverp00010110100111 : Covers (-723261639/500000 : ℚ) vp00010110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110100110_0 : Blocks := edgeBlocks% "full/vectors/00010110100110-V-0000.bin"
noncomputable def vp00010110100110 : Blocks := vp00010110100110_0
theorem coverp00010110100110 : Covers (-722761639/500000 : ℚ) vp00010110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010011_0 : Blocks := edgeBlocks% "full/vectors/0001011010011-V-0000.bin"
noncomputable def vp0001011010011 : Blocks := vp0001011010011_0
private theorem bp00010110100110 : Branch 0 (-722761639/1000000 : ℚ) vp0001011010011 := by
  apply branch_left_normalized (c:=vp00010110100110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-722761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-722761639/500000 : ℚ) by norm_num]
  exact coverp00010110100110
private noncomputable def ep00010110100111_0 : Blocks := edgeBlocks% "full/vectors/00010110100111-E-0000.bin"
noncomputable def ep00010110100111 : Blocks := ep00010110100111_0
private theorem idp00010110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010011.list =
    C ((2:ℤ)^60) * horner X vp00010110100111.list + horner X ep00010110100111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110100111 : Branch 1 (-722761639/1000000 : ℚ) vp0001011010011 := by
  apply branch_checked idp00010110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-722761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-723261639/500000 : ℚ) by norm_num]
  exact coverp00010110100111
theorem coverp0001011010011 : Covers (-722761639/1000000 : ℚ) vp0001011010011 := join_branches bp00010110100110 bp00010110100111
private noncomputable def vp00010110100101_0 : Blocks := edgeBlocks% "full/vectors/00010110100101-V-0000.bin"
noncomputable def vp00010110100101 : Blocks := vp00010110100101_0
theorem coverp00010110100101 : Covers (-722261639/500000 : ℚ) vp00010110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110100100_0 : Blocks := edgeBlocks% "full/vectors/00010110100100-V-0000.bin"
noncomputable def vp00010110100100 : Blocks := vp00010110100100_0
theorem coverp00010110100100 : Covers (-721761639/500000 : ℚ) vp00010110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010010_0 : Blocks := edgeBlocks% "full/vectors/0001011010010-V-0000.bin"
noncomputable def vp0001011010010 : Blocks := vp0001011010010_0
private theorem bp00010110100100 : Branch 0 (-721761639/1000000 : ℚ) vp0001011010010 := by
  apply branch_left_normalized (c:=vp00010110100100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-721761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-721761639/500000 : ℚ) by norm_num]
  exact coverp00010110100100
private noncomputable def ep00010110100101_0 : Blocks := edgeBlocks% "full/vectors/00010110100101-E-0000.bin"
noncomputable def ep00010110100101 : Blocks := ep00010110100101_0
private theorem idp00010110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010010.list =
    C ((2:ℤ)^60) * horner X vp00010110100101.list + horner X ep00010110100101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110100101 : Branch 1 (-721761639/1000000 : ℚ) vp0001011010010 := by
  apply branch_checked idp00010110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-721761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-722261639/500000 : ℚ) by norm_num]
  exact coverp00010110100101
theorem coverp0001011010010 : Covers (-721761639/1000000 : ℚ) vp0001011010010 := join_branches bp00010110100100 bp00010110100101
private noncomputable def vp000101101001_0 : Blocks := edgeBlocks% "full/vectors/000101101001-V-0000.bin"
noncomputable def vp000101101001 : Blocks := vp000101101001_0
private theorem bp0001011010010 : Branch 0 (-721761639/2000000 : ℚ) vp000101101001 := by
  apply branch_left_normalized (c:=vp0001011010010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-721761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-721761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010010
private noncomputable def ep0001011010011_0 : Blocks := edgeBlocks% "full/vectors/0001011010011-E-0000.bin"
noncomputable def ep0001011010011 : Blocks := ep0001011010011_0
private theorem idp0001011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101001.list =
    C ((2:ℤ)^99) * horner X vp0001011010011.list + horner X ep0001011010011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011010011 : Branch 1 (-721761639/2000000 : ℚ) vp000101101001 := by
  apply branch_checked idp0001011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-721761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-722761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010011
theorem coverp000101101001 : Covers (-721761639/2000000 : ℚ) vp000101101001 := join_branches bp0001011010010 bp0001011010011
private noncomputable def vp00010110100011_0 : Blocks := edgeBlocks% "full/vectors/00010110100011-V-0000.bin"
noncomputable def vp00010110100011 : Blocks := vp00010110100011_0
theorem coverp00010110100011 : Covers (-721261639/500000 : ℚ) vp00010110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110100010_0 : Blocks := edgeBlocks% "full/vectors/00010110100010-V-0000.bin"
noncomputable def vp00010110100010 : Blocks := vp00010110100010_0
theorem coverp00010110100010 : Covers (-720761639/500000 : ℚ) vp00010110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010001_0 : Blocks := edgeBlocks% "full/vectors/0001011010001-V-0000.bin"
noncomputable def vp0001011010001 : Blocks := vp0001011010001_0
private theorem bp00010110100010 : Branch 0 (-720761639/1000000 : ℚ) vp0001011010001 := by
  apply branch_left_normalized (c:=vp00010110100010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-720761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-720761639/500000 : ℚ) by norm_num]
  exact coverp00010110100010
private noncomputable def ep00010110100011_0 : Blocks := edgeBlocks% "full/vectors/00010110100011-E-0000.bin"
noncomputable def ep00010110100011 : Blocks := ep00010110100011_0
private theorem idp00010110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010001.list =
    C ((2:ℤ)^60) * horner X vp00010110100011.list + horner X ep00010110100011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110100011 : Branch 1 (-720761639/1000000 : ℚ) vp0001011010001 := by
  apply branch_checked idp00010110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-720761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-721261639/500000 : ℚ) by norm_num]
  exact coverp00010110100011
theorem coverp0001011010001 : Covers (-720761639/1000000 : ℚ) vp0001011010001 := join_branches bp00010110100010 bp00010110100011
private noncomputable def vp00010110100001_0 : Blocks := edgeBlocks% "full/vectors/00010110100001-V-0000.bin"
noncomputable def vp00010110100001 : Blocks := vp00010110100001_0
theorem coverp00010110100001 : Covers (-720261639/500000 : ℚ) vp00010110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110100000_0 : Blocks := edgeBlocks% "full/vectors/00010110100000-V-0000.bin"
noncomputable def vp00010110100000 : Blocks := vp00010110100000_0
theorem coverp00010110100000 : Covers (-719761639/500000 : ℚ) vp00010110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011010000_0 : Blocks := edgeBlocks% "full/vectors/0001011010000-V-0000.bin"
noncomputable def vp0001011010000 : Blocks := vp0001011010000_0
private theorem bp00010110100000 : Branch 0 (-719761639/1000000 : ℚ) vp0001011010000 := by
  apply branch_left_normalized (c:=vp00010110100000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-719761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-719761639/500000 : ℚ) by norm_num]
  exact coverp00010110100000
private noncomputable def ep00010110100001_0 : Blocks := edgeBlocks% "full/vectors/00010110100001-E-0000.bin"
noncomputable def ep00010110100001 : Blocks := ep00010110100001_0
private theorem idp00010110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010000.list =
    C ((2:ℤ)^60) * horner X vp00010110100001.list + horner X ep00010110100001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110100001 : Branch 1 (-719761639/1000000 : ℚ) vp0001011010000 := by
  apply branch_checked idp00010110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-719761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-720261639/500000 : ℚ) by norm_num]
  exact coverp00010110100001
theorem coverp0001011010000 : Covers (-719761639/1000000 : ℚ) vp0001011010000 := join_branches bp00010110100000 bp00010110100001
private noncomputable def vp000101101000_0 : Blocks := edgeBlocks% "full/vectors/000101101000-V-0000.bin"
noncomputable def vp000101101000 : Blocks := vp000101101000_0
private theorem bp0001011010000 : Branch 0 (-719761639/2000000 : ℚ) vp000101101000 := by
  apply branch_left_normalized (c:=vp0001011010000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-719761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-719761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010000
private noncomputable def ep0001011010001_0 : Blocks := edgeBlocks% "full/vectors/0001011010001-E-0000.bin"
noncomputable def ep0001011010001 : Blocks := ep0001011010001_0
private theorem idp0001011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101000.list =
    C ((2:ℤ)^102) * horner X vp0001011010001.list + horner X ep0001011010001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011010001 : Branch 1 (-719761639/2000000 : ℚ) vp000101101000 := by
  apply branch_checked idp0001011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-719761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-720761639/1000000 : ℚ) by norm_num]
  exact coverp0001011010001
theorem coverp000101101000 : Covers (-719761639/2000000 : ℚ) vp000101101000 := join_branches bp0001011010000 bp0001011010001
private noncomputable def vp00010110100_0 : Blocks := edgeBlocks% "full/vectors/00010110100-V-0000.bin"
private noncomputable def vp00010110100_1 : Blocks := edgeBlocks% "full/vectors/00010110100-V-0001.bin"
noncomputable def vp00010110100 : Blocks := (Blocks.join vp00010110100_0 vp00010110100_1)
private theorem bp000101101000 : Branch 0 (-719761639/4000000 : ℚ) vp00010110100 := by
  apply branch_left_normalized (c:=vp000101101000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-719761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-719761639/2000000 : ℚ) by norm_num]
  exact coverp000101101000
private noncomputable def ep000101101001_0 : Blocks := edgeBlocks% "full/vectors/000101101001-E-0000.bin"
private noncomputable def ep000101101001_1 : Blocks := edgeBlocks% "full/vectors/000101101001-E-0001.bin"
noncomputable def ep000101101001 : Blocks := (Blocks.join ep000101101001_0 ep000101101001_1)
private theorem idp000101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110100.list =
    C ((2:ℤ)^183) * horner X vp000101101001.list + horner X ep000101101001.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101101001 : Branch 1 (-719761639/4000000 : ℚ) vp00010110100 := by
  apply branch_checked idp000101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-719761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-721761639/2000000 : ℚ) by norm_num]
  exact coverp000101101001
theorem coverp00010110100 : Covers (-719761639/4000000 : ℚ) vp00010110100 := join_branches bp000101101000 bp000101101001
private noncomputable def vp0001011010_0 : Blocks := edgeBlocks% "full/vectors/0001011010-V-0000.bin"
private noncomputable def vp0001011010_1 : Blocks := edgeBlocks% "full/vectors/0001011010-V-0001.bin"
private noncomputable def vp0001011010_2 : Blocks := edgeBlocks% "full/vectors/0001011010-V-0002.bin"
noncomputable def vp0001011010 : Blocks := (Blocks.join vp0001011010_0 (Blocks.join vp0001011010_1 vp0001011010_2))
private theorem bp00010110100 : Branch 0 (-719761639/8000000 : ℚ) vp0001011010 := by
  apply branch_left_normalized (c:=vp00010110100) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-719761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-719761639/4000000 : ℚ) by norm_num]
  exact coverp00010110100
private noncomputable def ep00010110101_0 : Blocks := edgeBlocks% "full/vectors/00010110101-E-0000.bin"
private noncomputable def ep00010110101_1 : Blocks := edgeBlocks% "full/vectors/00010110101-E-0001.bin"
private noncomputable def ep00010110101_2 : Blocks := edgeBlocks% "full/vectors/00010110101-E-0002.bin"
noncomputable def ep00010110101 : Blocks := (Blocks.join ep00010110101_0 (Blocks.join ep00010110101_1 ep00010110101_2))
private theorem idp00010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011010.list =
    C ((2:ℤ)^339) * horner X vp00010110101.list + horner X ep00010110101.list := by
  exact edge_identity (B := (2:ℤ)^572) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110101 : Branch 1 (-719761639/8000000 : ℚ) vp0001011010 := by
  apply branch_checked idp00010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-719761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-723761639/4000000 : ℚ) by norm_num]
  exact coverp00010110101
theorem coverp0001011010 : Covers (-719761639/8000000 : ℚ) vp0001011010 := join_branches bp00010110100 bp00010110101
private noncomputable def vp000101101_0 : Blocks := edgeBlocks% "full/vectors/000101101-V-0000.bin"
private noncomputable def vp000101101_1 : Blocks := edgeBlocks% "full/vectors/000101101-V-0001.bin"
private noncomputable def vp000101101_2 : Blocks := edgeBlocks% "full/vectors/000101101-V-0002.bin"
private noncomputable def vp000101101_3 : Blocks := edgeBlocks% "full/vectors/000101101-V-0003.bin"
private noncomputable def vp000101101_4 : Blocks := edgeBlocks% "full/vectors/000101101-V-0004.bin"
noncomputable def vp000101101 : Blocks := (Blocks.join (Blocks.join vp000101101_0 vp000101101_1) (Blocks.join vp000101101_2 (Blocks.join vp000101101_3 vp000101101_4)))
private theorem bp0001011010 : Branch 0 (-719761639/16000000 : ℚ) vp000101101 := by
  apply branch_left_normalized (c:=vp0001011010) (k:=0) (m:=314) (by decide +kernel)
  rw [show 2*(-719761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-719761639/8000000 : ℚ) by norm_num]
  exact coverp0001011010
private noncomputable def ep0001011011_0 : Blocks := edgeBlocks% "full/vectors/0001011011-E-0000.bin"
private noncomputable def ep0001011011_1 : Blocks := edgeBlocks% "full/vectors/0001011011-E-0001.bin"
private noncomputable def ep0001011011_2 : Blocks := edgeBlocks% "full/vectors/0001011011-E-0002.bin"
private noncomputable def ep0001011011_3 : Blocks := edgeBlocks% "full/vectors/0001011011-E-0003.bin"
private noncomputable def ep0001011011_4 : Blocks := edgeBlocks% "full/vectors/0001011011-E-0004.bin"
noncomputable def ep0001011011 : Blocks := (Blocks.join (Blocks.join ep0001011011_0 ep0001011011_1) (Blocks.join ep0001011011_2 (Blocks.join ep0001011011_3 ep0001011011_4)))
private theorem idp0001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101101.list =
    C ((2:ℤ)^653) * horner X vp0001011011.list + horner X ep0001011011.list := by
  exact edge_identity (B := (2:ℤ)^1017) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011011 : Branch 1 (-719761639/16000000 : ℚ) vp000101101 := by
  apply branch_checked idp0001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-719761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-727761639/8000000 : ℚ) by norm_num]
  exact coverp0001011011
theorem coverp000101101 : Covers (-719761639/16000000 : ℚ) vp000101101 := join_branches bp0001011010 bp0001011011
private noncomputable def vp00010110011111_0 : Blocks := edgeBlocks% "full/vectors/00010110011111-V-0000.bin"
noncomputable def vp00010110011111 : Blocks := vp00010110011111_0
theorem coverp00010110011111 : Covers (-719261639/500000 : ℚ) vp00010110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110011110_0 : Blocks := edgeBlocks% "full/vectors/00010110011110-V-0000.bin"
noncomputable def vp00010110011110 : Blocks := vp00010110011110_0
theorem coverp00010110011110 : Covers (-718761639/500000 : ℚ) vp00010110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001111_0 : Blocks := edgeBlocks% "full/vectors/0001011001111-V-0000.bin"
noncomputable def vp0001011001111 : Blocks := vp0001011001111_0
private theorem bp00010110011110 : Branch 0 (-718761639/1000000 : ℚ) vp0001011001111 := by
  apply branch_left_normalized (c:=vp00010110011110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-718761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-718761639/500000 : ℚ) by norm_num]
  exact coverp00010110011110
private noncomputable def ep00010110011111_0 : Blocks := edgeBlocks% "full/vectors/00010110011111-E-0000.bin"
noncomputable def ep00010110011111 : Blocks := ep00010110011111_0
private theorem idp00010110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001111.list =
    C ((2:ℤ)^60) * horner X vp00010110011111.list + horner X ep00010110011111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110011111 : Branch 1 (-718761639/1000000 : ℚ) vp0001011001111 := by
  apply branch_checked idp00010110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-718761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-719261639/500000 : ℚ) by norm_num]
  exact coverp00010110011111
theorem coverp0001011001111 : Covers (-718761639/1000000 : ℚ) vp0001011001111 := join_branches bp00010110011110 bp00010110011111
private noncomputable def vp00010110011101_0 : Blocks := edgeBlocks% "full/vectors/00010110011101-V-0000.bin"
noncomputable def vp00010110011101 : Blocks := vp00010110011101_0
theorem coverp00010110011101 : Covers (-718261639/500000 : ℚ) vp00010110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110011100_0 : Blocks := edgeBlocks% "full/vectors/00010110011100-V-0000.bin"
noncomputable def vp00010110011100 : Blocks := vp00010110011100_0
theorem coverp00010110011100 : Covers (-717761639/500000 : ℚ) vp00010110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001110_0 : Blocks := edgeBlocks% "full/vectors/0001011001110-V-0000.bin"
noncomputable def vp0001011001110 : Blocks := vp0001011001110_0
private theorem bp00010110011100 : Branch 0 (-717761639/1000000 : ℚ) vp0001011001110 := by
  apply branch_left_normalized (c:=vp00010110011100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-717761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-717761639/500000 : ℚ) by norm_num]
  exact coverp00010110011100
private noncomputable def ep00010110011101_0 : Blocks := edgeBlocks% "full/vectors/00010110011101-E-0000.bin"
noncomputable def ep00010110011101 : Blocks := ep00010110011101_0
private theorem idp00010110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001110.list =
    C ((2:ℤ)^60) * horner X vp00010110011101.list + horner X ep00010110011101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110011101 : Branch 1 (-717761639/1000000 : ℚ) vp0001011001110 := by
  apply branch_checked idp00010110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-717761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-718261639/500000 : ℚ) by norm_num]
  exact coverp00010110011101
theorem coverp0001011001110 : Covers (-717761639/1000000 : ℚ) vp0001011001110 := join_branches bp00010110011100 bp00010110011101
private noncomputable def vp000101100111_0 : Blocks := edgeBlocks% "full/vectors/000101100111-V-0000.bin"
noncomputable def vp000101100111 : Blocks := vp000101100111_0
private theorem bp0001011001110 : Branch 0 (-717761639/2000000 : ℚ) vp000101100111 := by
  apply branch_left_normalized (c:=vp0001011001110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-717761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-717761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001110
private noncomputable def ep0001011001111_0 : Blocks := edgeBlocks% "full/vectors/0001011001111-E-0000.bin"
noncomputable def ep0001011001111 : Blocks := ep0001011001111_0
private theorem idp0001011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100111.list =
    C ((2:ℤ)^101) * horner X vp0001011001111.list + horner X ep0001011001111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011001111 : Branch 1 (-717761639/2000000 : ℚ) vp000101100111 := by
  apply branch_checked idp0001011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-717761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-718761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001111
theorem coverp000101100111 : Covers (-717761639/2000000 : ℚ) vp000101100111 := join_branches bp0001011001110 bp0001011001111
private noncomputable def vp00010110011011_0 : Blocks := edgeBlocks% "full/vectors/00010110011011-V-0000.bin"
noncomputable def vp00010110011011 : Blocks := vp00010110011011_0
theorem coverp00010110011011 : Covers (-717261639/500000 : ℚ) vp00010110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110011010_0 : Blocks := edgeBlocks% "full/vectors/00010110011010-V-0000.bin"
noncomputable def vp00010110011010 : Blocks := vp00010110011010_0
theorem coverp00010110011010 : Covers (-716761639/500000 : ℚ) vp00010110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001101_0 : Blocks := edgeBlocks% "full/vectors/0001011001101-V-0000.bin"
noncomputable def vp0001011001101 : Blocks := vp0001011001101_0
private theorem bp00010110011010 : Branch 0 (-716761639/1000000 : ℚ) vp0001011001101 := by
  apply branch_left_normalized (c:=vp00010110011010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-716761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-716761639/500000 : ℚ) by norm_num]
  exact coverp00010110011010
private noncomputable def ep00010110011011_0 : Blocks := edgeBlocks% "full/vectors/00010110011011-E-0000.bin"
noncomputable def ep00010110011011 : Blocks := ep00010110011011_0
private theorem idp00010110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001101.list =
    C ((2:ℤ)^60) * horner X vp00010110011011.list + horner X ep00010110011011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110011011 : Branch 1 (-716761639/1000000 : ℚ) vp0001011001101 := by
  apply branch_checked idp00010110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-716761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-717261639/500000 : ℚ) by norm_num]
  exact coverp00010110011011
theorem coverp0001011001101 : Covers (-716761639/1000000 : ℚ) vp0001011001101 := join_branches bp00010110011010 bp00010110011011
private noncomputable def vp00010110011001_0 : Blocks := edgeBlocks% "full/vectors/00010110011001-V-0000.bin"
noncomputable def vp00010110011001 : Blocks := vp00010110011001_0
theorem coverp00010110011001 : Covers (-716261639/500000 : ℚ) vp00010110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110011000_0 : Blocks := edgeBlocks% "full/vectors/00010110011000-V-0000.bin"
noncomputable def vp00010110011000 : Blocks := vp00010110011000_0
theorem coverp00010110011000 : Covers (-715761639/500000 : ℚ) vp00010110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001100_0 : Blocks := edgeBlocks% "full/vectors/0001011001100-V-0000.bin"
noncomputable def vp0001011001100 : Blocks := vp0001011001100_0
private theorem bp00010110011000 : Branch 0 (-715761639/1000000 : ℚ) vp0001011001100 := by
  apply branch_left_normalized (c:=vp00010110011000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-715761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-715761639/500000 : ℚ) by norm_num]
  exact coverp00010110011000
private noncomputable def ep00010110011001_0 : Blocks := edgeBlocks% "full/vectors/00010110011001-E-0000.bin"
noncomputable def ep00010110011001 : Blocks := ep00010110011001_0
private theorem idp00010110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001100.list =
    C ((2:ℤ)^60) * horner X vp00010110011001.list + horner X ep00010110011001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110011001 : Branch 1 (-715761639/1000000 : ℚ) vp0001011001100 := by
  apply branch_checked idp00010110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-715761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-716261639/500000 : ℚ) by norm_num]
  exact coverp00010110011001
theorem coverp0001011001100 : Covers (-715761639/1000000 : ℚ) vp0001011001100 := join_branches bp00010110011000 bp00010110011001
private noncomputable def vp000101100110_0 : Blocks := edgeBlocks% "full/vectors/000101100110-V-0000.bin"
noncomputable def vp000101100110 : Blocks := vp000101100110_0
private theorem bp0001011001100 : Branch 0 (-715761639/2000000 : ℚ) vp000101100110 := by
  apply branch_left_normalized (c:=vp0001011001100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-715761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-715761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001100
private noncomputable def ep0001011001101_0 : Blocks := edgeBlocks% "full/vectors/0001011001101-E-0000.bin"
noncomputable def ep0001011001101 : Blocks := ep0001011001101_0
private theorem idp0001011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100110.list =
    C ((2:ℤ)^101) * horner X vp0001011001101.list + horner X ep0001011001101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011001101 : Branch 1 (-715761639/2000000 : ℚ) vp000101100110 := by
  apply branch_checked idp0001011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-715761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-716761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001101
theorem coverp000101100110 : Covers (-715761639/2000000 : ℚ) vp000101100110 := join_branches bp0001011001100 bp0001011001101
private noncomputable def vp00010110011_0 : Blocks := edgeBlocks% "full/vectors/00010110011-V-0000.bin"
private noncomputable def vp00010110011_1 : Blocks := edgeBlocks% "full/vectors/00010110011-V-0001.bin"
noncomputable def vp00010110011 : Blocks := (Blocks.join vp00010110011_0 vp00010110011_1)
private theorem bp000101100110 : Branch 0 (-715761639/4000000 : ℚ) vp00010110011 := by
  apply branch_left_normalized (c:=vp000101100110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-715761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-715761639/2000000 : ℚ) by norm_num]
  exact coverp000101100110
private noncomputable def ep000101100111_0 : Blocks := edgeBlocks% "full/vectors/000101100111-E-0000.bin"
private noncomputable def ep000101100111_1 : Blocks := edgeBlocks% "full/vectors/000101100111-E-0001.bin"
noncomputable def ep000101100111 : Blocks := (Blocks.join ep000101100111_0 ep000101100111_1)
private theorem idp000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110011.list =
    C ((2:ℤ)^180) * horner X vp000101100111.list + horner X ep000101100111.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101100111 : Branch 1 (-715761639/4000000 : ℚ) vp00010110011 := by
  apply branch_checked idp000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-715761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-717761639/2000000 : ℚ) by norm_num]
  exact coverp000101100111
theorem coverp00010110011 : Covers (-715761639/4000000 : ℚ) vp00010110011 := join_branches bp000101100110 bp000101100111
private noncomputable def vp00010110010111_0 : Blocks := edgeBlocks% "full/vectors/00010110010111-V-0000.bin"
noncomputable def vp00010110010111 : Blocks := vp00010110010111_0
theorem coverp00010110010111 : Covers (-715261639/500000 : ℚ) vp00010110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110010110_0 : Blocks := edgeBlocks% "full/vectors/00010110010110-V-0000.bin"
noncomputable def vp00010110010110 : Blocks := vp00010110010110_0
theorem coverp00010110010110 : Covers (-714761639/500000 : ℚ) vp00010110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001011_0 : Blocks := edgeBlocks% "full/vectors/0001011001011-V-0000.bin"
noncomputable def vp0001011001011 : Blocks := vp0001011001011_0
private theorem bp00010110010110 : Branch 0 (-714761639/1000000 : ℚ) vp0001011001011 := by
  apply branch_left_normalized (c:=vp00010110010110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-714761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-714761639/500000 : ℚ) by norm_num]
  exact coverp00010110010110
private noncomputable def ep00010110010111_0 : Blocks := edgeBlocks% "full/vectors/00010110010111-E-0000.bin"
noncomputable def ep00010110010111 : Blocks := ep00010110010111_0
private theorem idp00010110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001011.list =
    C ((2:ℤ)^58) * horner X vp00010110010111.list + horner X ep00010110010111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110010111 : Branch 1 (-714761639/1000000 : ℚ) vp0001011001011 := by
  apply branch_checked idp00010110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-714761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-715261639/500000 : ℚ) by norm_num]
  exact coverp00010110010111
theorem coverp0001011001011 : Covers (-714761639/1000000 : ℚ) vp0001011001011 := join_branches bp00010110010110 bp00010110010111
private noncomputable def vp00010110010101_0 : Blocks := edgeBlocks% "full/vectors/00010110010101-V-0000.bin"
noncomputable def vp00010110010101 : Blocks := vp00010110010101_0
theorem coverp00010110010101 : Covers (-714261639/500000 : ℚ) vp00010110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110010100_0 : Blocks := edgeBlocks% "full/vectors/00010110010100-V-0000.bin"
noncomputable def vp00010110010100 : Blocks := vp00010110010100_0
theorem coverp00010110010100 : Covers (-713761639/500000 : ℚ) vp00010110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001010_0 : Blocks := edgeBlocks% "full/vectors/0001011001010-V-0000.bin"
noncomputable def vp0001011001010 : Blocks := vp0001011001010_0
private theorem bp00010110010100 : Branch 0 (-713761639/1000000 : ℚ) vp0001011001010 := by
  apply branch_left_normalized (c:=vp00010110010100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-713761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-713761639/500000 : ℚ) by norm_num]
  exact coverp00010110010100
private noncomputable def ep00010110010101_0 : Blocks := edgeBlocks% "full/vectors/00010110010101-E-0000.bin"
noncomputable def ep00010110010101 : Blocks := ep00010110010101_0
private theorem idp00010110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001010.list =
    C ((2:ℤ)^60) * horner X vp00010110010101.list + horner X ep00010110010101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110010101 : Branch 1 (-713761639/1000000 : ℚ) vp0001011001010 := by
  apply branch_checked idp00010110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-713761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-714261639/500000 : ℚ) by norm_num]
  exact coverp00010110010101
theorem coverp0001011001010 : Covers (-713761639/1000000 : ℚ) vp0001011001010 := join_branches bp00010110010100 bp00010110010101
private noncomputable def vp000101100101_0 : Blocks := edgeBlocks% "full/vectors/000101100101-V-0000.bin"
noncomputable def vp000101100101 : Blocks := vp000101100101_0
private theorem bp0001011001010 : Branch 0 (-713761639/2000000 : ℚ) vp000101100101 := by
  apply branch_left_normalized (c:=vp0001011001010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-713761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-713761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001010
private noncomputable def ep0001011001011_0 : Blocks := edgeBlocks% "full/vectors/0001011001011-E-0000.bin"
noncomputable def ep0001011001011 : Blocks := ep0001011001011_0
private theorem idp0001011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100101.list =
    C ((2:ℤ)^102) * horner X vp0001011001011.list + horner X ep0001011001011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011001011 : Branch 1 (-713761639/2000000 : ℚ) vp000101100101 := by
  apply branch_checked idp0001011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-713761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-714761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001011
theorem coverp000101100101 : Covers (-713761639/2000000 : ℚ) vp000101100101 := join_branches bp0001011001010 bp0001011001011
private noncomputable def vp00010110010011_0 : Blocks := edgeBlocks% "full/vectors/00010110010011-V-0000.bin"
noncomputable def vp00010110010011 : Blocks := vp00010110010011_0
theorem coverp00010110010011 : Covers (-713261639/500000 : ℚ) vp00010110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110010010_0 : Blocks := edgeBlocks% "full/vectors/00010110010010-V-0000.bin"
noncomputable def vp00010110010010 : Blocks := vp00010110010010_0
theorem coverp00010110010010 : Covers (-712761639/500000 : ℚ) vp00010110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001001_0 : Blocks := edgeBlocks% "full/vectors/0001011001001-V-0000.bin"
noncomputable def vp0001011001001 : Blocks := vp0001011001001_0
private theorem bp00010110010010 : Branch 0 (-712761639/1000000 : ℚ) vp0001011001001 := by
  apply branch_left_normalized (c:=vp00010110010010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-712761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-712761639/500000 : ℚ) by norm_num]
  exact coverp00010110010010
private noncomputable def ep00010110010011_0 : Blocks := edgeBlocks% "full/vectors/00010110010011-E-0000.bin"
noncomputable def ep00010110010011 : Blocks := ep00010110010011_0
private theorem idp00010110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001001.list =
    C ((2:ℤ)^60) * horner X vp00010110010011.list + horner X ep00010110010011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110010011 : Branch 1 (-712761639/1000000 : ℚ) vp0001011001001 := by
  apply branch_checked idp00010110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-712761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-713261639/500000 : ℚ) by norm_num]
  exact coverp00010110010011
theorem coverp0001011001001 : Covers (-712761639/1000000 : ℚ) vp0001011001001 := join_branches bp00010110010010 bp00010110010011
private noncomputable def vp00010110010001_0 : Blocks := edgeBlocks% "full/vectors/00010110010001-V-0000.bin"
noncomputable def vp00010110010001 : Blocks := vp00010110010001_0
theorem coverp00010110010001 : Covers (-712261639/500000 : ℚ) vp00010110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110010000_0 : Blocks := edgeBlocks% "full/vectors/00010110010000-V-0000.bin"
noncomputable def vp00010110010000 : Blocks := vp00010110010000_0
theorem coverp00010110010000 : Covers (-711761639/500000 : ℚ) vp00010110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011001000_0 : Blocks := edgeBlocks% "full/vectors/0001011001000-V-0000.bin"
noncomputable def vp0001011001000 : Blocks := vp0001011001000_0
private theorem bp00010110010000 : Branch 0 (-711761639/1000000 : ℚ) vp0001011001000 := by
  apply branch_left_normalized (c:=vp00010110010000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-711761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-711761639/500000 : ℚ) by norm_num]
  exact coverp00010110010000
private noncomputable def ep00010110010001_0 : Blocks := edgeBlocks% "full/vectors/00010110010001-E-0000.bin"
noncomputable def ep00010110010001 : Blocks := ep00010110010001_0
private theorem idp00010110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001000.list =
    C ((2:ℤ)^60) * horner X vp00010110010001.list + horner X ep00010110010001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110010001 : Branch 1 (-711761639/1000000 : ℚ) vp0001011001000 := by
  apply branch_checked idp00010110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-711761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-712261639/500000 : ℚ) by norm_num]
  exact coverp00010110010001
theorem coverp0001011001000 : Covers (-711761639/1000000 : ℚ) vp0001011001000 := join_branches bp00010110010000 bp00010110010001
private noncomputable def vp000101100100_0 : Blocks := edgeBlocks% "full/vectors/000101100100-V-0000.bin"
noncomputable def vp000101100100 : Blocks := vp000101100100_0
private theorem bp0001011001000 : Branch 0 (-711761639/2000000 : ℚ) vp000101100100 := by
  apply branch_left_normalized (c:=vp0001011001000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-711761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-711761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001000
private noncomputable def ep0001011001001_0 : Blocks := edgeBlocks% "full/vectors/0001011001001-E-0000.bin"
noncomputable def ep0001011001001 : Blocks := ep0001011001001_0
private theorem idp0001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100100.list =
    C ((2:ℤ)^102) * horner X vp0001011001001.list + horner X ep0001011001001.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011001001 : Branch 1 (-711761639/2000000 : ℚ) vp000101100100 := by
  apply branch_checked idp0001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-711761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-712761639/1000000 : ℚ) by norm_num]
  exact coverp0001011001001
theorem coverp000101100100 : Covers (-711761639/2000000 : ℚ) vp000101100100 := join_branches bp0001011001000 bp0001011001001
private noncomputable def vp00010110010_0 : Blocks := edgeBlocks% "full/vectors/00010110010-V-0000.bin"
private noncomputable def vp00010110010_1 : Blocks := edgeBlocks% "full/vectors/00010110010-V-0001.bin"
noncomputable def vp00010110010 : Blocks := (Blocks.join vp00010110010_0 vp00010110010_1)
private theorem bp000101100100 : Branch 0 (-711761639/4000000 : ℚ) vp00010110010 := by
  apply branch_left_normalized (c:=vp000101100100) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-711761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-711761639/2000000 : ℚ) by norm_num]
  exact coverp000101100100
private noncomputable def ep000101100101_0 : Blocks := edgeBlocks% "full/vectors/000101100101-E-0000.bin"
private noncomputable def ep000101100101_1 : Blocks := edgeBlocks% "full/vectors/000101100101-E-0001.bin"
noncomputable def ep000101100101 : Blocks := (Blocks.join ep000101100101_0 ep000101100101_1)
private theorem idp000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110010.list =
    C ((2:ℤ)^182) * horner X vp000101100101.list + horner X ep000101100101.list := by
  exact edge_identity (B := (2:ℤ)^350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101100101 : Branch 1 (-711761639/4000000 : ℚ) vp00010110010 := by
  apply branch_checked idp000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-711761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-713761639/2000000 : ℚ) by norm_num]
  exact coverp000101100101
theorem coverp00010110010 : Covers (-711761639/4000000 : ℚ) vp00010110010 := join_branches bp000101100100 bp000101100101
private noncomputable def vp0001011001_0 : Blocks := edgeBlocks% "full/vectors/0001011001-V-0000.bin"
private noncomputable def vp0001011001_1 : Blocks := edgeBlocks% "full/vectors/0001011001-V-0001.bin"
private noncomputable def vp0001011001_2 : Blocks := edgeBlocks% "full/vectors/0001011001-V-0002.bin"
noncomputable def vp0001011001 : Blocks := (Blocks.join vp0001011001_0 (Blocks.join vp0001011001_1 vp0001011001_2))
private theorem bp00010110010 : Branch 0 (-711761639/8000000 : ℚ) vp0001011001 := by
  apply branch_left_normalized (c:=vp00010110010) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-711761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-711761639/4000000 : ℚ) by norm_num]
  exact coverp00010110010
private noncomputable def ep00010110011_0 : Blocks := edgeBlocks% "full/vectors/00010110011-E-0000.bin"
private noncomputable def ep00010110011_1 : Blocks := edgeBlocks% "full/vectors/00010110011-E-0001.bin"
private noncomputable def ep00010110011_2 : Blocks := edgeBlocks% "full/vectors/00010110011-E-0002.bin"
noncomputable def ep00010110011 : Blocks := (Blocks.join ep00010110011_0 (Blocks.join ep00010110011_1 ep00010110011_2))
private theorem idp00010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011001.list =
    C ((2:ℤ)^340) * horner X vp00010110011.list + horner X ep00010110011.list := by
  exact edge_identity (B := (2:ℤ)^575) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110011 : Branch 1 (-711761639/8000000 : ℚ) vp0001011001 := by
  apply branch_checked idp00010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-711761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-715761639/4000000 : ℚ) by norm_num]
  exact coverp00010110011
theorem coverp0001011001 : Covers (-711761639/8000000 : ℚ) vp0001011001 := join_branches bp00010110010 bp00010110011
private noncomputable def vp00010110001111_0 : Blocks := edgeBlocks% "full/vectors/00010110001111-V-0000.bin"
noncomputable def vp00010110001111 : Blocks := vp00010110001111_0
theorem coverp00010110001111 : Covers (-711261639/500000 : ℚ) vp00010110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110001110_0 : Blocks := edgeBlocks% "full/vectors/00010110001110-V-0000.bin"
noncomputable def vp00010110001110 : Blocks := vp00010110001110_0
theorem coverp00010110001110 : Covers (-710761639/500000 : ℚ) vp00010110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000111_0 : Blocks := edgeBlocks% "full/vectors/0001011000111-V-0000.bin"
noncomputable def vp0001011000111 : Blocks := vp0001011000111_0
private theorem bp00010110001110 : Branch 0 (-710761639/1000000 : ℚ) vp0001011000111 := by
  apply branch_left_normalized (c:=vp00010110001110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-710761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-710761639/500000 : ℚ) by norm_num]
  exact coverp00010110001110
private noncomputable def ep00010110001111_0 : Blocks := edgeBlocks% "full/vectors/00010110001111-E-0000.bin"
noncomputable def ep00010110001111 : Blocks := ep00010110001111_0
private theorem idp00010110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000111.list =
    C ((2:ℤ)^60) * horner X vp00010110001111.list + horner X ep00010110001111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110001111 : Branch 1 (-710761639/1000000 : ℚ) vp0001011000111 := by
  apply branch_checked idp00010110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-710761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-711261639/500000 : ℚ) by norm_num]
  exact coverp00010110001111
theorem coverp0001011000111 : Covers (-710761639/1000000 : ℚ) vp0001011000111 := join_branches bp00010110001110 bp00010110001111
private noncomputable def vp00010110001101_0 : Blocks := edgeBlocks% "full/vectors/00010110001101-V-0000.bin"
noncomputable def vp00010110001101 : Blocks := vp00010110001101_0
theorem coverp00010110001101 : Covers (-710261639/500000 : ℚ) vp00010110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110001100_0 : Blocks := edgeBlocks% "full/vectors/00010110001100-V-0000.bin"
noncomputable def vp00010110001100 : Blocks := vp00010110001100_0
theorem coverp00010110001100 : Covers (-709761639/500000 : ℚ) vp00010110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000110_0 : Blocks := edgeBlocks% "full/vectors/0001011000110-V-0000.bin"
noncomputable def vp0001011000110 : Blocks := vp0001011000110_0
private theorem bp00010110001100 : Branch 0 (-709761639/1000000 : ℚ) vp0001011000110 := by
  apply branch_left_normalized (c:=vp00010110001100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-709761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-709761639/500000 : ℚ) by norm_num]
  exact coverp00010110001100
private noncomputable def ep00010110001101_0 : Blocks := edgeBlocks% "full/vectors/00010110001101-E-0000.bin"
noncomputable def ep00010110001101 : Blocks := ep00010110001101_0
private theorem idp00010110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000110.list =
    C ((2:ℤ)^60) * horner X vp00010110001101.list + horner X ep00010110001101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110001101 : Branch 1 (-709761639/1000000 : ℚ) vp0001011000110 := by
  apply branch_checked idp00010110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-709761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-710261639/500000 : ℚ) by norm_num]
  exact coverp00010110001101
theorem coverp0001011000110 : Covers (-709761639/1000000 : ℚ) vp0001011000110 := join_branches bp00010110001100 bp00010110001101
private noncomputable def vp000101100011_0 : Blocks := edgeBlocks% "full/vectors/000101100011-V-0000.bin"
noncomputable def vp000101100011 : Blocks := vp000101100011_0
private theorem bp0001011000110 : Branch 0 (-709761639/2000000 : ℚ) vp000101100011 := by
  apply branch_left_normalized (c:=vp0001011000110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-709761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-709761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000110
private noncomputable def ep0001011000111_0 : Blocks := edgeBlocks% "full/vectors/0001011000111-E-0000.bin"
noncomputable def ep0001011000111 : Blocks := ep0001011000111_0
private theorem idp0001011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100011.list =
    C ((2:ℤ)^102) * horner X vp0001011000111.list + horner X ep0001011000111.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011000111 : Branch 1 (-709761639/2000000 : ℚ) vp000101100011 := by
  apply branch_checked idp0001011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-709761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-710761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000111
theorem coverp000101100011 : Covers (-709761639/2000000 : ℚ) vp000101100011 := join_branches bp0001011000110 bp0001011000111
private noncomputable def vp00010110001011_0 : Blocks := edgeBlocks% "full/vectors/00010110001011-V-0000.bin"
noncomputable def vp00010110001011 : Blocks := vp00010110001011_0
theorem coverp00010110001011 : Covers (-709261639/500000 : ℚ) vp00010110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110001010_0 : Blocks := edgeBlocks% "full/vectors/00010110001010-V-0000.bin"
noncomputable def vp00010110001010 : Blocks := vp00010110001010_0
theorem coverp00010110001010 : Covers (-708761639/500000 : ℚ) vp00010110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000101_0 : Blocks := edgeBlocks% "full/vectors/0001011000101-V-0000.bin"
noncomputable def vp0001011000101 : Blocks := vp0001011000101_0
private theorem bp00010110001010 : Branch 0 (-708761639/1000000 : ℚ) vp0001011000101 := by
  apply branch_left_normalized (c:=vp00010110001010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-708761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-708761639/500000 : ℚ) by norm_num]
  exact coverp00010110001010
private noncomputable def ep00010110001011_0 : Blocks := edgeBlocks% "full/vectors/00010110001011-E-0000.bin"
noncomputable def ep00010110001011 : Blocks := ep00010110001011_0
private theorem idp00010110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000101.list =
    C ((2:ℤ)^60) * horner X vp00010110001011.list + horner X ep00010110001011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110001011 : Branch 1 (-708761639/1000000 : ℚ) vp0001011000101 := by
  apply branch_checked idp00010110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-708761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-709261639/500000 : ℚ) by norm_num]
  exact coverp00010110001011
theorem coverp0001011000101 : Covers (-708761639/1000000 : ℚ) vp0001011000101 := join_branches bp00010110001010 bp00010110001011
private noncomputable def vp00010110001001_0 : Blocks := edgeBlocks% "full/vectors/00010110001001-V-0000.bin"
noncomputable def vp00010110001001 : Blocks := vp00010110001001_0
theorem coverp00010110001001 : Covers (-708261639/500000 : ℚ) vp00010110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110001000_0 : Blocks := edgeBlocks% "full/vectors/00010110001000-V-0000.bin"
noncomputable def vp00010110001000 : Blocks := vp00010110001000_0
theorem coverp00010110001000 : Covers (-707761639/500000 : ℚ) vp00010110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000100_0 : Blocks := edgeBlocks% "full/vectors/0001011000100-V-0000.bin"
noncomputable def vp0001011000100 : Blocks := vp0001011000100_0
private theorem bp00010110001000 : Branch 0 (-707761639/1000000 : ℚ) vp0001011000100 := by
  apply branch_left_normalized (c:=vp00010110001000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-707761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-707761639/500000 : ℚ) by norm_num]
  exact coverp00010110001000
private noncomputable def ep00010110001001_0 : Blocks := edgeBlocks% "full/vectors/00010110001001-E-0000.bin"
noncomputable def ep00010110001001 : Blocks := ep00010110001001_0
private theorem idp00010110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000100.list =
    C ((2:ℤ)^61) * horner X vp00010110001001.list + horner X ep00010110001001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110001001 : Branch 1 (-707761639/1000000 : ℚ) vp0001011000100 := by
  apply branch_checked idp00010110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-707761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-708261639/500000 : ℚ) by norm_num]
  exact coverp00010110001001
theorem coverp0001011000100 : Covers (-707761639/1000000 : ℚ) vp0001011000100 := join_branches bp00010110001000 bp00010110001001
private noncomputable def vp000101100010_0 : Blocks := edgeBlocks% "full/vectors/000101100010-V-0000.bin"
noncomputable def vp000101100010 : Blocks := vp000101100010_0
private theorem bp0001011000100 : Branch 0 (-707761639/2000000 : ℚ) vp000101100010 := by
  apply branch_left_normalized (c:=vp0001011000100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-707761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-707761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000100
private noncomputable def ep0001011000101_0 : Blocks := edgeBlocks% "full/vectors/0001011000101-E-0000.bin"
noncomputable def ep0001011000101 : Blocks := ep0001011000101_0
private theorem idp0001011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100010.list =
    C ((2:ℤ)^101) * horner X vp0001011000101.list + horner X ep0001011000101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011000101 : Branch 1 (-707761639/2000000 : ℚ) vp000101100010 := by
  apply branch_checked idp0001011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-707761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-708761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000101
theorem coverp000101100010 : Covers (-707761639/2000000 : ℚ) vp000101100010 := join_branches bp0001011000100 bp0001011000101
private noncomputable def vp00010110001_0 : Blocks := edgeBlocks% "full/vectors/00010110001-V-0000.bin"
private noncomputable def vp00010110001_1 : Blocks := edgeBlocks% "full/vectors/00010110001-V-0001.bin"
noncomputable def vp00010110001 : Blocks := (Blocks.join vp00010110001_0 vp00010110001_1)
private theorem bp000101100010 : Branch 0 (-707761639/4000000 : ℚ) vp00010110001 := by
  apply branch_left_normalized (c:=vp000101100010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-707761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-707761639/2000000 : ℚ) by norm_num]
  exact coverp000101100010
private noncomputable def ep000101100011_0 : Blocks := edgeBlocks% "full/vectors/000101100011-E-0000.bin"
private noncomputable def ep000101100011_1 : Blocks := edgeBlocks% "full/vectors/000101100011-E-0001.bin"
noncomputable def ep000101100011 : Blocks := (Blocks.join ep000101100011_0 ep000101100011_1)
private theorem idp000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110001.list =
    C ((2:ℤ)^182) * horner X vp000101100011.list + horner X ep000101100011.list := by
  exact edge_identity (B := (2:ℤ)^351) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101100011 : Branch 1 (-707761639/4000000 : ℚ) vp00010110001 := by
  apply branch_checked idp000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-707761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-709761639/2000000 : ℚ) by norm_num]
  exact coverp000101100011
theorem coverp00010110001 : Covers (-707761639/4000000 : ℚ) vp00010110001 := join_branches bp000101100010 bp000101100011
private noncomputable def vp00010110000111_0 : Blocks := edgeBlocks% "full/vectors/00010110000111-V-0000.bin"
noncomputable def vp00010110000111 : Blocks := vp00010110000111_0
theorem coverp00010110000111 : Covers (-707261639/500000 : ℚ) vp00010110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110000110_0 : Blocks := edgeBlocks% "full/vectors/00010110000110-V-0000.bin"
noncomputable def vp00010110000110 : Blocks := vp00010110000110_0
theorem coverp00010110000110 : Covers (-706761639/500000 : ℚ) vp00010110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000011_0 : Blocks := edgeBlocks% "full/vectors/0001011000011-V-0000.bin"
noncomputable def vp0001011000011 : Blocks := vp0001011000011_0
private theorem bp00010110000110 : Branch 0 (-706761639/1000000 : ℚ) vp0001011000011 := by
  apply branch_left_normalized (c:=vp00010110000110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-706761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-706761639/500000 : ℚ) by norm_num]
  exact coverp00010110000110
private noncomputable def ep00010110000111_0 : Blocks := edgeBlocks% "full/vectors/00010110000111-E-0000.bin"
noncomputable def ep00010110000111 : Blocks := ep00010110000111_0
private theorem idp00010110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000011.list =
    C ((2:ℤ)^61) * horner X vp00010110000111.list + horner X ep00010110000111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110000111 : Branch 1 (-706761639/1000000 : ℚ) vp0001011000011 := by
  apply branch_checked idp00010110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-706761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-707261639/500000 : ℚ) by norm_num]
  exact coverp00010110000111
theorem coverp0001011000011 : Covers (-706761639/1000000 : ℚ) vp0001011000011 := join_branches bp00010110000110 bp00010110000111
private noncomputable def vp00010110000101_0 : Blocks := edgeBlocks% "full/vectors/00010110000101-V-0000.bin"
noncomputable def vp00010110000101 : Blocks := vp00010110000101_0
theorem coverp00010110000101 : Covers (-706261639/500000 : ℚ) vp00010110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110000100_0 : Blocks := edgeBlocks% "full/vectors/00010110000100-V-0000.bin"
noncomputable def vp00010110000100 : Blocks := vp00010110000100_0
theorem coverp00010110000100 : Covers (-705761639/500000 : ℚ) vp00010110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000010_0 : Blocks := edgeBlocks% "full/vectors/0001011000010-V-0000.bin"
noncomputable def vp0001011000010 : Blocks := vp0001011000010_0
private theorem bp00010110000100 : Branch 0 (-705761639/1000000 : ℚ) vp0001011000010 := by
  apply branch_left_normalized (c:=vp00010110000100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-705761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-705761639/500000 : ℚ) by norm_num]
  exact coverp00010110000100
private noncomputable def ep00010110000101_0 : Blocks := edgeBlocks% "full/vectors/00010110000101-E-0000.bin"
noncomputable def ep00010110000101 : Blocks := ep00010110000101_0
private theorem idp00010110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000010.list =
    C ((2:ℤ)^61) * horner X vp00010110000101.list + horner X ep00010110000101.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110000101 : Branch 1 (-705761639/1000000 : ℚ) vp0001011000010 := by
  apply branch_checked idp00010110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-705761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-706261639/500000 : ℚ) by norm_num]
  exact coverp00010110000101
theorem coverp0001011000010 : Covers (-705761639/1000000 : ℚ) vp0001011000010 := join_branches bp00010110000100 bp00010110000101
private noncomputable def vp000101100001_0 : Blocks := edgeBlocks% "full/vectors/000101100001-V-0000.bin"
noncomputable def vp000101100001 : Blocks := vp000101100001_0
private theorem bp0001011000010 : Branch 0 (-705761639/2000000 : ℚ) vp000101100001 := by
  apply branch_left_normalized (c:=vp0001011000010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-705761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-705761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000010
private noncomputable def ep0001011000011_0 : Blocks := edgeBlocks% "full/vectors/0001011000011-E-0000.bin"
noncomputable def ep0001011000011 : Blocks := ep0001011000011_0
private theorem idp0001011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100001.list =
    C ((2:ℤ)^102) * horner X vp0001011000011.list + horner X ep0001011000011.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011000011 : Branch 1 (-705761639/2000000 : ℚ) vp000101100001 := by
  apply branch_checked idp0001011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-705761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-706761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000011
theorem coverp000101100001 : Covers (-705761639/2000000 : ℚ) vp000101100001 := join_branches bp0001011000010 bp0001011000011
private noncomputable def vp00010110000011_0 : Blocks := edgeBlocks% "full/vectors/00010110000011-V-0000.bin"
noncomputable def vp00010110000011 : Blocks := vp00010110000011_0
theorem coverp00010110000011 : Covers (-705261639/500000 : ℚ) vp00010110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110000010_0 : Blocks := edgeBlocks% "full/vectors/00010110000010-V-0000.bin"
noncomputable def vp00010110000010 : Blocks := vp00010110000010_0
theorem coverp00010110000010 : Covers (-704761639/500000 : ℚ) vp00010110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000001_0 : Blocks := edgeBlocks% "full/vectors/0001011000001-V-0000.bin"
noncomputable def vp0001011000001 : Blocks := vp0001011000001_0
private theorem bp00010110000010 : Branch 0 (-704761639/1000000 : ℚ) vp0001011000001 := by
  apply branch_left_normalized (c:=vp00010110000010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-704761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-704761639/500000 : ℚ) by norm_num]
  exact coverp00010110000010
private noncomputable def ep00010110000011_0 : Blocks := edgeBlocks% "full/vectors/00010110000011-E-0000.bin"
noncomputable def ep00010110000011 : Blocks := ep00010110000011_0
private theorem idp00010110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000001.list =
    C ((2:ℤ)^60) * horner X vp00010110000011.list + horner X ep00010110000011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110000011 : Branch 1 (-704761639/1000000 : ℚ) vp0001011000001 := by
  apply branch_checked idp00010110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-704761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-705261639/500000 : ℚ) by norm_num]
  exact coverp00010110000011
theorem coverp0001011000001 : Covers (-704761639/1000000 : ℚ) vp0001011000001 := join_branches bp00010110000010 bp00010110000011
private noncomputable def vp00010110000001_0 : Blocks := edgeBlocks% "full/vectors/00010110000001-V-0000.bin"
noncomputable def vp00010110000001 : Blocks := vp00010110000001_0
theorem coverp00010110000001 : Covers (-704261639/500000 : ℚ) vp00010110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010110000000_0 : Blocks := edgeBlocks% "full/vectors/00010110000000-V-0000.bin"
noncomputable def vp00010110000000 : Blocks := vp00010110000000_0
theorem coverp00010110000000 : Covers (-703761639/500000 : ℚ) vp00010110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011000000_0 : Blocks := edgeBlocks% "full/vectors/0001011000000-V-0000.bin"
noncomputable def vp0001011000000 : Blocks := vp0001011000000_0
private theorem bp00010110000000 : Branch 0 (-703761639/1000000 : ℚ) vp0001011000000 := by
  apply branch_left_normalized (c:=vp00010110000000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-703761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/500000 : ℚ) by norm_num]
  exact coverp00010110000000
private noncomputable def ep00010110000001_0 : Blocks := edgeBlocks% "full/vectors/00010110000001-E-0000.bin"
noncomputable def ep00010110000001 : Blocks := ep00010110000001_0
private theorem idp00010110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000000.list =
    C ((2:ℤ)^59) * horner X vp00010110000001.list + horner X ep00010110000001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110000001 : Branch 1 (-703761639/1000000 : ℚ) vp0001011000000 := by
  apply branch_checked idp00010110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-704261639/500000 : ℚ) by norm_num]
  exact coverp00010110000001
theorem coverp0001011000000 : Covers (-703761639/1000000 : ℚ) vp0001011000000 := join_branches bp00010110000000 bp00010110000001
private noncomputable def vp000101100000_0 : Blocks := edgeBlocks% "full/vectors/000101100000-V-0000.bin"
noncomputable def vp000101100000 : Blocks := vp000101100000_0
private theorem bp0001011000000 : Branch 0 (-703761639/2000000 : ℚ) vp000101100000 := by
  apply branch_left_normalized (c:=vp0001011000000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-703761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000000
private noncomputable def ep0001011000001_0 : Blocks := edgeBlocks% "full/vectors/0001011000001-E-0000.bin"
noncomputable def ep0001011000001 : Blocks := ep0001011000001_0
private theorem idp0001011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100000.list =
    C ((2:ℤ)^101) * horner X vp0001011000001.list + horner X ep0001011000001.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011000001 : Branch 1 (-703761639/2000000 : ℚ) vp000101100000 := by
  apply branch_checked idp0001011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-704761639/1000000 : ℚ) by norm_num]
  exact coverp0001011000001
theorem coverp000101100000 : Covers (-703761639/2000000 : ℚ) vp000101100000 := join_branches bp0001011000000 bp0001011000001
private noncomputable def vp00010110000_0 : Blocks := edgeBlocks% "full/vectors/00010110000-V-0000.bin"
private noncomputable def vp00010110000_1 : Blocks := edgeBlocks% "full/vectors/00010110000-V-0001.bin"
noncomputable def vp00010110000 : Blocks := (Blocks.join vp00010110000_0 vp00010110000_1)
private theorem bp000101100000 : Branch 0 (-703761639/4000000 : ℚ) vp00010110000 := by
  apply branch_left_normalized (c:=vp000101100000) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-703761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/2000000 : ℚ) by norm_num]
  exact coverp000101100000
private noncomputable def ep000101100001_0 : Blocks := edgeBlocks% "full/vectors/000101100001-E-0000.bin"
private noncomputable def ep000101100001_1 : Blocks := edgeBlocks% "full/vectors/000101100001-E-0001.bin"
noncomputable def ep000101100001 : Blocks := (Blocks.join ep000101100001_0 ep000101100001_1)
private theorem idp000101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110000.list =
    C ((2:ℤ)^182) * horner X vp000101100001.list + horner X ep000101100001.list := by
  exact edge_identity (B := (2:ℤ)^351) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101100001 : Branch 1 (-703761639/4000000 : ℚ) vp00010110000 := by
  apply branch_checked idp000101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-705761639/2000000 : ℚ) by norm_num]
  exact coverp000101100001
theorem coverp00010110000 : Covers (-703761639/4000000 : ℚ) vp00010110000 := join_branches bp000101100000 bp000101100001
private noncomputable def vp0001011000_0 : Blocks := edgeBlocks% "full/vectors/0001011000-V-0000.bin"
private noncomputable def vp0001011000_1 : Blocks := edgeBlocks% "full/vectors/0001011000-V-0001.bin"
private noncomputable def vp0001011000_2 : Blocks := edgeBlocks% "full/vectors/0001011000-V-0002.bin"
noncomputable def vp0001011000 : Blocks := (Blocks.join vp0001011000_0 (Blocks.join vp0001011000_1 vp0001011000_2))
private theorem bp00010110000 : Branch 0 (-703761639/8000000 : ℚ) vp0001011000 := by
  apply branch_left_normalized (c:=vp00010110000) (k:=0) (m:=170) (by decide +kernel)
  rw [show 2*(-703761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/4000000 : ℚ) by norm_num]
  exact coverp00010110000
private noncomputable def ep00010110001_0 : Blocks := edgeBlocks% "full/vectors/00010110001-E-0000.bin"
private noncomputable def ep00010110001_1 : Blocks := edgeBlocks% "full/vectors/00010110001-E-0001.bin"
private noncomputable def ep00010110001_2 : Blocks := edgeBlocks% "full/vectors/00010110001-E-0002.bin"
noncomputable def ep00010110001 : Blocks := (Blocks.join ep00010110001_0 (Blocks.join ep00010110001_1 ep00010110001_2))
private theorem idp00010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011000.list =
    C ((2:ℤ)^342) * horner X vp00010110001.list + horner X ep00010110001.list := by
  exact edge_identity (B := (2:ℤ)^578) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010110001 : Branch 1 (-703761639/8000000 : ℚ) vp0001011000 := by
  apply branch_checked idp00010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-707761639/4000000 : ℚ) by norm_num]
  exact coverp00010110001
theorem coverp0001011000 : Covers (-703761639/8000000 : ℚ) vp0001011000 := join_branches bp00010110000 bp00010110001
private noncomputable def vp000101100_0 : Blocks := edgeBlocks% "full/vectors/000101100-V-0000.bin"
private noncomputable def vp000101100_1 : Blocks := edgeBlocks% "full/vectors/000101100-V-0001.bin"
private noncomputable def vp000101100_2 : Blocks := edgeBlocks% "full/vectors/000101100-V-0002.bin"
private noncomputable def vp000101100_3 : Blocks := edgeBlocks% "full/vectors/000101100-V-0003.bin"
private noncomputable def vp000101100_4 : Blocks := edgeBlocks% "full/vectors/000101100-V-0004.bin"
noncomputable def vp000101100 : Blocks := (Blocks.join (Blocks.join vp000101100_0 vp000101100_1) (Blocks.join vp000101100_2 (Blocks.join vp000101100_3 vp000101100_4)))
private theorem bp0001011000 : Branch 0 (-703761639/16000000 : ℚ) vp000101100 := by
  apply branch_left_normalized (c:=vp0001011000) (k:=0) (m:=318) (by decide +kernel)
  rw [show 2*(-703761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/8000000 : ℚ) by norm_num]
  exact coverp0001011000
private noncomputable def ep0001011001_0 : Blocks := edgeBlocks% "full/vectors/0001011001-E-0000.bin"
private noncomputable def ep0001011001_1 : Blocks := edgeBlocks% "full/vectors/0001011001-E-0001.bin"
private noncomputable def ep0001011001_2 : Blocks := edgeBlocks% "full/vectors/0001011001-E-0002.bin"
private noncomputable def ep0001011001_3 : Blocks := edgeBlocks% "full/vectors/0001011001-E-0003.bin"
private noncomputable def ep0001011001_4 : Blocks := edgeBlocks% "full/vectors/0001011001-E-0004.bin"
noncomputable def ep0001011001 : Blocks := (Blocks.join (Blocks.join ep0001011001_0 ep0001011001_1) (Blocks.join ep0001011001_2 (Blocks.join ep0001011001_3 ep0001011001_4)))
private theorem idp0001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101100.list =
    C ((2:ℤ)^658) * horner X vp0001011001.list + horner X ep0001011001.list := by
  exact edge_identity (B := (2:ℤ)^1027) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011001 : Branch 1 (-703761639/16000000 : ℚ) vp000101100 := by
  apply branch_checked idp0001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-711761639/8000000 : ℚ) by norm_num]
  exact coverp0001011001
theorem coverp000101100 : Covers (-703761639/16000000 : ℚ) vp000101100 := join_branches bp0001011000 bp0001011001
private noncomputable def vp00010110_0 : Blocks := edgeBlocks% "full/vectors/00010110-V-0000.bin"
private noncomputable def vp00010110_1 : Blocks := edgeBlocks% "full/vectors/00010110-V-0001.bin"
private noncomputable def vp00010110_2 : Blocks := edgeBlocks% "full/vectors/00010110-V-0002.bin"
private noncomputable def vp00010110_3 : Blocks := edgeBlocks% "full/vectors/00010110-V-0003.bin"
private noncomputable def vp00010110_4 : Blocks := edgeBlocks% "full/vectors/00010110-V-0004.bin"
private noncomputable def vp00010110_5 : Blocks := edgeBlocks% "full/vectors/00010110-V-0005.bin"
private noncomputable def vp00010110_6 : Blocks := edgeBlocks% "full/vectors/00010110-V-0006.bin"
private noncomputable def vp00010110_7 : Blocks := edgeBlocks% "full/vectors/00010110-V-0007.bin"
private noncomputable def vp00010110_8 : Blocks := edgeBlocks% "full/vectors/00010110-V-0008.bin"
private noncomputable def vp00010110_9 : Blocks := edgeBlocks% "full/vectors/00010110-V-0009.bin"
noncomputable def vp00010110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010110_0 vp00010110_1) (Blocks.join vp00010110_2 (Blocks.join vp00010110_3 vp00010110_4))) (Blocks.join (Blocks.join vp00010110_5 vp00010110_6) (Blocks.join vp00010110_7 (Blocks.join vp00010110_8 vp00010110_9))))
private theorem bp000101100 : Branch 0 (-703761639/32000000 : ℚ) vp00010110 := by
  apply branch_left_normalized (c:=vp000101100) (k:=0) (m:=611) (by decide +kernel)
  rw [show 2*(-703761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/16000000 : ℚ) by norm_num]
  exact coverp000101100
private noncomputable def ep000101101_0 : Blocks := edgeBlocks% "full/vectors/000101101-E-0000.bin"
private noncomputable def ep000101101_1 : Blocks := edgeBlocks% "full/vectors/000101101-E-0001.bin"
private noncomputable def ep000101101_2 : Blocks := edgeBlocks% "full/vectors/000101101-E-0002.bin"
private noncomputable def ep000101101_3 : Blocks := edgeBlocks% "full/vectors/000101101-E-0003.bin"
private noncomputable def ep000101101_4 : Blocks := edgeBlocks% "full/vectors/000101101-E-0004.bin"
private noncomputable def ep000101101_5 : Blocks := edgeBlocks% "full/vectors/000101101-E-0005.bin"
private noncomputable def ep000101101_6 : Blocks := edgeBlocks% "full/vectors/000101101-E-0006.bin"
private noncomputable def ep000101101_7 : Blocks := edgeBlocks% "full/vectors/000101101-E-0007.bin"
private noncomputable def ep000101101_8 : Blocks := edgeBlocks% "full/vectors/000101101-E-0008.bin"
private noncomputable def ep000101101_9 : Blocks := edgeBlocks% "full/vectors/000101101-E-0009.bin"
noncomputable def ep000101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000101101_0 ep000101101_1) (Blocks.join ep000101101_2 (Blocks.join ep000101101_3 ep000101101_4))) (Blocks.join (Blocks.join ep000101101_5 ep000101101_6) (Blocks.join ep000101101_7 (Blocks.join ep000101101_8 ep000101101_9))))
private theorem idp000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010110.list =
    C ((2:ℤ)^1281) * horner X vp000101101.list + horner X ep000101101.list := by
  exact edge_identity (B := (2:ℤ)^1916) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101101 : Branch 1 (-703761639/32000000 : ℚ) vp00010110 := by
  apply branch_checked idp000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-719761639/16000000 : ℚ) by norm_num]
  exact coverp000101101
theorem coverp00010110 : Covers (-703761639/32000000 : ℚ) vp00010110 := join_branches bp000101100 bp000101101
private noncomputable def vp0001011_0 : Blocks := edgeBlocks% "full/vectors/0001011-V-0000.bin"
private noncomputable def vp0001011_1 : Blocks := edgeBlocks% "full/vectors/0001011-V-0001.bin"
private noncomputable def vp0001011_2 : Blocks := edgeBlocks% "full/vectors/0001011-V-0002.bin"
private noncomputable def vp0001011_3 : Blocks := edgeBlocks% "full/vectors/0001011-V-0003.bin"
private noncomputable def vp0001011_4 : Blocks := edgeBlocks% "full/vectors/0001011-V-0004.bin"
private noncomputable def vp0001011_5 : Blocks := edgeBlocks% "full/vectors/0001011-V-0005.bin"
private noncomputable def vp0001011_6 : Blocks := edgeBlocks% "full/vectors/0001011-V-0006.bin"
private noncomputable def vp0001011_7 : Blocks := edgeBlocks% "full/vectors/0001011-V-0007.bin"
private noncomputable def vp0001011_8 : Blocks := edgeBlocks% "full/vectors/0001011-V-0008.bin"
private noncomputable def vp0001011_9 : Blocks := edgeBlocks% "full/vectors/0001011-V-0009.bin"
private noncomputable def vp0001011_10 : Blocks := edgeBlocks% "full/vectors/0001011-V-0010.bin"
private noncomputable def vp0001011_11 : Blocks := edgeBlocks% "full/vectors/0001011-V-0011.bin"
private noncomputable def vp0001011_12 : Blocks := edgeBlocks% "full/vectors/0001011-V-0012.bin"
private noncomputable def vp0001011_13 : Blocks := edgeBlocks% "full/vectors/0001011-V-0013.bin"
private noncomputable def vp0001011_14 : Blocks := edgeBlocks% "full/vectors/0001011-V-0014.bin"
private noncomputable def vp0001011_15 : Blocks := edgeBlocks% "full/vectors/0001011-V-0015.bin"
private noncomputable def vp0001011_16 : Blocks := edgeBlocks% "full/vectors/0001011-V-0016.bin"
private noncomputable def vp0001011_17 : Blocks := edgeBlocks% "full/vectors/0001011-V-0017.bin"
private noncomputable def vp0001011_18 : Blocks := edgeBlocks% "full/vectors/0001011-V-0018.bin"
noncomputable def vp0001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001011_0 vp0001011_1) (Blocks.join vp0001011_2 vp0001011_3)) (Blocks.join (Blocks.join vp0001011_4 vp0001011_5) (Blocks.join vp0001011_6 (Blocks.join vp0001011_7 vp0001011_8)))) (Blocks.join (Blocks.join (Blocks.join vp0001011_9 vp0001011_10) (Blocks.join vp0001011_11 (Blocks.join vp0001011_12 vp0001011_13))) (Blocks.join (Blocks.join vp0001011_14 vp0001011_15) (Blocks.join vp0001011_16 (Blocks.join vp0001011_17 vp0001011_18)))))
private theorem bp00010110 : Branch 0 (-703761639/64000000 : ℚ) vp0001011 := by
  apply branch_left_normalized (c:=vp00010110) (k:=0) (m:=1188) (by decide +kernel)
  rw [show 2*(-703761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-703761639/32000000 : ℚ) by norm_num]
  exact coverp00010110
private noncomputable def ep00010111_0 : Blocks := edgeBlocks% "full/vectors/00010111-E-0000.bin"
private noncomputable def ep00010111_1 : Blocks := edgeBlocks% "full/vectors/00010111-E-0001.bin"
private noncomputable def ep00010111_2 : Blocks := edgeBlocks% "full/vectors/00010111-E-0002.bin"
private noncomputable def ep00010111_3 : Blocks := edgeBlocks% "full/vectors/00010111-E-0003.bin"
private noncomputable def ep00010111_4 : Blocks := edgeBlocks% "full/vectors/00010111-E-0004.bin"
private noncomputable def ep00010111_5 : Blocks := edgeBlocks% "full/vectors/00010111-E-0005.bin"
private noncomputable def ep00010111_6 : Blocks := edgeBlocks% "full/vectors/00010111-E-0006.bin"
private noncomputable def ep00010111_7 : Blocks := edgeBlocks% "full/vectors/00010111-E-0007.bin"
private noncomputable def ep00010111_8 : Blocks := edgeBlocks% "full/vectors/00010111-E-0008.bin"
private noncomputable def ep00010111_9 : Blocks := edgeBlocks% "full/vectors/00010111-E-0009.bin"
private noncomputable def ep00010111_10 : Blocks := edgeBlocks% "full/vectors/00010111-E-0010.bin"
private noncomputable def ep00010111_11 : Blocks := edgeBlocks% "full/vectors/00010111-E-0011.bin"
private noncomputable def ep00010111_12 : Blocks := edgeBlocks% "full/vectors/00010111-E-0012.bin"
private noncomputable def ep00010111_13 : Blocks := edgeBlocks% "full/vectors/00010111-E-0013.bin"
private noncomputable def ep00010111_14 : Blocks := edgeBlocks% "full/vectors/00010111-E-0014.bin"
private noncomputable def ep00010111_15 : Blocks := edgeBlocks% "full/vectors/00010111-E-0015.bin"
private noncomputable def ep00010111_16 : Blocks := edgeBlocks% "full/vectors/00010111-E-0016.bin"
private noncomputable def ep00010111_17 : Blocks := edgeBlocks% "full/vectors/00010111-E-0017.bin"
private noncomputable def ep00010111_18 : Blocks := edgeBlocks% "full/vectors/00010111-E-0018.bin"
noncomputable def ep00010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00010111_0 ep00010111_1) (Blocks.join ep00010111_2 ep00010111_3)) (Blocks.join (Blocks.join ep00010111_4 ep00010111_5) (Blocks.join ep00010111_6 (Blocks.join ep00010111_7 ep00010111_8)))) (Blocks.join (Blocks.join (Blocks.join ep00010111_9 ep00010111_10) (Blocks.join ep00010111_11 (Blocks.join ep00010111_12 ep00010111_13))) (Blocks.join (Blocks.join ep00010111_14 ep00010111_15) (Blocks.join ep00010111_16 (Blocks.join ep00010111_17 ep00010111_18)))))
private theorem idp00010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011.list =
    C ((2:ℤ)^2502) * horner X vp00010111.list + horner X ep00010111.list := by
  exact edge_identity (B := (2:ℤ)^3656) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111 : Branch 1 (-703761639/64000000 : ℚ) vp0001011 := by
  apply branch_checked idp00010111 (by positivity) (by decide +kernel)
  rw [show 2*(-703761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-735761639/32000000 : ℚ) by norm_num]
  exact coverp00010111
theorem coverp0001011 : Covers (-703761639/64000000 : ℚ) vp0001011 := join_branches bp00010110 bp00010111
end NextProof.EdgeFull

