import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000011111111-V-0000.bin"
noncomputable def vp00000011111111 : Blocks := vp00000011111111_0
theorem coverp00000011111111 : Covers (-127261639/500000 : ℚ) vp00000011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011111110_0 : Blocks := edgeBlocks% "full/vectors/00000011111110-V-0000.bin"
noncomputable def vp00000011111110 : Blocks := vp00000011111110_0
theorem coverp00000011111110 : Covers (-126761639/500000 : ℚ) vp00000011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000001111111-V-0000.bin"
noncomputable def vp0000001111111 : Blocks := vp0000001111111_0
private theorem bp00000011111110 : Branch 0 (-126761639/1000000 : ℚ) vp0000001111111 := by
  apply branch_left_normalized (c:=vp00000011111110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-126761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-126761639/500000 : ℚ) by norm_num]
  exact coverp00000011111110
private noncomputable def ep00000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000011111111-E-0000.bin"
noncomputable def ep00000011111111 : Blocks := ep00000011111111_0
private theorem idp00000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111111.list =
    C ((2:ℤ)^105) * horner X vp00000011111111.list + horner X ep00000011111111.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011111111 : Branch 1 (-126761639/1000000 : ℚ) vp0000001111111 := by
  apply branch_checked idp00000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-126761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-127261639/500000 : ℚ) by norm_num]
  exact coverp00000011111111
theorem coverp0000001111111 : Covers (-126761639/1000000 : ℚ) vp0000001111111 := join_branches bp00000011111110 bp00000011111111
private noncomputable def vp00000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000011111101-V-0000.bin"
noncomputable def vp00000011111101 : Blocks := vp00000011111101_0
theorem coverp00000011111101 : Covers (-126261639/500000 : ℚ) vp00000011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011111100_0 : Blocks := edgeBlocks% "full/vectors/00000011111100-V-0000.bin"
noncomputable def vp00000011111100 : Blocks := vp00000011111100_0
theorem coverp00000011111100 : Covers (-125761639/500000 : ℚ) vp00000011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111110_0 : Blocks := edgeBlocks% "full/vectors/0000001111110-V-0000.bin"
noncomputable def vp0000001111110 : Blocks := vp0000001111110_0
private theorem bp00000011111100 : Branch 0 (-125761639/1000000 : ℚ) vp0000001111110 := by
  apply branch_left_normalized (c:=vp00000011111100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-125761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-125761639/500000 : ℚ) by norm_num]
  exact coverp00000011111100
private noncomputable def ep00000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000011111101-E-0000.bin"
noncomputable def ep00000011111101 : Blocks := ep00000011111101_0
private theorem idp00000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111110.list =
    C ((2:ℤ)^106) * horner X vp00000011111101.list + horner X ep00000011111101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011111101 : Branch 1 (-125761639/1000000 : ℚ) vp0000001111110 := by
  apply branch_checked idp00000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-125761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-126261639/500000 : ℚ) by norm_num]
  exact coverp00000011111101
theorem coverp0000001111110 : Covers (-125761639/1000000 : ℚ) vp0000001111110 := join_branches bp00000011111100 bp00000011111101
private noncomputable def vp000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000111111-V-0000.bin"
private noncomputable def vp000000111111_1 : Blocks := edgeBlocks% "full/vectors/000000111111-V-0001.bin"
noncomputable def vp000000111111 : Blocks := (Blocks.join vp000000111111_0 vp000000111111_1)
private theorem bp0000001111110 : Branch 0 (-125761639/2000000 : ℚ) vp000000111111 := by
  apply branch_left_normalized (c:=vp0000001111110) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-125761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-125761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111110
private noncomputable def ep0000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000001111111-E-0000.bin"
private noncomputable def ep0000001111111_1 : Blocks := edgeBlocks% "full/vectors/0000001111111-E-0001.bin"
noncomputable def ep0000001111111 : Blocks := (Blocks.join ep0000001111111_0 ep0000001111111_1)
private theorem idp0000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111111.list =
    C ((2:ℤ)^196) * horner X vp0000001111111.list + horner X ep0000001111111.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001111111 : Branch 1 (-125761639/2000000 : ℚ) vp000000111111 := by
  apply branch_checked idp0000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-125761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-126761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111111
theorem coverp000000111111 : Covers (-125761639/2000000 : ℚ) vp000000111111 := join_branches bp0000001111110 bp0000001111111
private noncomputable def vp00000011111011_0 : Blocks := edgeBlocks% "full/vectors/00000011111011-V-0000.bin"
noncomputable def vp00000011111011 : Blocks := vp00000011111011_0
theorem coverp00000011111011 : Covers (-125261639/500000 : ℚ) vp00000011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011111010_0 : Blocks := edgeBlocks% "full/vectors/00000011111010-V-0000.bin"
noncomputable def vp00000011111010 : Blocks := vp00000011111010_0
theorem coverp00000011111010 : Covers (-124761639/500000 : ℚ) vp00000011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000001111101-V-0000.bin"
noncomputable def vp0000001111101 : Blocks := vp0000001111101_0
private theorem bp00000011111010 : Branch 0 (-124761639/1000000 : ℚ) vp0000001111101 := by
  apply branch_left_normalized (c:=vp00000011111010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-124761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-124761639/500000 : ℚ) by norm_num]
  exact coverp00000011111010
private noncomputable def ep00000011111011_0 : Blocks := edgeBlocks% "full/vectors/00000011111011-E-0000.bin"
noncomputable def ep00000011111011 : Blocks := ep00000011111011_0
private theorem idp00000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111101.list =
    C ((2:ℤ)^106) * horner X vp00000011111011.list + horner X ep00000011111011.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011111011 : Branch 1 (-124761639/1000000 : ℚ) vp0000001111101 := by
  apply branch_checked idp00000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-124761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-125261639/500000 : ℚ) by norm_num]
  exact coverp00000011111011
theorem coverp0000001111101 : Covers (-124761639/1000000 : ℚ) vp0000001111101 := join_branches bp00000011111010 bp00000011111011
private noncomputable def vp00000011111001_0 : Blocks := edgeBlocks% "full/vectors/00000011111001-V-0000.bin"
noncomputable def vp00000011111001 : Blocks := vp00000011111001_0
theorem coverp00000011111001 : Covers (-124261639/500000 : ℚ) vp00000011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011111000_0 : Blocks := edgeBlocks% "full/vectors/00000011111000-V-0000.bin"
noncomputable def vp00000011111000 : Blocks := vp00000011111000_0
theorem coverp00000011111000 : Covers (-123761639/500000 : ℚ) vp00000011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111100_0 : Blocks := edgeBlocks% "full/vectors/0000001111100-V-0000.bin"
noncomputable def vp0000001111100 : Blocks := vp0000001111100_0
private theorem bp00000011111000 : Branch 0 (-123761639/1000000 : ℚ) vp0000001111100 := by
  apply branch_left_normalized (c:=vp00000011111000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-123761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-123761639/500000 : ℚ) by norm_num]
  exact coverp00000011111000
private noncomputable def ep00000011111001_0 : Blocks := edgeBlocks% "full/vectors/00000011111001-E-0000.bin"
noncomputable def ep00000011111001 : Blocks := ep00000011111001_0
private theorem idp00000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111100.list =
    C ((2:ℤ)^107) * horner X vp00000011111001.list + horner X ep00000011111001.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011111001 : Branch 1 (-123761639/1000000 : ℚ) vp0000001111100 := by
  apply branch_checked idp00000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-123761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-124261639/500000 : ℚ) by norm_num]
  exact coverp00000011111001
theorem coverp0000001111100 : Covers (-123761639/1000000 : ℚ) vp0000001111100 := join_branches bp00000011111000 bp00000011111001
private noncomputable def vp000000111110_0 : Blocks := edgeBlocks% "full/vectors/000000111110-V-0000.bin"
private noncomputable def vp000000111110_1 : Blocks := edgeBlocks% "full/vectors/000000111110-V-0001.bin"
noncomputable def vp000000111110 : Blocks := (Blocks.join vp000000111110_0 vp000000111110_1)
private theorem bp0000001111100 : Branch 0 (-123761639/2000000 : ℚ) vp000000111110 := by
  apply branch_left_normalized (c:=vp0000001111100) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-123761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-123761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111100
private noncomputable def ep0000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000001111101-E-0000.bin"
private noncomputable def ep0000001111101_1 : Blocks := edgeBlocks% "full/vectors/0000001111101-E-0001.bin"
noncomputable def ep0000001111101 : Blocks := (Blocks.join ep0000001111101_0 ep0000001111101_1)
private theorem idp0000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111110.list =
    C ((2:ℤ)^198) * horner X vp0000001111101.list + horner X ep0000001111101.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001111101 : Branch 1 (-123761639/2000000 : ℚ) vp000000111110 := by
  apply branch_checked idp0000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-123761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-124761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111101
theorem coverp000000111110 : Covers (-123761639/2000000 : ℚ) vp000000111110 := join_branches bp0000001111100 bp0000001111101
private noncomputable def vp00000011111_0 : Blocks := edgeBlocks% "full/vectors/00000011111-V-0000.bin"
private noncomputable def vp00000011111_1 : Blocks := edgeBlocks% "full/vectors/00000011111-V-0001.bin"
private noncomputable def vp00000011111_2 : Blocks := edgeBlocks% "full/vectors/00000011111-V-0002.bin"
noncomputable def vp00000011111 : Blocks := (Blocks.join vp00000011111_0 (Blocks.join vp00000011111_1 vp00000011111_2))
private theorem bp000000111110 : Branch 0 (-123761639/4000000 : ℚ) vp00000011111 := by
  apply branch_left_normalized (c:=vp000000111110) (k:=0) (m:=191) (by decide +kernel)
  rw [show 2*(-123761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-123761639/2000000 : ℚ) by norm_num]
  exact coverp000000111110
private noncomputable def ep000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000111111-E-0000.bin"
private noncomputable def ep000000111111_1 : Blocks := edgeBlocks% "full/vectors/000000111111-E-0001.bin"
private noncomputable def ep000000111111_2 : Blocks := edgeBlocks% "full/vectors/000000111111-E-0002.bin"
noncomputable def ep000000111111 : Blocks := (Blocks.join ep000000111111_0 (Blocks.join ep000000111111_1 ep000000111111_2))
private theorem idp000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011111.list =
    C ((2:ℤ)^379) * horner X vp000000111111.list + horner X ep000000111111.list := by
  exact edge_identity (B := (2:ℤ)^644) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111111 : Branch 1 (-123761639/4000000 : ℚ) vp00000011111 := by
  apply branch_checked idp000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-123761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-125761639/2000000 : ℚ) by norm_num]
  exact coverp000000111111
theorem coverp00000011111 : Covers (-123761639/4000000 : ℚ) vp00000011111 := join_branches bp000000111110 bp000000111111
private noncomputable def vp00000011110111_0 : Blocks := edgeBlocks% "full/vectors/00000011110111-V-0000.bin"
noncomputable def vp00000011110111 : Blocks := vp00000011110111_0
theorem coverp00000011110111 : Covers (-123261639/500000 : ℚ) vp00000011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011110110_0 : Blocks := edgeBlocks% "full/vectors/00000011110110-V-0000.bin"
noncomputable def vp00000011110110 : Blocks := vp00000011110110_0
theorem coverp00000011110110 : Covers (-122761639/500000 : ℚ) vp00000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111011_0 : Blocks := edgeBlocks% "full/vectors/0000001111011-V-0000.bin"
noncomputable def vp0000001111011 : Blocks := vp0000001111011_0
private theorem bp00000011110110 : Branch 0 (-122761639/1000000 : ℚ) vp0000001111011 := by
  apply branch_left_normalized (c:=vp00000011110110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-122761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-122761639/500000 : ℚ) by norm_num]
  exact coverp00000011110110
private noncomputable def ep00000011110111_0 : Blocks := edgeBlocks% "full/vectors/00000011110111-E-0000.bin"
noncomputable def ep00000011110111 : Blocks := ep00000011110111_0
private theorem idp00000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111011.list =
    C ((2:ℤ)^108) * horner X vp00000011110111.list + horner X ep00000011110111.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011110111 : Branch 1 (-122761639/1000000 : ℚ) vp0000001111011 := by
  apply branch_checked idp00000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-122761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-123261639/500000 : ℚ) by norm_num]
  exact coverp00000011110111
theorem coverp0000001111011 : Covers (-122761639/1000000 : ℚ) vp0000001111011 := join_branches bp00000011110110 bp00000011110111
private noncomputable def vp00000011110101_0 : Blocks := edgeBlocks% "full/vectors/00000011110101-V-0000.bin"
noncomputable def vp00000011110101 : Blocks := vp00000011110101_0
theorem coverp00000011110101 : Covers (-122261639/500000 : ℚ) vp00000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011110100_0 : Blocks := edgeBlocks% "full/vectors/00000011110100-V-0000.bin"
noncomputable def vp00000011110100 : Blocks := vp00000011110100_0
theorem coverp00000011110100 : Covers (-121761639/500000 : ℚ) vp00000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111010_0 : Blocks := edgeBlocks% "full/vectors/0000001111010-V-0000.bin"
noncomputable def vp0000001111010 : Blocks := vp0000001111010_0
private theorem bp00000011110100 : Branch 0 (-121761639/1000000 : ℚ) vp0000001111010 := by
  apply branch_left_normalized (c:=vp00000011110100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-121761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-121761639/500000 : ℚ) by norm_num]
  exact coverp00000011110100
private noncomputable def ep00000011110101_0 : Blocks := edgeBlocks% "full/vectors/00000011110101-E-0000.bin"
noncomputable def ep00000011110101 : Blocks := ep00000011110101_0
private theorem idp00000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111010.list =
    C ((2:ℤ)^108) * horner X vp00000011110101.list + horner X ep00000011110101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011110101 : Branch 1 (-121761639/1000000 : ℚ) vp0000001111010 := by
  apply branch_checked idp00000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-121761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-122261639/500000 : ℚ) by norm_num]
  exact coverp00000011110101
theorem coverp0000001111010 : Covers (-121761639/1000000 : ℚ) vp0000001111010 := join_branches bp00000011110100 bp00000011110101
private noncomputable def vp000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000111101-V-0000.bin"
private noncomputable def vp000000111101_1 : Blocks := edgeBlocks% "full/vectors/000000111101-V-0001.bin"
noncomputable def vp000000111101 : Blocks := (Blocks.join vp000000111101_0 vp000000111101_1)
private theorem bp0000001111010 : Branch 0 (-121761639/2000000 : ℚ) vp000000111101 := by
  apply branch_left_normalized (c:=vp0000001111010) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-121761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-121761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111010
private noncomputable def ep0000001111011_0 : Blocks := edgeBlocks% "full/vectors/0000001111011-E-0000.bin"
private noncomputable def ep0000001111011_1 : Blocks := edgeBlocks% "full/vectors/0000001111011-E-0001.bin"
noncomputable def ep0000001111011 : Blocks := (Blocks.join ep0000001111011_0 ep0000001111011_1)
private theorem idp0000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111101.list =
    C ((2:ℤ)^201) * horner X vp0000001111011.list + horner X ep0000001111011.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001111011 : Branch 1 (-121761639/2000000 : ℚ) vp000000111101 := by
  apply branch_checked idp0000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-121761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-122761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111011
theorem coverp000000111101 : Covers (-121761639/2000000 : ℚ) vp000000111101 := join_branches bp0000001111010 bp0000001111011
private noncomputable def vp00000011110011_0 : Blocks := edgeBlocks% "full/vectors/00000011110011-V-0000.bin"
noncomputable def vp00000011110011 : Blocks := vp00000011110011_0
theorem coverp00000011110011 : Covers (-121261639/500000 : ℚ) vp00000011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011110010_0 : Blocks := edgeBlocks% "full/vectors/00000011110010-V-0000.bin"
noncomputable def vp00000011110010 : Blocks := vp00000011110010_0
theorem coverp00000011110010 : Covers (-120761639/500000 : ℚ) vp00000011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001111001_0 : Blocks := edgeBlocks% "full/vectors/0000001111001-V-0000.bin"
noncomputable def vp0000001111001 : Blocks := vp0000001111001_0
private theorem bp00000011110010 : Branch 0 (-120761639/1000000 : ℚ) vp0000001111001 := by
  apply branch_left_normalized (c:=vp00000011110010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-120761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-120761639/500000 : ℚ) by norm_num]
  exact coverp00000011110010
private noncomputable def ep00000011110011_0 : Blocks := edgeBlocks% "full/vectors/00000011110011-E-0000.bin"
noncomputable def ep00000011110011 : Blocks := ep00000011110011_0
private theorem idp00000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111001.list =
    C ((2:ℤ)^111) * horner X vp00000011110011.list + horner X ep00000011110011.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011110011 : Branch 1 (-120761639/1000000 : ℚ) vp0000001111001 := by
  apply branch_checked idp00000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-120761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-121261639/500000 : ℚ) by norm_num]
  exact coverp00000011110011
theorem coverp0000001111001 : Covers (-120761639/1000000 : ℚ) vp0000001111001 := join_branches bp00000011110010 bp00000011110011
private noncomputable def vp000000111100011_0 : Blocks := edgeBlocks% "full/vectors/000000111100011-V-0000.bin"
noncomputable def vp000000111100011 : Blocks := vp000000111100011_0
theorem coverp000000111100011 : Covers (-120511639/250000 : ℚ) vp000000111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111100010_0 : Blocks := edgeBlocks% "full/vectors/000000111100010-V-0000.bin"
noncomputable def vp000000111100010 : Blocks := vp000000111100010_0
theorem coverp000000111100010 : Covers (-120261639/250000 : ℚ) vp000000111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011110001_0 : Blocks := edgeBlocks% "full/vectors/00000011110001-V-0000.bin"
noncomputable def vp00000011110001 : Blocks := vp00000011110001_0
private theorem bp000000111100010 : Branch 0 (-120261639/500000 : ℚ) vp00000011110001 := by
  apply branch_left_normalized (c:=vp000000111100010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-120261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-120261639/250000 : ℚ) by norm_num]
  exact coverp000000111100010
private noncomputable def ep000000111100011_0 : Blocks := edgeBlocks% "full/vectors/000000111100011-E-0000.bin"
noncomputable def ep000000111100011 : Blocks := ep000000111100011_0
private theorem idp000000111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011110001.list =
    C ((2:ℤ)^64) * horner X vp000000111100011.list + horner X ep000000111100011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111100011 : Branch 1 (-120261639/500000 : ℚ) vp00000011110001 := by
  apply branch_checked idp000000111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-120261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-120511639/250000 : ℚ) by norm_num]
  exact coverp000000111100011
theorem coverp00000011110001 : Covers (-120261639/500000 : ℚ) vp00000011110001 := join_branches bp000000111100010 bp000000111100011
private noncomputable def vp000000111100001_0 : Blocks := edgeBlocks% "full/vectors/000000111100001-V-0000.bin"
noncomputable def vp000000111100001 : Blocks := vp000000111100001_0
theorem coverp000000111100001 : Covers (-120011639/250000 : ℚ) vp000000111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111100000_0 : Blocks := edgeBlocks% "full/vectors/000000111100000-V-0000.bin"
noncomputable def vp000000111100000 : Blocks := vp000000111100000_0
theorem coverp000000111100000 : Covers (-119761639/250000 : ℚ) vp000000111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011110000_0 : Blocks := edgeBlocks% "full/vectors/00000011110000-V-0000.bin"
noncomputable def vp00000011110000 : Blocks := vp00000011110000_0
private theorem bp000000111100000 : Branch 0 (-119761639/500000 : ℚ) vp00000011110000 := by
  apply branch_left_normalized (c:=vp000000111100000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-119761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-119761639/250000 : ℚ) by norm_num]
  exact coverp000000111100000
private noncomputable def ep000000111100001_0 : Blocks := edgeBlocks% "full/vectors/000000111100001-E-0000.bin"
noncomputable def ep000000111100001 : Blocks := ep000000111100001_0
private theorem idp000000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011110000.list =
    C ((2:ℤ)^65) * horner X vp000000111100001.list + horner X ep000000111100001.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111100001 : Branch 1 (-119761639/500000 : ℚ) vp00000011110000 := by
  apply branch_checked idp000000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-119761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-120011639/250000 : ℚ) by norm_num]
  exact coverp000000111100001
theorem coverp00000011110000 : Covers (-119761639/500000 : ℚ) vp00000011110000 := join_branches bp000000111100000 bp000000111100001
private noncomputable def vp0000001111000_0 : Blocks := edgeBlocks% "full/vectors/0000001111000-V-0000.bin"
noncomputable def vp0000001111000 : Blocks := vp0000001111000_0
private theorem bp00000011110000 : Branch 0 (-119761639/1000000 : ℚ) vp0000001111000 := by
  apply branch_left_normalized (c:=vp00000011110000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-119761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-119761639/500000 : ℚ) by norm_num]
  exact coverp00000011110000
private noncomputable def ep00000011110001_0 : Blocks := edgeBlocks% "full/vectors/00000011110001-E-0000.bin"
noncomputable def ep00000011110001 : Blocks := ep00000011110001_0
private theorem idp00000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111000.list =
    C ((2:ℤ)^114) * horner X vp00000011110001.list + horner X ep00000011110001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011110001 : Branch 1 (-119761639/1000000 : ℚ) vp0000001111000 := by
  apply branch_checked idp00000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-119761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-120261639/500000 : ℚ) by norm_num]
  exact coverp00000011110001
theorem coverp0000001111000 : Covers (-119761639/1000000 : ℚ) vp0000001111000 := join_branches bp00000011110000 bp00000011110001
private noncomputable def vp000000111100_0 : Blocks := edgeBlocks% "full/vectors/000000111100-V-0000.bin"
private noncomputable def vp000000111100_1 : Blocks := edgeBlocks% "full/vectors/000000111100-V-0001.bin"
noncomputable def vp000000111100 : Blocks := (Blocks.join vp000000111100_0 vp000000111100_1)
private theorem bp0000001111000 : Branch 0 (-119761639/2000000 : ℚ) vp000000111100 := by
  apply branch_left_normalized (c:=vp0000001111000) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-119761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-119761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111000
private noncomputable def ep0000001111001_0 : Blocks := edgeBlocks% "full/vectors/0000001111001-E-0000.bin"
private noncomputable def ep0000001111001_1 : Blocks := edgeBlocks% "full/vectors/0000001111001-E-0001.bin"
noncomputable def ep0000001111001 : Blocks := (Blocks.join ep0000001111001_0 ep0000001111001_1)
private theorem idp0000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111100.list =
    C ((2:ℤ)^206) * horner X vp0000001111001.list + horner X ep0000001111001.list := by
  exact edge_identity (B := (2:ℤ)^389) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001111001 : Branch 1 (-119761639/2000000 : ℚ) vp000000111100 := by
  apply branch_checked idp0000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-119761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-120761639/1000000 : ℚ) by norm_num]
  exact coverp0000001111001
theorem coverp000000111100 : Covers (-119761639/2000000 : ℚ) vp000000111100 := join_branches bp0000001111000 bp0000001111001
private noncomputable def vp00000011110_0 : Blocks := edgeBlocks% "full/vectors/00000011110-V-0000.bin"
private noncomputable def vp00000011110_1 : Blocks := edgeBlocks% "full/vectors/00000011110-V-0001.bin"
private noncomputable def vp00000011110_2 : Blocks := edgeBlocks% "full/vectors/00000011110-V-0002.bin"
noncomputable def vp00000011110 : Blocks := (Blocks.join vp00000011110_0 (Blocks.join vp00000011110_1 vp00000011110_2))
private theorem bp000000111100 : Branch 0 (-119761639/4000000 : ℚ) vp00000011110 := by
  apply branch_left_normalized (c:=vp000000111100) (k:=0) (m:=197) (by decide +kernel)
  rw [show 2*(-119761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-119761639/2000000 : ℚ) by norm_num]
  exact coverp000000111100
private noncomputable def ep000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000111101-E-0000.bin"
private noncomputable def ep000000111101_1 : Blocks := edgeBlocks% "full/vectors/000000111101-E-0001.bin"
private noncomputable def ep000000111101_2 : Blocks := edgeBlocks% "full/vectors/000000111101-E-0002.bin"
noncomputable def ep000000111101 : Blocks := (Blocks.join ep000000111101_0 (Blocks.join ep000000111101_1 ep000000111101_2))
private theorem idp000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011110.list =
    C ((2:ℤ)^392) * horner X vp000000111101.list + horner X ep000000111101.list := by
  exact edge_identity (B := (2:ℤ)^662) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111101 : Branch 1 (-119761639/4000000 : ℚ) vp00000011110 := by
  apply branch_checked idp000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-119761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-121761639/2000000 : ℚ) by norm_num]
  exact coverp000000111101
theorem coverp00000011110 : Covers (-119761639/4000000 : ℚ) vp00000011110 := join_branches bp000000111100 bp000000111101
private noncomputable def vp0000001111_0 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0000.bin"
private noncomputable def vp0000001111_1 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0001.bin"
private noncomputable def vp0000001111_2 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0002.bin"
private noncomputable def vp0000001111_3 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0003.bin"
private noncomputable def vp0000001111_4 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0004.bin"
private noncomputable def vp0000001111_5 : Blocks := edgeBlocks% "full/vectors/0000001111-V-0005.bin"
noncomputable def vp0000001111 : Blocks := (Blocks.join (Blocks.join vp0000001111_0 (Blocks.join vp0000001111_1 vp0000001111_2)) (Blocks.join vp0000001111_3 (Blocks.join vp0000001111_4 vp0000001111_5)))
private theorem bp00000011110 : Branch 0 (-119761639/8000000 : ℚ) vp0000001111 := by
  apply branch_left_normalized (c:=vp00000011110) (k:=0) (m:=375) (by decide +kernel)
  rw [show 2*(-119761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-119761639/4000000 : ℚ) by norm_num]
  exact coverp00000011110
private noncomputable def ep00000011111_0 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0000.bin"
private noncomputable def ep00000011111_1 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0001.bin"
private noncomputable def ep00000011111_2 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0002.bin"
private noncomputable def ep00000011111_3 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0003.bin"
private noncomputable def ep00000011111_4 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0004.bin"
private noncomputable def ep00000011111_5 : Blocks := edgeBlocks% "full/vectors/00000011111-E-0005.bin"
noncomputable def ep00000011111 : Blocks := (Blocks.join (Blocks.join ep00000011111_0 (Blocks.join ep00000011111_1 ep00000011111_2)) (Blocks.join ep00000011111_3 (Blocks.join ep00000011111_4 ep00000011111_5)))
private theorem idp00000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001111.list =
    C ((2:ℤ)^759) * horner X vp00000011111.list + horner X ep00000011111.list := by
  exact edge_identity (B := (2:ℤ)^1205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011111 : Branch 1 (-119761639/8000000 : ℚ) vp0000001111 := by
  apply branch_checked idp00000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-119761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-123761639/4000000 : ℚ) by norm_num]
  exact coverp00000011111
theorem coverp0000001111 : Covers (-119761639/8000000 : ℚ) vp0000001111 := join_branches bp00000011110 bp00000011111
private noncomputable def vp000000111011111_0 : Blocks := edgeBlocks% "full/vectors/000000111011111-V-0000.bin"
noncomputable def vp000000111011111 : Blocks := vp000000111011111_0
theorem coverp000000111011111 : Covers (-119511639/250000 : ℚ) vp000000111011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111011110_0 : Blocks := edgeBlocks% "full/vectors/000000111011110-V-0000.bin"
noncomputable def vp000000111011110 : Blocks := vp000000111011110_0
theorem coverp000000111011110 : Covers (-119261639/250000 : ℚ) vp000000111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101111_0 : Blocks := edgeBlocks% "full/vectors/00000011101111-V-0000.bin"
noncomputable def vp00000011101111 : Blocks := vp00000011101111_0
private theorem bp000000111011110 : Branch 0 (-119261639/500000 : ℚ) vp00000011101111 := by
  apply branch_left_normalized (c:=vp000000111011110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-119261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-119261639/250000 : ℚ) by norm_num]
  exact coverp000000111011110
private noncomputable def ep000000111011111_0 : Blocks := edgeBlocks% "full/vectors/000000111011111-E-0000.bin"
noncomputable def ep000000111011111 : Blocks := ep000000111011111_0
private theorem idp000000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101111.list =
    C ((2:ℤ)^67) * horner X vp000000111011111.list + horner X ep000000111011111.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111011111 : Branch 1 (-119261639/500000 : ℚ) vp00000011101111 := by
  apply branch_checked idp000000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-119261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-119511639/250000 : ℚ) by norm_num]
  exact coverp000000111011111
theorem coverp00000011101111 : Covers (-119261639/500000 : ℚ) vp00000011101111 := join_branches bp000000111011110 bp000000111011111
private noncomputable def vp000000111011101_0 : Blocks := edgeBlocks% "full/vectors/000000111011101-V-0000.bin"
noncomputable def vp000000111011101 : Blocks := vp000000111011101_0
theorem coverp000000111011101 : Covers (-119011639/250000 : ℚ) vp000000111011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111011100_0 : Blocks := edgeBlocks% "full/vectors/000000111011100-V-0000.bin"
noncomputable def vp000000111011100 : Blocks := vp000000111011100_0
theorem coverp000000111011100 : Covers (-118761639/250000 : ℚ) vp000000111011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101110_0 : Blocks := edgeBlocks% "full/vectors/00000011101110-V-0000.bin"
noncomputable def vp00000011101110 : Blocks := vp00000011101110_0
private theorem bp000000111011100 : Branch 0 (-118761639/500000 : ℚ) vp00000011101110 := by
  apply branch_left_normalized (c:=vp000000111011100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-118761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-118761639/250000 : ℚ) by norm_num]
  exact coverp000000111011100
private noncomputable def ep000000111011101_0 : Blocks := edgeBlocks% "full/vectors/000000111011101-E-0000.bin"
noncomputable def ep000000111011101 : Blocks := ep000000111011101_0
private theorem idp000000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101110.list =
    C ((2:ℤ)^70) * horner X vp000000111011101.list + horner X ep000000111011101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111011101 : Branch 1 (-118761639/500000 : ℚ) vp00000011101110 := by
  apply branch_checked idp000000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-118761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-119011639/250000 : ℚ) by norm_num]
  exact coverp000000111011101
theorem coverp00000011101110 : Covers (-118761639/500000 : ℚ) vp00000011101110 := join_branches bp000000111011100 bp000000111011101
private noncomputable def vp0000001110111_0 : Blocks := edgeBlocks% "full/vectors/0000001110111-V-0000.bin"
noncomputable def vp0000001110111 : Blocks := vp0000001110111_0
private theorem bp00000011101110 : Branch 0 (-118761639/1000000 : ℚ) vp0000001110111 := by
  apply branch_left_normalized (c:=vp00000011101110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-118761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-118761639/500000 : ℚ) by norm_num]
  exact coverp00000011101110
private noncomputable def ep00000011101111_0 : Blocks := edgeBlocks% "full/vectors/00000011101111-E-0000.bin"
noncomputable def ep00000011101111 : Blocks := ep00000011101111_0
private theorem idp00000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110111.list =
    C ((2:ℤ)^120) * horner X vp00000011101111.list + horner X ep00000011101111.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011101111 : Branch 1 (-118761639/1000000 : ℚ) vp0000001110111 := by
  apply branch_checked idp00000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-118761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-119261639/500000 : ℚ) by norm_num]
  exact coverp00000011101111
theorem coverp0000001110111 : Covers (-118761639/1000000 : ℚ) vp0000001110111 := join_branches bp00000011101110 bp00000011101111
private noncomputable def vp000000111011011_0 : Blocks := edgeBlocks% "full/vectors/000000111011011-V-0000.bin"
noncomputable def vp000000111011011 : Blocks := vp000000111011011_0
theorem coverp000000111011011 : Covers (-118511639/250000 : ℚ) vp000000111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110110101_0 : Blocks := edgeBlocks% "full/vectors/0000001110110101-V-0000.bin"
noncomputable def vp0000001110110101 : Blocks := vp0000001110110101_0
theorem coverp0000001110110101 : Covers (-118386639/125000 : ℚ) vp0000001110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110110100_0 : Blocks := edgeBlocks% "full/vectors/0000001110110100-V-0000.bin"
noncomputable def vp0000001110110100 : Blocks := vp0000001110110100_0
theorem coverp0000001110110100 : Covers (-118261639/125000 : ℚ) vp0000001110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111011010_0 : Blocks := edgeBlocks% "full/vectors/000000111011010-V-0000.bin"
noncomputable def vp000000111011010 : Blocks := vp000000111011010_0
private theorem bp0000001110110100 : Branch 0 (-118261639/250000 : ℚ) vp000000111011010 := by
  apply branch_left_normalized (c:=vp0000001110110100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-118261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-118261639/125000 : ℚ) by norm_num]
  exact coverp0000001110110100
private noncomputable def ep0000001110110101_0 : Blocks := edgeBlocks% "full/vectors/0000001110110101-E-0000.bin"
noncomputable def ep0000001110110101 : Blocks := ep0000001110110101_0
private theorem idp0000001110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111011010.list =
    C ((2:ℤ)^41) * horner X vp0000001110110101.list + horner X ep0000001110110101.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110110101 : Branch 1 (-118261639/250000 : ℚ) vp000000111011010 := by
  apply branch_checked idp0000001110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-118261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-118386639/125000 : ℚ) by norm_num]
  exact coverp0000001110110101
theorem coverp000000111011010 : Covers (-118261639/250000 : ℚ) vp000000111011010 := join_branches bp0000001110110100 bp0000001110110101
private noncomputable def vp00000011101101_0 : Blocks := edgeBlocks% "full/vectors/00000011101101-V-0000.bin"
noncomputable def vp00000011101101 : Blocks := vp00000011101101_0
private theorem bp000000111011010 : Branch 0 (-118261639/500000 : ℚ) vp00000011101101 := by
  apply branch_left_normalized (c:=vp000000111011010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-118261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-118261639/250000 : ℚ) by norm_num]
  exact coverp000000111011010
private noncomputable def ep000000111011011_0 : Blocks := edgeBlocks% "full/vectors/000000111011011-E-0000.bin"
noncomputable def ep000000111011011 : Blocks := ep000000111011011_0
private theorem idp000000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101101.list =
    C ((2:ℤ)^65) * horner X vp000000111011011.list + horner X ep000000111011011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111011011 : Branch 1 (-118261639/500000 : ℚ) vp00000011101101 := by
  apply branch_checked idp000000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-118261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-118511639/250000 : ℚ) by norm_num]
  exact coverp000000111011011
theorem coverp00000011101101 : Covers (-118261639/500000 : ℚ) vp00000011101101 := join_branches bp000000111011010 bp000000111011011
private noncomputable def vp000000111011001_0 : Blocks := edgeBlocks% "full/vectors/000000111011001-V-0000.bin"
noncomputable def vp000000111011001 : Blocks := vp000000111011001_0
theorem coverp000000111011001 : Covers (-118011639/250000 : ℚ) vp000000111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111011000_0 : Blocks := edgeBlocks% "full/vectors/000000111011000-V-0000.bin"
noncomputable def vp000000111011000 : Blocks := vp000000111011000_0
theorem coverp000000111011000 : Covers (-117761639/250000 : ℚ) vp000000111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101100_0 : Blocks := edgeBlocks% "full/vectors/00000011101100-V-0000.bin"
noncomputable def vp00000011101100 : Blocks := vp00000011101100_0
private theorem bp000000111011000 : Branch 0 (-117761639/500000 : ℚ) vp00000011101100 := by
  apply branch_left_normalized (c:=vp000000111011000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-117761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-117761639/250000 : ℚ) by norm_num]
  exact coverp000000111011000
private noncomputable def ep000000111011001_0 : Blocks := edgeBlocks% "full/vectors/000000111011001-E-0000.bin"
noncomputable def ep000000111011001 : Blocks := ep000000111011001_0
private theorem idp000000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101100.list =
    C ((2:ℤ)^66) * horner X vp000000111011001.list + horner X ep000000111011001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111011001 : Branch 1 (-117761639/500000 : ℚ) vp00000011101100 := by
  apply branch_checked idp000000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-117761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-118011639/250000 : ℚ) by norm_num]
  exact coverp000000111011001
theorem coverp00000011101100 : Covers (-117761639/500000 : ℚ) vp00000011101100 := join_branches bp000000111011000 bp000000111011001
private noncomputable def vp0000001110110_0 : Blocks := edgeBlocks% "full/vectors/0000001110110-V-0000.bin"
noncomputable def vp0000001110110 : Blocks := vp0000001110110_0
private theorem bp00000011101100 : Branch 0 (-117761639/1000000 : ℚ) vp0000001110110 := by
  apply branch_left_normalized (c:=vp00000011101100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-117761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-117761639/500000 : ℚ) by norm_num]
  exact coverp00000011101100
private noncomputable def ep00000011101101_0 : Blocks := edgeBlocks% "full/vectors/00000011101101-E-0000.bin"
noncomputable def ep00000011101101 : Blocks := ep00000011101101_0
private theorem idp00000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110110.list =
    C ((2:ℤ)^112) * horner X vp00000011101101.list + horner X ep00000011101101.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011101101 : Branch 1 (-117761639/1000000 : ℚ) vp0000001110110 := by
  apply branch_checked idp00000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-117761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-118261639/500000 : ℚ) by norm_num]
  exact coverp00000011101101
theorem coverp0000001110110 : Covers (-117761639/1000000 : ℚ) vp0000001110110 := join_branches bp00000011101100 bp00000011101101
private noncomputable def vp000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000111011-V-0000.bin"
private noncomputable def vp000000111011_1 : Blocks := edgeBlocks% "full/vectors/000000111011-V-0001.bin"
noncomputable def vp000000111011 : Blocks := (Blocks.join vp000000111011_0 vp000000111011_1)
private theorem bp0000001110110 : Branch 0 (-117761639/2000000 : ℚ) vp000000111011 := by
  apply branch_left_normalized (c:=vp0000001110110) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-117761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-117761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110110
private noncomputable def ep0000001110111_0 : Blocks := edgeBlocks% "full/vectors/0000001110111-E-0000.bin"
private noncomputable def ep0000001110111_1 : Blocks := edgeBlocks% "full/vectors/0000001110111-E-0001.bin"
noncomputable def ep0000001110111 : Blocks := (Blocks.join ep0000001110111_0 ep0000001110111_1)
private theorem idp0000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111011.list =
    C ((2:ℤ)^205) * horner X vp0000001110111.list + horner X ep0000001110111.list := by
  exact edge_identity (B := (2:ℤ)^397) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110111 : Branch 1 (-117761639/2000000 : ℚ) vp000000111011 := by
  apply branch_checked idp0000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-117761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-118761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110111
theorem coverp000000111011 : Covers (-117761639/2000000 : ℚ) vp000000111011 := join_branches bp0000001110110 bp0000001110111
private noncomputable def vp000000111010111_0 : Blocks := edgeBlocks% "full/vectors/000000111010111-V-0000.bin"
noncomputable def vp000000111010111 : Blocks := vp000000111010111_0
theorem coverp000000111010111 : Covers (-117511639/250000 : ℚ) vp000000111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111010110_0 : Blocks := edgeBlocks% "full/vectors/000000111010110-V-0000.bin"
noncomputable def vp000000111010110 : Blocks := vp000000111010110_0
theorem coverp000000111010110 : Covers (-117261639/250000 : ℚ) vp000000111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101011_0 : Blocks := edgeBlocks% "full/vectors/00000011101011-V-0000.bin"
noncomputable def vp00000011101011 : Blocks := vp00000011101011_0
private theorem bp000000111010110 : Branch 0 (-117261639/500000 : ℚ) vp00000011101011 := by
  apply branch_left_normalized (c:=vp000000111010110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-117261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-117261639/250000 : ℚ) by norm_num]
  exact coverp000000111010110
private noncomputable def ep000000111010111_0 : Blocks := edgeBlocks% "full/vectors/000000111010111-E-0000.bin"
noncomputable def ep000000111010111 : Blocks := ep000000111010111_0
private theorem idp000000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101011.list =
    C ((2:ℤ)^67) * horner X vp000000111010111.list + horner X ep000000111010111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111010111 : Branch 1 (-117261639/500000 : ℚ) vp00000011101011 := by
  apply branch_checked idp000000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-117261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-117511639/250000 : ℚ) by norm_num]
  exact coverp000000111010111
theorem coverp00000011101011 : Covers (-117261639/500000 : ℚ) vp00000011101011 := join_branches bp000000111010110 bp000000111010111
private noncomputable def vp000000111010101_0 : Blocks := edgeBlocks% "full/vectors/000000111010101-V-0000.bin"
noncomputable def vp000000111010101 : Blocks := vp000000111010101_0
theorem coverp000000111010101 : Covers (-117011639/250000 : ℚ) vp000000111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111010100_0 : Blocks := edgeBlocks% "full/vectors/000000111010100-V-0000.bin"
noncomputable def vp000000111010100 : Blocks := vp000000111010100_0
theorem coverp000000111010100 : Covers (-116761639/250000 : ℚ) vp000000111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101010_0 : Blocks := edgeBlocks% "full/vectors/00000011101010-V-0000.bin"
noncomputable def vp00000011101010 : Blocks := vp00000011101010_0
private theorem bp000000111010100 : Branch 0 (-116761639/500000 : ℚ) vp00000011101010 := by
  apply branch_left_normalized (c:=vp000000111010100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-116761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-116761639/250000 : ℚ) by norm_num]
  exact coverp000000111010100
private noncomputable def ep000000111010101_0 : Blocks := edgeBlocks% "full/vectors/000000111010101-E-0000.bin"
noncomputable def ep000000111010101 : Blocks := ep000000111010101_0
private theorem idp000000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101010.list =
    C ((2:ℤ)^68) * horner X vp000000111010101.list + horner X ep000000111010101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111010101 : Branch 1 (-116761639/500000 : ℚ) vp00000011101010 := by
  apply branch_checked idp000000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-116761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-117011639/250000 : ℚ) by norm_num]
  exact coverp000000111010101
theorem coverp00000011101010 : Covers (-116761639/500000 : ℚ) vp00000011101010 := join_branches bp000000111010100 bp000000111010101
private noncomputable def vp0000001110101_0 : Blocks := edgeBlocks% "full/vectors/0000001110101-V-0000.bin"
noncomputable def vp0000001110101 : Blocks := vp0000001110101_0
private theorem bp00000011101010 : Branch 0 (-116761639/1000000 : ℚ) vp0000001110101 := by
  apply branch_left_normalized (c:=vp00000011101010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-116761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-116761639/500000 : ℚ) by norm_num]
  exact coverp00000011101010
private noncomputable def ep00000011101011_0 : Blocks := edgeBlocks% "full/vectors/00000011101011-E-0000.bin"
noncomputable def ep00000011101011 : Blocks := ep00000011101011_0
private theorem idp00000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110101.list =
    C ((2:ℤ)^116) * horner X vp00000011101011.list + horner X ep00000011101011.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011101011 : Branch 1 (-116761639/1000000 : ℚ) vp0000001110101 := by
  apply branch_checked idp00000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-116761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-117261639/500000 : ℚ) by norm_num]
  exact coverp00000011101011
theorem coverp0000001110101 : Covers (-116761639/1000000 : ℚ) vp0000001110101 := join_branches bp00000011101010 bp00000011101011
private noncomputable def vp000000111010011_0 : Blocks := edgeBlocks% "full/vectors/000000111010011-V-0000.bin"
noncomputable def vp000000111010011 : Blocks := vp000000111010011_0
theorem coverp000000111010011 : Covers (-116511639/250000 : ℚ) vp000000111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111010010_0 : Blocks := edgeBlocks% "full/vectors/000000111010010-V-0000.bin"
noncomputable def vp000000111010010 : Blocks := vp000000111010010_0
theorem coverp000000111010010 : Covers (-116261639/250000 : ℚ) vp000000111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011101001_0 : Blocks := edgeBlocks% "full/vectors/00000011101001-V-0000.bin"
noncomputable def vp00000011101001 : Blocks := vp00000011101001_0
private theorem bp000000111010010 : Branch 0 (-116261639/500000 : ℚ) vp00000011101001 := by
  apply branch_left_normalized (c:=vp000000111010010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-116261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-116261639/250000 : ℚ) by norm_num]
  exact coverp000000111010010
private noncomputable def ep000000111010011_0 : Blocks := edgeBlocks% "full/vectors/000000111010011-E-0000.bin"
noncomputable def ep000000111010011 : Blocks := ep000000111010011_0
private theorem idp000000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101001.list =
    C ((2:ℤ)^69) * horner X vp000000111010011.list + horner X ep000000111010011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111010011 : Branch 1 (-116261639/500000 : ℚ) vp00000011101001 := by
  apply branch_checked idp000000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-116261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-116511639/250000 : ℚ) by norm_num]
  exact coverp000000111010011
theorem coverp00000011101001 : Covers (-116261639/500000 : ℚ) vp00000011101001 := join_branches bp000000111010010 bp000000111010011
private noncomputable def vp000000111010001_0 : Blocks := edgeBlocks% "full/vectors/000000111010001-V-0000.bin"
noncomputable def vp000000111010001 : Blocks := vp000000111010001_0
theorem coverp000000111010001 : Covers (-116011639/250000 : ℚ) vp000000111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110100001_0 : Blocks := edgeBlocks% "full/vectors/0000001110100001-V-0000.bin"
noncomputable def vp0000001110100001 : Blocks := vp0000001110100001_0
theorem coverp0000001110100001 : Covers (-115886639/125000 : ℚ) vp0000001110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110100000_0 : Blocks := edgeBlocks% "full/vectors/0000001110100000-V-0000.bin"
noncomputable def vp0000001110100000 : Blocks := vp0000001110100000_0
theorem coverp0000001110100000 : Covers (-115761639/125000 : ℚ) vp0000001110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111010000_0 : Blocks := edgeBlocks% "full/vectors/000000111010000-V-0000.bin"
noncomputable def vp000000111010000 : Blocks := vp000000111010000_0
private theorem bp0000001110100000 : Branch 0 (-115761639/250000 : ℚ) vp000000111010000 := by
  apply branch_left_normalized (c:=vp0000001110100000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-115761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-115761639/125000 : ℚ) by norm_num]
  exact coverp0000001110100000
private noncomputable def ep0000001110100001_0 : Blocks := edgeBlocks% "full/vectors/0000001110100001-E-0000.bin"
noncomputable def ep0000001110100001 : Blocks := ep0000001110100001_0
private theorem idp0000001110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111010000.list =
    C ((2:ℤ)^43) * horner X vp0000001110100001.list + horner X ep0000001110100001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110100001 : Branch 1 (-115761639/250000 : ℚ) vp000000111010000 := by
  apply branch_checked idp0000001110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-115761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-115886639/125000 : ℚ) by norm_num]
  exact coverp0000001110100001
theorem coverp000000111010000 : Covers (-115761639/250000 : ℚ) vp000000111010000 := join_branches bp0000001110100000 bp0000001110100001
private noncomputable def vp00000011101000_0 : Blocks := edgeBlocks% "full/vectors/00000011101000-V-0000.bin"
noncomputable def vp00000011101000 : Blocks := vp00000011101000_0
private theorem bp000000111010000 : Branch 0 (-115761639/500000 : ℚ) vp00000011101000 := by
  apply branch_left_normalized (c:=vp000000111010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-115761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-115761639/250000 : ℚ) by norm_num]
  exact coverp000000111010000
private noncomputable def ep000000111010001_0 : Blocks := edgeBlocks% "full/vectors/000000111010001-E-0000.bin"
noncomputable def ep000000111010001 : Blocks := ep000000111010001_0
private theorem idp000000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101000.list =
    C ((2:ℤ)^71) * horner X vp000000111010001.list + horner X ep000000111010001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111010001 : Branch 1 (-115761639/500000 : ℚ) vp00000011101000 := by
  apply branch_checked idp000000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-115761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-116011639/250000 : ℚ) by norm_num]
  exact coverp000000111010001
theorem coverp00000011101000 : Covers (-115761639/500000 : ℚ) vp00000011101000 := join_branches bp000000111010000 bp000000111010001
private noncomputable def vp0000001110100_0 : Blocks := edgeBlocks% "full/vectors/0000001110100-V-0000.bin"
noncomputable def vp0000001110100 : Blocks := vp0000001110100_0
private theorem bp00000011101000 : Branch 0 (-115761639/1000000 : ℚ) vp0000001110100 := by
  apply branch_left_normalized (c:=vp00000011101000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-115761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-115761639/500000 : ℚ) by norm_num]
  exact coverp00000011101000
private noncomputable def ep00000011101001_0 : Blocks := edgeBlocks% "full/vectors/00000011101001-E-0000.bin"
noncomputable def ep00000011101001 : Blocks := ep00000011101001_0
private theorem idp00000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110100.list =
    C ((2:ℤ)^120) * horner X vp00000011101001.list + horner X ep00000011101001.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011101001 : Branch 1 (-115761639/1000000 : ℚ) vp0000001110100 := by
  apply branch_checked idp00000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-115761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-116261639/500000 : ℚ) by norm_num]
  exact coverp00000011101001
theorem coverp0000001110100 : Covers (-115761639/1000000 : ℚ) vp0000001110100 := join_branches bp00000011101000 bp00000011101001
private noncomputable def vp000000111010_0 : Blocks := edgeBlocks% "full/vectors/000000111010-V-0000.bin"
private noncomputable def vp000000111010_1 : Blocks := edgeBlocks% "full/vectors/000000111010-V-0001.bin"
noncomputable def vp000000111010 : Blocks := (Blocks.join vp000000111010_0 vp000000111010_1)
private theorem bp0000001110100 : Branch 0 (-115761639/2000000 : ℚ) vp000000111010 := by
  apply branch_left_normalized (c:=vp0000001110100) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-115761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-115761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110100
private noncomputable def ep0000001110101_0 : Blocks := edgeBlocks% "full/vectors/0000001110101-E-0000.bin"
private noncomputable def ep0000001110101_1 : Blocks := edgeBlocks% "full/vectors/0000001110101-E-0001.bin"
noncomputable def ep0000001110101 : Blocks := (Blocks.join ep0000001110101_0 ep0000001110101_1)
private theorem idp0000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111010.list =
    C ((2:ℤ)^216) * horner X vp0000001110101.list + horner X ep0000001110101.list := by
  exact edge_identity (B := (2:ℤ)^407) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110101 : Branch 1 (-115761639/2000000 : ℚ) vp000000111010 := by
  apply branch_checked idp0000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-115761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-116761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110101
theorem coverp000000111010 : Covers (-115761639/2000000 : ℚ) vp000000111010 := join_branches bp0000001110100 bp0000001110101
private noncomputable def vp00000011101_0 : Blocks := edgeBlocks% "full/vectors/00000011101-V-0000.bin"
private noncomputable def vp00000011101_1 : Blocks := edgeBlocks% "full/vectors/00000011101-V-0001.bin"
private noncomputable def vp00000011101_2 : Blocks := edgeBlocks% "full/vectors/00000011101-V-0002.bin"
private noncomputable def vp00000011101_3 : Blocks := edgeBlocks% "full/vectors/00000011101-V-0003.bin"
noncomputable def vp00000011101 : Blocks := (Blocks.join (Blocks.join vp00000011101_0 vp00000011101_1) (Blocks.join vp00000011101_2 vp00000011101_3))
private theorem bp000000111010 : Branch 0 (-115761639/4000000 : ℚ) vp00000011101 := by
  apply branch_left_normalized (c:=vp000000111010) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-115761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-115761639/2000000 : ℚ) by norm_num]
  exact coverp000000111010
private noncomputable def ep000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000111011-E-0000.bin"
private noncomputable def ep000000111011_1 : Blocks := edgeBlocks% "full/vectors/000000111011-E-0001.bin"
private noncomputable def ep000000111011_2 : Blocks := edgeBlocks% "full/vectors/000000111011-E-0002.bin"
private noncomputable def ep000000111011_3 : Blocks := edgeBlocks% "full/vectors/000000111011-E-0003.bin"
noncomputable def ep000000111011 : Blocks := (Blocks.join (Blocks.join ep000000111011_0 ep000000111011_1) (Blocks.join ep000000111011_2 ep000000111011_3))
private theorem idp000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011101.list =
    C ((2:ℤ)^404) * horner X vp000000111011.list + horner X ep000000111011.list := by
  exact edge_identity (B := (2:ℤ)^685) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111011 : Branch 1 (-115761639/4000000 : ℚ) vp00000011101 := by
  apply branch_checked idp000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-115761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-117761639/2000000 : ℚ) by norm_num]
  exact coverp000000111011
theorem coverp00000011101 : Covers (-115761639/4000000 : ℚ) vp00000011101 := join_branches bp000000111010 bp000000111011
private noncomputable def vp0000001110011111_0 : Blocks := edgeBlocks% "full/vectors/0000001110011111-V-0000.bin"
noncomputable def vp0000001110011111 : Blocks := vp0000001110011111_0
theorem coverp0000001110011111 : Covers (-115636639/125000 : ℚ) vp0000001110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110011110_0 : Blocks := edgeBlocks% "full/vectors/0000001110011110-V-0000.bin"
noncomputable def vp0000001110011110 : Blocks := vp0000001110011110_0
theorem coverp0000001110011110 : Covers (-115511639/125000 : ℚ) vp0000001110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111001111_0 : Blocks := edgeBlocks% "full/vectors/000000111001111-V-0000.bin"
noncomputable def vp000000111001111 : Blocks := vp000000111001111_0
private theorem bp0000001110011110 : Branch 0 (-115511639/250000 : ℚ) vp000000111001111 := by
  apply branch_left_normalized (c:=vp0000001110011110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-115511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-115511639/125000 : ℚ) by norm_num]
  exact coverp0000001110011110
private noncomputable def ep0000001110011111_0 : Blocks := edgeBlocks% "full/vectors/0000001110011111-E-0000.bin"
noncomputable def ep0000001110011111 : Blocks := ep0000001110011111_0
private theorem idp0000001110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111001111.list =
    C ((2:ℤ)^44) * horner X vp0000001110011111.list + horner X ep0000001110011111.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110011111 : Branch 1 (-115511639/250000 : ℚ) vp000000111001111 := by
  apply branch_checked idp0000001110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-115511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-115636639/125000 : ℚ) by norm_num]
  exact coverp0000001110011111
theorem coverp000000111001111 : Covers (-115511639/250000 : ℚ) vp000000111001111 := join_branches bp0000001110011110 bp0000001110011111
private noncomputable def vp0000001110011101_0 : Blocks := edgeBlocks% "full/vectors/0000001110011101-V-0000.bin"
noncomputable def vp0000001110011101 : Blocks := vp0000001110011101_0
theorem coverp0000001110011101 : Covers (-115386639/125000 : ℚ) vp0000001110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110011100_0 : Blocks := edgeBlocks% "full/vectors/0000001110011100-V-0000.bin"
noncomputable def vp0000001110011100 : Blocks := vp0000001110011100_0
theorem coverp0000001110011100 : Covers (-115261639/125000 : ℚ) vp0000001110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111001110_0 : Blocks := edgeBlocks% "full/vectors/000000111001110-V-0000.bin"
noncomputable def vp000000111001110 : Blocks := vp000000111001110_0
private theorem bp0000001110011100 : Branch 0 (-115261639/250000 : ℚ) vp000000111001110 := by
  apply branch_left_normalized (c:=vp0000001110011100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-115261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-115261639/125000 : ℚ) by norm_num]
  exact coverp0000001110011100
private noncomputable def ep0000001110011101_0 : Blocks := edgeBlocks% "full/vectors/0000001110011101-E-0000.bin"
noncomputable def ep0000001110011101 : Blocks := ep0000001110011101_0
private theorem idp0000001110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111001110.list =
    C ((2:ℤ)^44) * horner X vp0000001110011101.list + horner X ep0000001110011101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110011101 : Branch 1 (-115261639/250000 : ℚ) vp000000111001110 := by
  apply branch_checked idp0000001110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-115261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-115386639/125000 : ℚ) by norm_num]
  exact coverp0000001110011101
theorem coverp000000111001110 : Covers (-115261639/250000 : ℚ) vp000000111001110 := join_branches bp0000001110011100 bp0000001110011101
private noncomputable def vp00000011100111_0 : Blocks := edgeBlocks% "full/vectors/00000011100111-V-0000.bin"
noncomputable def vp00000011100111 : Blocks := vp00000011100111_0
private theorem bp000000111001110 : Branch 0 (-115261639/500000 : ℚ) vp00000011100111 := by
  apply branch_left_normalized (c:=vp000000111001110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-115261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-115261639/250000 : ℚ) by norm_num]
  exact coverp000000111001110
private noncomputable def ep000000111001111_0 : Blocks := edgeBlocks% "full/vectors/000000111001111-E-0000.bin"
noncomputable def ep000000111001111 : Blocks := ep000000111001111_0
private theorem idp000000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100111.list =
    C ((2:ℤ)^68) * horner X vp000000111001111.list + horner X ep000000111001111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111001111 : Branch 1 (-115261639/500000 : ℚ) vp00000011100111 := by
  apply branch_checked idp000000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-115261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-115511639/250000 : ℚ) by norm_num]
  exact coverp000000111001111
theorem coverp00000011100111 : Covers (-115261639/500000 : ℚ) vp00000011100111 := join_branches bp000000111001110 bp000000111001111
private noncomputable def vp0000001110011011_0 : Blocks := edgeBlocks% "full/vectors/0000001110011011-V-0000.bin"
noncomputable def vp0000001110011011 : Blocks := vp0000001110011011_0
theorem coverp0000001110011011 : Covers (-115136639/125000 : ℚ) vp0000001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110011010_0 : Blocks := edgeBlocks% "full/vectors/0000001110011010-V-0000.bin"
noncomputable def vp0000001110011010 : Blocks := vp0000001110011010_0
theorem coverp0000001110011010 : Covers (-115011639/125000 : ℚ) vp0000001110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111001101_0 : Blocks := edgeBlocks% "full/vectors/000000111001101-V-0000.bin"
noncomputable def vp000000111001101 : Blocks := vp000000111001101_0
private theorem bp0000001110011010 : Branch 0 (-115011639/250000 : ℚ) vp000000111001101 := by
  apply branch_left_normalized (c:=vp0000001110011010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-115011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-115011639/125000 : ℚ) by norm_num]
  exact coverp0000001110011010
private noncomputable def ep0000001110011011_0 : Blocks := edgeBlocks% "full/vectors/0000001110011011-E-0000.bin"
noncomputable def ep0000001110011011 : Blocks := ep0000001110011011_0
private theorem idp0000001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111001101.list =
    C ((2:ℤ)^43) * horner X vp0000001110011011.list + horner X ep0000001110011011.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110011011 : Branch 1 (-115011639/250000 : ℚ) vp000000111001101 := by
  apply branch_checked idp0000001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-115011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-115136639/125000 : ℚ) by norm_num]
  exact coverp0000001110011011
theorem coverp000000111001101 : Covers (-115011639/250000 : ℚ) vp000000111001101 := join_branches bp0000001110011010 bp0000001110011011
private noncomputable def vp000000111001100_0 : Blocks := edgeBlocks% "full/vectors/000000111001100-V-0000.bin"
noncomputable def vp000000111001100 : Blocks := vp000000111001100_0
theorem coverp000000111001100 : Covers (-114761639/250000 : ℚ) vp000000111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011100110_0 : Blocks := edgeBlocks% "full/vectors/00000011100110-V-0000.bin"
noncomputable def vp00000011100110 : Blocks := vp00000011100110_0
private theorem bp000000111001100 : Branch 0 (-114761639/500000 : ℚ) vp00000011100110 := by
  apply branch_left_normalized (c:=vp000000111001100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-114761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-114761639/250000 : ℚ) by norm_num]
  exact coverp000000111001100
private noncomputable def ep000000111001101_0 : Blocks := edgeBlocks% "full/vectors/000000111001101-E-0000.bin"
noncomputable def ep000000111001101 : Blocks := ep000000111001101_0
private theorem idp000000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100110.list =
    C ((2:ℤ)^68) * horner X vp000000111001101.list + horner X ep000000111001101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111001101 : Branch 1 (-114761639/500000 : ℚ) vp00000011100110 := by
  apply branch_checked idp000000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-114761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-115011639/250000 : ℚ) by norm_num]
  exact coverp000000111001101
theorem coverp00000011100110 : Covers (-114761639/500000 : ℚ) vp00000011100110 := join_branches bp000000111001100 bp000000111001101
private noncomputable def vp0000001110011_0 : Blocks := edgeBlocks% "full/vectors/0000001110011-V-0000.bin"
noncomputable def vp0000001110011 : Blocks := vp0000001110011_0
private theorem bp00000011100110 : Branch 0 (-114761639/1000000 : ℚ) vp0000001110011 := by
  apply branch_left_normalized (c:=vp00000011100110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-114761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-114761639/500000 : ℚ) by norm_num]
  exact coverp00000011100110
private noncomputable def ep00000011100111_0 : Blocks := edgeBlocks% "full/vectors/00000011100111-E-0000.bin"
noncomputable def ep00000011100111 : Blocks := ep00000011100111_0
private theorem idp00000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110011.list =
    C ((2:ℤ)^116) * horner X vp00000011100111.list + horner X ep00000011100111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011100111 : Branch 1 (-114761639/1000000 : ℚ) vp0000001110011 := by
  apply branch_checked idp00000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-114761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-115261639/500000 : ℚ) by norm_num]
  exact coverp00000011100111
theorem coverp0000001110011 : Covers (-114761639/1000000 : ℚ) vp0000001110011 := join_branches bp00000011100110 bp00000011100111
private noncomputable def vp000000111001011_0 : Blocks := edgeBlocks% "full/vectors/000000111001011-V-0000.bin"
noncomputable def vp000000111001011 : Blocks := vp000000111001011_0
theorem coverp000000111001011 : Covers (-114511639/250000 : ℚ) vp000000111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111001010_0 : Blocks := edgeBlocks% "full/vectors/000000111001010-V-0000.bin"
noncomputable def vp000000111001010 : Blocks := vp000000111001010_0
theorem coverp000000111001010 : Covers (-114261639/250000 : ℚ) vp000000111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011100101_0 : Blocks := edgeBlocks% "full/vectors/00000011100101-V-0000.bin"
noncomputable def vp00000011100101 : Blocks := vp00000011100101_0
private theorem bp000000111001010 : Branch 0 (-114261639/500000 : ℚ) vp00000011100101 := by
  apply branch_left_normalized (c:=vp000000111001010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-114261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-114261639/250000 : ℚ) by norm_num]
  exact coverp000000111001010
private noncomputable def ep000000111001011_0 : Blocks := edgeBlocks% "full/vectors/000000111001011-E-0000.bin"
noncomputable def ep000000111001011 : Blocks := ep000000111001011_0
private theorem idp000000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100101.list =
    C ((2:ℤ)^68) * horner X vp000000111001011.list + horner X ep000000111001011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111001011 : Branch 1 (-114261639/500000 : ℚ) vp00000011100101 := by
  apply branch_checked idp000000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-114261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-114511639/250000 : ℚ) by norm_num]
  exact coverp000000111001011
theorem coverp00000011100101 : Covers (-114261639/500000 : ℚ) vp00000011100101 := join_branches bp000000111001010 bp000000111001011
private noncomputable def vp000000111001001_0 : Blocks := edgeBlocks% "full/vectors/000000111001001-V-0000.bin"
noncomputable def vp000000111001001 : Blocks := vp000000111001001_0
theorem coverp000000111001001 : Covers (-114011639/250000 : ℚ) vp000000111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111001000_0 : Blocks := edgeBlocks% "full/vectors/000000111001000-V-0000.bin"
noncomputable def vp000000111001000 : Blocks := vp000000111001000_0
theorem coverp000000111001000 : Covers (-113761639/250000 : ℚ) vp000000111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011100100_0 : Blocks := edgeBlocks% "full/vectors/00000011100100-V-0000.bin"
noncomputable def vp00000011100100 : Blocks := vp00000011100100_0
private theorem bp000000111001000 : Branch 0 (-113761639/500000 : ℚ) vp00000011100100 := by
  apply branch_left_normalized (c:=vp000000111001000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-113761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-113761639/250000 : ℚ) by norm_num]
  exact coverp000000111001000
private noncomputable def ep000000111001001_0 : Blocks := edgeBlocks% "full/vectors/000000111001001-E-0000.bin"
noncomputable def ep000000111001001 : Blocks := ep000000111001001_0
private theorem idp000000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100100.list =
    C ((2:ℤ)^70) * horner X vp000000111001001.list + horner X ep000000111001001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111001001 : Branch 1 (-113761639/500000 : ℚ) vp00000011100100 := by
  apply branch_checked idp000000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-113761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-114011639/250000 : ℚ) by norm_num]
  exact coverp000000111001001
theorem coverp00000011100100 : Covers (-113761639/500000 : ℚ) vp00000011100100 := join_branches bp000000111001000 bp000000111001001
private noncomputable def vp0000001110010_0 : Blocks := edgeBlocks% "full/vectors/0000001110010-V-0000.bin"
noncomputable def vp0000001110010 : Blocks := vp0000001110010_0
private theorem bp00000011100100 : Branch 0 (-113761639/1000000 : ℚ) vp0000001110010 := by
  apply branch_left_normalized (c:=vp00000011100100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-113761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-113761639/500000 : ℚ) by norm_num]
  exact coverp00000011100100
private noncomputable def ep00000011100101_0 : Blocks := edgeBlocks% "full/vectors/00000011100101-E-0000.bin"
noncomputable def ep00000011100101 : Blocks := ep00000011100101_0
private theorem idp00000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110010.list =
    C ((2:ℤ)^119) * horner X vp00000011100101.list + horner X ep00000011100101.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011100101 : Branch 1 (-113761639/1000000 : ℚ) vp0000001110010 := by
  apply branch_checked idp00000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-113761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-114261639/500000 : ℚ) by norm_num]
  exact coverp00000011100101
theorem coverp0000001110010 : Covers (-113761639/1000000 : ℚ) vp0000001110010 := join_branches bp00000011100100 bp00000011100101
private noncomputable def vp000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000111001-V-0000.bin"
private noncomputable def vp000000111001_1 : Blocks := edgeBlocks% "full/vectors/000000111001-V-0001.bin"
noncomputable def vp000000111001 : Blocks := (Blocks.join vp000000111001_0 vp000000111001_1)
private theorem bp0000001110010 : Branch 0 (-113761639/2000000 : ℚ) vp000000111001 := by
  apply branch_left_normalized (c:=vp0000001110010) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-113761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-113761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110010
private noncomputable def ep0000001110011_0 : Blocks := edgeBlocks% "full/vectors/0000001110011-E-0000.bin"
private noncomputable def ep0000001110011_1 : Blocks := edgeBlocks% "full/vectors/0000001110011-E-0001.bin"
noncomputable def ep0000001110011 : Blocks := (Blocks.join ep0000001110011_0 ep0000001110011_1)
private theorem idp0000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111001.list =
    C ((2:ℤ)^215) * horner X vp0000001110011.list + horner X ep0000001110011.list := by
  exact edge_identity (B := (2:ℤ)^408) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110011 : Branch 1 (-113761639/2000000 : ℚ) vp000000111001 := by
  apply branch_checked idp0000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-113761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-114761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110011
theorem coverp000000111001 : Covers (-113761639/2000000 : ℚ) vp000000111001 := join_branches bp0000001110010 bp0000001110011
private noncomputable def vp0000001110001111_0 : Blocks := edgeBlocks% "full/vectors/0000001110001111-V-0000.bin"
noncomputable def vp0000001110001111 : Blocks := vp0000001110001111_0
theorem coverp0000001110001111 : Covers (-113636639/125000 : ℚ) vp0000001110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110001110_0 : Blocks := edgeBlocks% "full/vectors/0000001110001110-V-0000.bin"
noncomputable def vp0000001110001110 : Blocks := vp0000001110001110_0
theorem coverp0000001110001110 : Covers (-113511639/125000 : ℚ) vp0000001110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000111_0 : Blocks := edgeBlocks% "full/vectors/000000111000111-V-0000.bin"
noncomputable def vp000000111000111 : Blocks := vp000000111000111_0
private theorem bp0000001110001110 : Branch 0 (-113511639/250000 : ℚ) vp000000111000111 := by
  apply branch_left_normalized (c:=vp0000001110001110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-113511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-113511639/125000 : ℚ) by norm_num]
  exact coverp0000001110001110
private noncomputable def ep0000001110001111_0 : Blocks := edgeBlocks% "full/vectors/0000001110001111-E-0000.bin"
noncomputable def ep0000001110001111 : Blocks := ep0000001110001111_0
private theorem idp0000001110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111000111.list =
    C ((2:ℤ)^43) * horner X vp0000001110001111.list + horner X ep0000001110001111.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110001111 : Branch 1 (-113511639/250000 : ℚ) vp000000111000111 := by
  apply branch_checked idp0000001110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-113511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-113636639/125000 : ℚ) by norm_num]
  exact coverp0000001110001111
theorem coverp000000111000111 : Covers (-113511639/250000 : ℚ) vp000000111000111 := join_branches bp0000001110001110 bp0000001110001111
private noncomputable def vp0000001110001101_0 : Blocks := edgeBlocks% "full/vectors/0000001110001101-V-0000.bin"
noncomputable def vp0000001110001101 : Blocks := vp0000001110001101_0
theorem coverp0000001110001101 : Covers (-113386639/125000 : ℚ) vp0000001110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110001100_0 : Blocks := edgeBlocks% "full/vectors/0000001110001100-V-0000.bin"
noncomputable def vp0000001110001100 : Blocks := vp0000001110001100_0
theorem coverp0000001110001100 : Covers (-113261639/125000 : ℚ) vp0000001110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000110_0 : Blocks := edgeBlocks% "full/vectors/000000111000110-V-0000.bin"
noncomputable def vp000000111000110 : Blocks := vp000000111000110_0
private theorem bp0000001110001100 : Branch 0 (-113261639/250000 : ℚ) vp000000111000110 := by
  apply branch_left_normalized (c:=vp0000001110001100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-113261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-113261639/125000 : ℚ) by norm_num]
  exact coverp0000001110001100
private noncomputable def ep0000001110001101_0 : Blocks := edgeBlocks% "full/vectors/0000001110001101-E-0000.bin"
noncomputable def ep0000001110001101 : Blocks := ep0000001110001101_0
private theorem idp0000001110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111000110.list =
    C ((2:ℤ)^44) * horner X vp0000001110001101.list + horner X ep0000001110001101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110001101 : Branch 1 (-113261639/250000 : ℚ) vp000000111000110 := by
  apply branch_checked idp0000001110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-113261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-113386639/125000 : ℚ) by norm_num]
  exact coverp0000001110001101
theorem coverp000000111000110 : Covers (-113261639/250000 : ℚ) vp000000111000110 := join_branches bp0000001110001100 bp0000001110001101
private noncomputable def vp00000011100011_0 : Blocks := edgeBlocks% "full/vectors/00000011100011-V-0000.bin"
noncomputable def vp00000011100011 : Blocks := vp00000011100011_0
private theorem bp000000111000110 : Branch 0 (-113261639/500000 : ℚ) vp00000011100011 := by
  apply branch_left_normalized (c:=vp000000111000110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-113261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-113261639/250000 : ℚ) by norm_num]
  exact coverp000000111000110
private noncomputable def ep000000111000111_0 : Blocks := edgeBlocks% "full/vectors/000000111000111-E-0000.bin"
noncomputable def ep000000111000111 : Blocks := ep000000111000111_0
private theorem idp000000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100011.list =
    C ((2:ℤ)^69) * horner X vp000000111000111.list + horner X ep000000111000111.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111000111 : Branch 1 (-113261639/500000 : ℚ) vp00000011100011 := by
  apply branch_checked idp000000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-113261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-113511639/250000 : ℚ) by norm_num]
  exact coverp000000111000111
theorem coverp00000011100011 : Covers (-113261639/500000 : ℚ) vp00000011100011 := join_branches bp000000111000110 bp000000111000111
private noncomputable def vp0000001110001011_0 : Blocks := edgeBlocks% "full/vectors/0000001110001011-V-0000.bin"
noncomputable def vp0000001110001011 : Blocks := vp0000001110001011_0
theorem coverp0000001110001011 : Covers (-113136639/125000 : ℚ) vp0000001110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110001010_0 : Blocks := edgeBlocks% "full/vectors/0000001110001010-V-0000.bin"
noncomputable def vp0000001110001010 : Blocks := vp0000001110001010_0
theorem coverp0000001110001010 : Covers (-113011639/125000 : ℚ) vp0000001110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000101_0 : Blocks := edgeBlocks% "full/vectors/000000111000101-V-0000.bin"
noncomputable def vp000000111000101 : Blocks := vp000000111000101_0
private theorem bp0000001110001010 : Branch 0 (-113011639/250000 : ℚ) vp000000111000101 := by
  apply branch_left_normalized (c:=vp0000001110001010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-113011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-113011639/125000 : ℚ) by norm_num]
  exact coverp0000001110001010
private noncomputable def ep0000001110001011_0 : Blocks := edgeBlocks% "full/vectors/0000001110001011-E-0000.bin"
noncomputable def ep0000001110001011 : Blocks := ep0000001110001011_0
private theorem idp0000001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111000101.list =
    C ((2:ℤ)^43) * horner X vp0000001110001011.list + horner X ep0000001110001011.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110001011 : Branch 1 (-113011639/250000 : ℚ) vp000000111000101 := by
  apply branch_checked idp0000001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-113011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-113136639/125000 : ℚ) by norm_num]
  exact coverp0000001110001011
theorem coverp000000111000101 : Covers (-113011639/250000 : ℚ) vp000000111000101 := join_branches bp0000001110001010 bp0000001110001011
private noncomputable def vp0000001110001001_0 : Blocks := edgeBlocks% "full/vectors/0000001110001001-V-0000.bin"
noncomputable def vp0000001110001001 : Blocks := vp0000001110001001_0
theorem coverp0000001110001001 : Covers (-112886639/125000 : ℚ) vp0000001110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001110001000_0 : Blocks := edgeBlocks% "full/vectors/0000001110001000-V-0000.bin"
noncomputable def vp0000001110001000 : Blocks := vp0000001110001000_0
theorem coverp0000001110001000 : Covers (-112761639/125000 : ℚ) vp0000001110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000100_0 : Blocks := edgeBlocks% "full/vectors/000000111000100-V-0000.bin"
noncomputable def vp000000111000100 : Blocks := vp000000111000100_0
private theorem bp0000001110001000 : Branch 0 (-112761639/250000 : ℚ) vp000000111000100 := by
  apply branch_left_normalized (c:=vp0000001110001000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-112761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-112761639/125000 : ℚ) by norm_num]
  exact coverp0000001110001000
private noncomputable def ep0000001110001001_0 : Blocks := edgeBlocks% "full/vectors/0000001110001001-E-0000.bin"
noncomputable def ep0000001110001001 : Blocks := ep0000001110001001_0
private theorem idp0000001110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111000100.list =
    C ((2:ℤ)^42) * horner X vp0000001110001001.list + horner X ep0000001110001001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110001001 : Branch 1 (-112761639/250000 : ℚ) vp000000111000100 := by
  apply branch_checked idp0000001110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-112761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-112886639/125000 : ℚ) by norm_num]
  exact coverp0000001110001001
theorem coverp000000111000100 : Covers (-112761639/250000 : ℚ) vp000000111000100 := join_branches bp0000001110001000 bp0000001110001001
private noncomputable def vp00000011100010_0 : Blocks := edgeBlocks% "full/vectors/00000011100010-V-0000.bin"
noncomputable def vp00000011100010 : Blocks := vp00000011100010_0
private theorem bp000000111000100 : Branch 0 (-112761639/500000 : ℚ) vp00000011100010 := by
  apply branch_left_normalized (c:=vp000000111000100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-112761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-112761639/250000 : ℚ) by norm_num]
  exact coverp000000111000100
private noncomputable def ep000000111000101_0 : Blocks := edgeBlocks% "full/vectors/000000111000101-E-0000.bin"
noncomputable def ep000000111000101 : Blocks := ep000000111000101_0
private theorem idp000000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100010.list =
    C ((2:ℤ)^69) * horner X vp000000111000101.list + horner X ep000000111000101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111000101 : Branch 1 (-112761639/500000 : ℚ) vp00000011100010 := by
  apply branch_checked idp000000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-112761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-113011639/250000 : ℚ) by norm_num]
  exact coverp000000111000101
theorem coverp00000011100010 : Covers (-112761639/500000 : ℚ) vp00000011100010 := join_branches bp000000111000100 bp000000111000101
private noncomputable def vp0000001110001_0 : Blocks := edgeBlocks% "full/vectors/0000001110001-V-0000.bin"
noncomputable def vp0000001110001 : Blocks := vp0000001110001_0
private theorem bp00000011100010 : Branch 0 (-112761639/1000000 : ℚ) vp0000001110001 := by
  apply branch_left_normalized (c:=vp00000011100010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-112761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-112761639/500000 : ℚ) by norm_num]
  exact coverp00000011100010
private noncomputable def ep00000011100011_0 : Blocks := edgeBlocks% "full/vectors/00000011100011-E-0000.bin"
noncomputable def ep00000011100011 : Blocks := ep00000011100011_0
private theorem idp00000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110001.list =
    C ((2:ℤ)^117) * horner X vp00000011100011.list + horner X ep00000011100011.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011100011 : Branch 1 (-112761639/1000000 : ℚ) vp0000001110001 := by
  apply branch_checked idp00000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-112761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-113261639/500000 : ℚ) by norm_num]
  exact coverp00000011100011
theorem coverp0000001110001 : Covers (-112761639/1000000 : ℚ) vp0000001110001 := join_branches bp00000011100010 bp00000011100011
private noncomputable def vp000000111000011_0 : Blocks := edgeBlocks% "full/vectors/000000111000011-V-0000.bin"
noncomputable def vp000000111000011 : Blocks := vp000000111000011_0
theorem coverp000000111000011 : Covers (-112511639/250000 : ℚ) vp000000111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000010_0 : Blocks := edgeBlocks% "full/vectors/000000111000010-V-0000.bin"
noncomputable def vp000000111000010 : Blocks := vp000000111000010_0
theorem coverp000000111000010 : Covers (-112261639/250000 : ℚ) vp000000111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011100001_0 : Blocks := edgeBlocks% "full/vectors/00000011100001-V-0000.bin"
noncomputable def vp00000011100001 : Blocks := vp00000011100001_0
private theorem bp000000111000010 : Branch 0 (-112261639/500000 : ℚ) vp00000011100001 := by
  apply branch_left_normalized (c:=vp000000111000010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-112261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-112261639/250000 : ℚ) by norm_num]
  exact coverp000000111000010
private noncomputable def ep000000111000011_0 : Blocks := edgeBlocks% "full/vectors/000000111000011-E-0000.bin"
noncomputable def ep000000111000011 : Blocks := ep000000111000011_0
private theorem idp000000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100001.list =
    C ((2:ℤ)^68) * horner X vp000000111000011.list + horner X ep000000111000011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111000011 : Branch 1 (-112261639/500000 : ℚ) vp00000011100001 := by
  apply branch_checked idp000000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-112261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-112511639/250000 : ℚ) by norm_num]
  exact coverp000000111000011
theorem coverp00000011100001 : Covers (-112261639/500000 : ℚ) vp00000011100001 := join_branches bp000000111000010 bp000000111000011
private noncomputable def vp000000111000001_0 : Blocks := edgeBlocks% "full/vectors/000000111000001-V-0000.bin"
noncomputable def vp000000111000001 : Blocks := vp000000111000001_0
theorem coverp000000111000001 : Covers (-112011639/250000 : ℚ) vp000000111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000111000000_0 : Blocks := edgeBlocks% "full/vectors/000000111000000-V-0000.bin"
noncomputable def vp000000111000000 : Blocks := vp000000111000000_0
theorem coverp000000111000000 : Covers (-111761639/250000 : ℚ) vp000000111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011100000_0 : Blocks := edgeBlocks% "full/vectors/00000011100000-V-0000.bin"
noncomputable def vp00000011100000 : Blocks := vp00000011100000_0
private theorem bp000000111000000 : Branch 0 (-111761639/500000 : ℚ) vp00000011100000 := by
  apply branch_left_normalized (c:=vp000000111000000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-111761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/250000 : ℚ) by norm_num]
  exact coverp000000111000000
private noncomputable def ep000000111000001_0 : Blocks := edgeBlocks% "full/vectors/000000111000001-E-0000.bin"
noncomputable def ep000000111000001 : Blocks := ep000000111000001_0
private theorem idp000000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100000.list =
    C ((2:ℤ)^69) * horner X vp000000111000001.list + horner X ep000000111000001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111000001 : Branch 1 (-111761639/500000 : ℚ) vp00000011100000 := by
  apply branch_checked idp000000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-112011639/250000 : ℚ) by norm_num]
  exact coverp000000111000001
theorem coverp00000011100000 : Covers (-111761639/500000 : ℚ) vp00000011100000 := join_branches bp000000111000000 bp000000111000001
private noncomputable def vp0000001110000_0 : Blocks := edgeBlocks% "full/vectors/0000001110000-V-0000.bin"
noncomputable def vp0000001110000 : Blocks := vp0000001110000_0
private theorem bp00000011100000 : Branch 0 (-111761639/1000000 : ℚ) vp0000001110000 := by
  apply branch_left_normalized (c:=vp00000011100000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-111761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/500000 : ℚ) by norm_num]
  exact coverp00000011100000
private noncomputable def ep00000011100001_0 : Blocks := edgeBlocks% "full/vectors/00000011100001-E-0000.bin"
noncomputable def ep00000011100001 : Blocks := ep00000011100001_0
private theorem idp00000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110000.list =
    C ((2:ℤ)^118) * horner X vp00000011100001.list + horner X ep00000011100001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011100001 : Branch 1 (-111761639/1000000 : ℚ) vp0000001110000 := by
  apply branch_checked idp00000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-112261639/500000 : ℚ) by norm_num]
  exact coverp00000011100001
theorem coverp0000001110000 : Covers (-111761639/1000000 : ℚ) vp0000001110000 := join_branches bp00000011100000 bp00000011100001
private noncomputable def vp000000111000_0 : Blocks := edgeBlocks% "full/vectors/000000111000-V-0000.bin"
private noncomputable def vp000000111000_1 : Blocks := edgeBlocks% "full/vectors/000000111000-V-0001.bin"
noncomputable def vp000000111000 : Blocks := (Blocks.join vp000000111000_0 vp000000111000_1)
private theorem bp0000001110000 : Branch 0 (-111761639/2000000 : ℚ) vp000000111000 := by
  apply branch_left_normalized (c:=vp0000001110000) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-111761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110000
private noncomputable def ep0000001110001_0 : Blocks := edgeBlocks% "full/vectors/0000001110001-E-0000.bin"
private noncomputable def ep0000001110001_1 : Blocks := edgeBlocks% "full/vectors/0000001110001-E-0001.bin"
noncomputable def ep0000001110001 : Blocks := (Blocks.join ep0000001110001_0 ep0000001110001_1)
private theorem idp0000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111000.list =
    C ((2:ℤ)^213) * horner X vp0000001110001.list + horner X ep0000001110001.list := by
  exact edge_identity (B := (2:ℤ)^408) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001110001 : Branch 1 (-111761639/2000000 : ℚ) vp000000111000 := by
  apply branch_checked idp0000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-112761639/1000000 : ℚ) by norm_num]
  exact coverp0000001110001
theorem coverp000000111000 : Covers (-111761639/2000000 : ℚ) vp000000111000 := join_branches bp0000001110000 bp0000001110001
private noncomputable def vp00000011100_0 : Blocks := edgeBlocks% "full/vectors/00000011100-V-0000.bin"
private noncomputable def vp00000011100_1 : Blocks := edgeBlocks% "full/vectors/00000011100-V-0001.bin"
private noncomputable def vp00000011100_2 : Blocks := edgeBlocks% "full/vectors/00000011100-V-0002.bin"
private noncomputable def vp00000011100_3 : Blocks := edgeBlocks% "full/vectors/00000011100-V-0003.bin"
noncomputable def vp00000011100 : Blocks := (Blocks.join (Blocks.join vp00000011100_0 vp00000011100_1) (Blocks.join vp00000011100_2 vp00000011100_3))
private theorem bp000000111000 : Branch 0 (-111761639/4000000 : ℚ) vp00000011100 := by
  apply branch_left_normalized (c:=vp000000111000) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-111761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/2000000 : ℚ) by norm_num]
  exact coverp000000111000
private noncomputable def ep000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000111001-E-0000.bin"
private noncomputable def ep000000111001_1 : Blocks := edgeBlocks% "full/vectors/000000111001-E-0001.bin"
private noncomputable def ep000000111001_2 : Blocks := edgeBlocks% "full/vectors/000000111001-E-0002.bin"
private noncomputable def ep000000111001_3 : Blocks := edgeBlocks% "full/vectors/000000111001-E-0003.bin"
noncomputable def ep000000111001 : Blocks := (Blocks.join (Blocks.join ep000000111001_0 ep000000111001_1) (Blocks.join ep000000111001_2 ep000000111001_3))
private theorem idp000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011100.list =
    C ((2:ℤ)^403) * horner X vp000000111001.list + horner X ep000000111001.list := by
  exact edge_identity (B := (2:ℤ)^691) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000111001 : Branch 1 (-111761639/4000000 : ℚ) vp00000011100 := by
  apply branch_checked idp000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-113761639/2000000 : ℚ) by norm_num]
  exact coverp000000111001
theorem coverp00000011100 : Covers (-111761639/4000000 : ℚ) vp00000011100 := join_branches bp000000111000 bp000000111001
private noncomputable def vp0000001110_0 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0000.bin"
private noncomputable def vp0000001110_1 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0001.bin"
private noncomputable def vp0000001110_2 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0002.bin"
private noncomputable def vp0000001110_3 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0003.bin"
private noncomputable def vp0000001110_4 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0004.bin"
private noncomputable def vp0000001110_5 : Blocks := edgeBlocks% "full/vectors/0000001110-V-0005.bin"
noncomputable def vp0000001110 : Blocks := (Blocks.join (Blocks.join vp0000001110_0 (Blocks.join vp0000001110_1 vp0000001110_2)) (Blocks.join vp0000001110_3 (Blocks.join vp0000001110_4 vp0000001110_5)))
private theorem bp00000011100 : Branch 0 (-111761639/8000000 : ℚ) vp0000001110 := by
  apply branch_left_normalized (c:=vp00000011100) (k:=0) (m:=392) (by decide +kernel)
  rw [show 2*(-111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/4000000 : ℚ) by norm_num]
  exact coverp00000011100
private noncomputable def ep00000011101_0 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0000.bin"
private noncomputable def ep00000011101_1 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0001.bin"
private noncomputable def ep00000011101_2 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0002.bin"
private noncomputable def ep00000011101_3 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0003.bin"
private noncomputable def ep00000011101_4 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0004.bin"
private noncomputable def ep00000011101_5 : Blocks := edgeBlocks% "full/vectors/00000011101-E-0005.bin"
noncomputable def ep00000011101 : Blocks := (Blocks.join (Blocks.join ep00000011101_0 (Blocks.join ep00000011101_1 ep00000011101_2)) (Blocks.join ep00000011101_3 (Blocks.join ep00000011101_4 ep00000011101_5)))
private theorem idp00000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001110.list =
    C ((2:ℤ)^780) * horner X vp00000011101.list + horner X ep00000011101.list := by
  exact edge_identity (B := (2:ℤ)^1253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011101 : Branch 1 (-111761639/8000000 : ℚ) vp0000001110 := by
  apply branch_checked idp00000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-115761639/4000000 : ℚ) by norm_num]
  exact coverp00000011101
theorem coverp0000001110 : Covers (-111761639/8000000 : ℚ) vp0000001110 := join_branches bp00000011100 bp00000011101
private noncomputable def vp000000111_0 : Blocks := edgeBlocks% "full/vectors/000000111-V-0000.bin"
private noncomputable def vp000000111_1 : Blocks := edgeBlocks% "full/vectors/000000111-V-0001.bin"
private noncomputable def vp000000111_2 : Blocks := edgeBlocks% "full/vectors/000000111-V-0002.bin"
private noncomputable def vp000000111_3 : Blocks := edgeBlocks% "full/vectors/000000111-V-0003.bin"
private noncomputable def vp000000111_4 : Blocks := edgeBlocks% "full/vectors/000000111-V-0004.bin"
private noncomputable def vp000000111_5 : Blocks := edgeBlocks% "full/vectors/000000111-V-0005.bin"
private noncomputable def vp000000111_6 : Blocks := edgeBlocks% "full/vectors/000000111-V-0006.bin"
private noncomputable def vp000000111_7 : Blocks := edgeBlocks% "full/vectors/000000111-V-0007.bin"
private noncomputable def vp000000111_8 : Blocks := edgeBlocks% "full/vectors/000000111-V-0008.bin"
private noncomputable def vp000000111_9 : Blocks := edgeBlocks% "full/vectors/000000111-V-0009.bin"
private noncomputable def vp000000111_10 : Blocks := edgeBlocks% "full/vectors/000000111-V-0010.bin"
private noncomputable def vp000000111_11 : Blocks := edgeBlocks% "full/vectors/000000111-V-0011.bin"
noncomputable def vp000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000000111_0 (Blocks.join vp000000111_1 vp000000111_2)) (Blocks.join vp000000111_3 (Blocks.join vp000000111_4 vp000000111_5))) (Blocks.join (Blocks.join vp000000111_6 (Blocks.join vp000000111_7 vp000000111_8)) (Blocks.join vp000000111_9 (Blocks.join vp000000111_10 vp000000111_11))))
private theorem bp0000001110 : Branch 0 (-111761639/16000000 : ℚ) vp000000111 := by
  apply branch_left_normalized (c:=vp0000001110) (k:=0) (m:=758) (by decide +kernel)
  rw [show 2*(-111761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-111761639/8000000 : ℚ) by norm_num]
  exact coverp0000001110
private noncomputable def ep0000001111_0 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0000.bin"
private noncomputable def ep0000001111_1 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0001.bin"
private noncomputable def ep0000001111_2 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0002.bin"
private noncomputable def ep0000001111_3 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0003.bin"
private noncomputable def ep0000001111_4 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0004.bin"
private noncomputable def ep0000001111_5 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0005.bin"
private noncomputable def ep0000001111_6 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0006.bin"
private noncomputable def ep0000001111_7 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0007.bin"
private noncomputable def ep0000001111_8 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0008.bin"
private noncomputable def ep0000001111_9 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0009.bin"
private noncomputable def ep0000001111_10 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0010.bin"
private noncomputable def ep0000001111_11 : Blocks := edgeBlocks% "full/vectors/0000001111-E-0011.bin"
noncomputable def ep0000001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000001111_0 (Blocks.join ep0000001111_1 ep0000001111_2)) (Blocks.join ep0000001111_3 (Blocks.join ep0000001111_4 ep0000001111_5))) (Blocks.join (Blocks.join ep0000001111_6 (Blocks.join ep0000001111_7 ep0000001111_8)) (Blocks.join ep0000001111_9 (Blocks.join ep0000001111_10 ep0000001111_11))))
private theorem idp0000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000111.list =
    C ((2:ℤ)^1529) * horner X vp0000001111.list + horner X ep0000001111.list := by
  exact edge_identity (B := (2:ℤ)^2361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001111 : Branch 1 (-111761639/16000000 : ℚ) vp000000111 := by
  apply branch_checked idp0000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-111761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-119761639/8000000 : ℚ) by norm_num]
  exact coverp0000001111
theorem coverp000000111 : Covers (-111761639/16000000 : ℚ) vp000000111 := join_branches bp0000001110 bp0000001111
end NextProof.EdgeFull

