import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00060

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00001110111111_0 : Blocks := edgeBlocks% "full/vectors/00001110111111-V-0000.bin"
noncomputable def vp00001110111111 : Blocks := vp00001110111111_0
theorem coverp00001110111111 : Covers (-479261639/500000 : ℚ) vp00001110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110111110_0 : Blocks := edgeBlocks% "full/vectors/00001110111110-V-0000.bin"
noncomputable def vp00001110111110 : Blocks := vp00001110111110_0
theorem coverp00001110111110 : Covers (-478761639/500000 : ℚ) vp00001110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011111_0 : Blocks := edgeBlocks% "full/vectors/0000111011111-V-0000.bin"
noncomputable def vp0000111011111 : Blocks := vp0000111011111_0
private theorem bp00001110111110 : Branch 0 (-478761639/1000000 : ℚ) vp0000111011111 := by
  apply branch_left_normalized (c:=vp00001110111110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-478761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-478761639/500000 : ℚ) by norm_num]
  exact coverp00001110111110
private noncomputable def ep00001110111111_0 : Blocks := edgeBlocks% "full/vectors/00001110111111-E-0000.bin"
noncomputable def ep00001110111111 : Blocks := ep00001110111111_0
private theorem idp00001110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011111.list =
    C ((2:ℤ)^69) * horner X vp00001110111111.list + horner X ep00001110111111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110111111 : Branch 1 (-478761639/1000000 : ℚ) vp0000111011111 := by
  apply branch_checked idp00001110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-478761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-479261639/500000 : ℚ) by norm_num]
  exact coverp00001110111111
theorem coverp0000111011111 : Covers (-478761639/1000000 : ℚ) vp0000111011111 := join_branches bp00001110111110 bp00001110111111
private noncomputable def vp00001110111101_0 : Blocks := edgeBlocks% "full/vectors/00001110111101-V-0000.bin"
noncomputable def vp00001110111101 : Blocks := vp00001110111101_0
theorem coverp00001110111101 : Covers (-478261639/500000 : ℚ) vp00001110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110111100_0 : Blocks := edgeBlocks% "full/vectors/00001110111100-V-0000.bin"
noncomputable def vp00001110111100 : Blocks := vp00001110111100_0
theorem coverp00001110111100 : Covers (-477761639/500000 : ℚ) vp00001110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011110_0 : Blocks := edgeBlocks% "full/vectors/0000111011110-V-0000.bin"
noncomputable def vp0000111011110 : Blocks := vp0000111011110_0
private theorem bp00001110111100 : Branch 0 (-477761639/1000000 : ℚ) vp0000111011110 := by
  apply branch_left_normalized (c:=vp00001110111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-477761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-477761639/500000 : ℚ) by norm_num]
  exact coverp00001110111100
private noncomputable def ep00001110111101_0 : Blocks := edgeBlocks% "full/vectors/00001110111101-E-0000.bin"
noncomputable def ep00001110111101 : Blocks := ep00001110111101_0
private theorem idp00001110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011110.list =
    C ((2:ℤ)^69) * horner X vp00001110111101.list + horner X ep00001110111101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110111101 : Branch 1 (-477761639/1000000 : ℚ) vp0000111011110 := by
  apply branch_checked idp00001110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-477761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-478261639/500000 : ℚ) by norm_num]
  exact coverp00001110111101
theorem coverp0000111011110 : Covers (-477761639/1000000 : ℚ) vp0000111011110 := join_branches bp00001110111100 bp00001110111101
private noncomputable def vp000011101111_0 : Blocks := edgeBlocks% "full/vectors/000011101111-V-0000.bin"
noncomputable def vp000011101111 : Blocks := vp000011101111_0
private theorem bp0000111011110 : Branch 0 (-477761639/2000000 : ℚ) vp000011101111 := by
  apply branch_left_normalized (c:=vp0000111011110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-477761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-477761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011110
private noncomputable def ep0000111011111_0 : Blocks := edgeBlocks% "full/vectors/0000111011111-E-0000.bin"
noncomputable def ep0000111011111 : Blocks := ep0000111011111_0
private theorem idp0000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101111.list =
    C ((2:ℤ)^119) * horner X vp0000111011111.list + horner X ep0000111011111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111011111 : Branch 1 (-477761639/2000000 : ℚ) vp000011101111 := by
  apply branch_checked idp0000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-477761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-478761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011111
theorem coverp000011101111 : Covers (-477761639/2000000 : ℚ) vp000011101111 := join_branches bp0000111011110 bp0000111011111
private noncomputable def vp00001110111011_0 : Blocks := edgeBlocks% "full/vectors/00001110111011-V-0000.bin"
noncomputable def vp00001110111011 : Blocks := vp00001110111011_0
theorem coverp00001110111011 : Covers (-477261639/500000 : ℚ) vp00001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110111010_0 : Blocks := edgeBlocks% "full/vectors/00001110111010-V-0000.bin"
noncomputable def vp00001110111010 : Blocks := vp00001110111010_0
theorem coverp00001110111010 : Covers (-476761639/500000 : ℚ) vp00001110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011101_0 : Blocks := edgeBlocks% "full/vectors/0000111011101-V-0000.bin"
noncomputable def vp0000111011101 : Blocks := vp0000111011101_0
private theorem bp00001110111010 : Branch 0 (-476761639/1000000 : ℚ) vp0000111011101 := by
  apply branch_left_normalized (c:=vp00001110111010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-476761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-476761639/500000 : ℚ) by norm_num]
  exact coverp00001110111010
private noncomputable def ep00001110111011_0 : Blocks := edgeBlocks% "full/vectors/00001110111011-E-0000.bin"
noncomputable def ep00001110111011 : Blocks := ep00001110111011_0
private theorem idp00001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011101.list =
    C ((2:ℤ)^69) * horner X vp00001110111011.list + horner X ep00001110111011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110111011 : Branch 1 (-476761639/1000000 : ℚ) vp0000111011101 := by
  apply branch_checked idp00001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-476761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-477261639/500000 : ℚ) by norm_num]
  exact coverp00001110111011
theorem coverp0000111011101 : Covers (-476761639/1000000 : ℚ) vp0000111011101 := join_branches bp00001110111010 bp00001110111011
private noncomputable def vp00001110111001_0 : Blocks := edgeBlocks% "full/vectors/00001110111001-V-0000.bin"
noncomputable def vp00001110111001 : Blocks := vp00001110111001_0
theorem coverp00001110111001 : Covers (-476261639/500000 : ℚ) vp00001110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110111000_0 : Blocks := edgeBlocks% "full/vectors/00001110111000-V-0000.bin"
noncomputable def vp00001110111000 : Blocks := vp00001110111000_0
theorem coverp00001110111000 : Covers (-475761639/500000 : ℚ) vp00001110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011100_0 : Blocks := edgeBlocks% "full/vectors/0000111011100-V-0000.bin"
noncomputable def vp0000111011100 : Blocks := vp0000111011100_0
private theorem bp00001110111000 : Branch 0 (-475761639/1000000 : ℚ) vp0000111011100 := by
  apply branch_left_normalized (c:=vp00001110111000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-475761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-475761639/500000 : ℚ) by norm_num]
  exact coverp00001110111000
private noncomputable def ep00001110111001_0 : Blocks := edgeBlocks% "full/vectors/00001110111001-E-0000.bin"
noncomputable def ep00001110111001 : Blocks := ep00001110111001_0
private theorem idp00001110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011100.list =
    C ((2:ℤ)^68) * horner X vp00001110111001.list + horner X ep00001110111001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110111001 : Branch 1 (-475761639/1000000 : ℚ) vp0000111011100 := by
  apply branch_checked idp00001110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-475761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-476261639/500000 : ℚ) by norm_num]
  exact coverp00001110111001
theorem coverp0000111011100 : Covers (-475761639/1000000 : ℚ) vp0000111011100 := join_branches bp00001110111000 bp00001110111001
private noncomputable def vp000011101110_0 : Blocks := edgeBlocks% "full/vectors/000011101110-V-0000.bin"
noncomputable def vp000011101110 : Blocks := vp000011101110_0
private theorem bp0000111011100 : Branch 0 (-475761639/2000000 : ℚ) vp000011101110 := by
  apply branch_left_normalized (c:=vp0000111011100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-475761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-475761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011100
private noncomputable def ep0000111011101_0 : Blocks := edgeBlocks% "full/vectors/0000111011101-E-0000.bin"
noncomputable def ep0000111011101 : Blocks := ep0000111011101_0
private theorem idp0000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101110.list =
    C ((2:ℤ)^117) * horner X vp0000111011101.list + horner X ep0000111011101.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111011101 : Branch 1 (-475761639/2000000 : ℚ) vp000011101110 := by
  apply branch_checked idp0000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-475761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-476761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011101
theorem coverp000011101110 : Covers (-475761639/2000000 : ℚ) vp000011101110 := join_branches bp0000111011100 bp0000111011101
private noncomputable def vp00001110111_0 : Blocks := edgeBlocks% "full/vectors/00001110111-V-0000.bin"
private noncomputable def vp00001110111_1 : Blocks := edgeBlocks% "full/vectors/00001110111-V-0001.bin"
noncomputable def vp00001110111 : Blocks := (Blocks.join vp00001110111_0 vp00001110111_1)
private theorem bp000011101110 : Branch 0 (-475761639/4000000 : ℚ) vp00001110111 := by
  apply branch_left_normalized (c:=vp000011101110) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-475761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-475761639/2000000 : ℚ) by norm_num]
  exact coverp000011101110
private noncomputable def ep000011101111_0 : Blocks := edgeBlocks% "full/vectors/000011101111-E-0000.bin"
private noncomputable def ep000011101111_1 : Blocks := edgeBlocks% "full/vectors/000011101111-E-0001.bin"
noncomputable def ep000011101111 : Blocks := (Blocks.join ep000011101111_0 ep000011101111_1)
private theorem idp000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110111.list =
    C ((2:ℤ)^213) * horner X vp000011101111.list + horner X ep000011101111.list := by
  exact edge_identity (B := (2:ℤ)^399) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011101111 : Branch 1 (-475761639/4000000 : ℚ) vp00001110111 := by
  apply branch_checked idp000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-475761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-477761639/2000000 : ℚ) by norm_num]
  exact coverp000011101111
theorem coverp00001110111 : Covers (-475761639/4000000 : ℚ) vp00001110111 := join_branches bp000011101110 bp000011101111
private noncomputable def vp00001110110111_0 : Blocks := edgeBlocks% "full/vectors/00001110110111-V-0000.bin"
noncomputable def vp00001110110111 : Blocks := vp00001110110111_0
theorem coverp00001110110111 : Covers (-475261639/500000 : ℚ) vp00001110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110110110_0 : Blocks := edgeBlocks% "full/vectors/00001110110110-V-0000.bin"
noncomputable def vp00001110110110 : Blocks := vp00001110110110_0
theorem coverp00001110110110 : Covers (-474761639/500000 : ℚ) vp00001110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011011_0 : Blocks := edgeBlocks% "full/vectors/0000111011011-V-0000.bin"
noncomputable def vp0000111011011 : Blocks := vp0000111011011_0
private theorem bp00001110110110 : Branch 0 (-474761639/1000000 : ℚ) vp0000111011011 := by
  apply branch_left_normalized (c:=vp00001110110110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-474761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-474761639/500000 : ℚ) by norm_num]
  exact coverp00001110110110
private noncomputable def ep00001110110111_0 : Blocks := edgeBlocks% "full/vectors/00001110110111-E-0000.bin"
noncomputable def ep00001110110111 : Blocks := ep00001110110111_0
private theorem idp00001110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011011.list =
    C ((2:ℤ)^69) * horner X vp00001110110111.list + horner X ep00001110110111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110110111 : Branch 1 (-474761639/1000000 : ℚ) vp0000111011011 := by
  apply branch_checked idp00001110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-474761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-475261639/500000 : ℚ) by norm_num]
  exact coverp00001110110111
theorem coverp0000111011011 : Covers (-474761639/1000000 : ℚ) vp0000111011011 := join_branches bp00001110110110 bp00001110110111
private noncomputable def vp00001110110101_0 : Blocks := edgeBlocks% "full/vectors/00001110110101-V-0000.bin"
noncomputable def vp00001110110101 : Blocks := vp00001110110101_0
theorem coverp00001110110101 : Covers (-474261639/500000 : ℚ) vp00001110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110110100_0 : Blocks := edgeBlocks% "full/vectors/00001110110100-V-0000.bin"
noncomputable def vp00001110110100 : Blocks := vp00001110110100_0
theorem coverp00001110110100 : Covers (-473761639/500000 : ℚ) vp00001110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011010_0 : Blocks := edgeBlocks% "full/vectors/0000111011010-V-0000.bin"
noncomputable def vp0000111011010 : Blocks := vp0000111011010_0
private theorem bp00001110110100 : Branch 0 (-473761639/1000000 : ℚ) vp0000111011010 := by
  apply branch_left_normalized (c:=vp00001110110100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-473761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-473761639/500000 : ℚ) by norm_num]
  exact coverp00001110110100
private noncomputable def ep00001110110101_0 : Blocks := edgeBlocks% "full/vectors/00001110110101-E-0000.bin"
noncomputable def ep00001110110101 : Blocks := ep00001110110101_0
private theorem idp00001110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011010.list =
    C ((2:ℤ)^69) * horner X vp00001110110101.list + horner X ep00001110110101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110110101 : Branch 1 (-473761639/1000000 : ℚ) vp0000111011010 := by
  apply branch_checked idp00001110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-473761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-474261639/500000 : ℚ) by norm_num]
  exact coverp00001110110101
theorem coverp0000111011010 : Covers (-473761639/1000000 : ℚ) vp0000111011010 := join_branches bp00001110110100 bp00001110110101
private noncomputable def vp000011101101_0 : Blocks := edgeBlocks% "full/vectors/000011101101-V-0000.bin"
noncomputable def vp000011101101 : Blocks := vp000011101101_0
private theorem bp0000111011010 : Branch 0 (-473761639/2000000 : ℚ) vp000011101101 := by
  apply branch_left_normalized (c:=vp0000111011010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-473761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-473761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011010
private noncomputable def ep0000111011011_0 : Blocks := edgeBlocks% "full/vectors/0000111011011-E-0000.bin"
noncomputable def ep0000111011011 : Blocks := ep0000111011011_0
private theorem idp0000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101101.list =
    C ((2:ℤ)^119) * horner X vp0000111011011.list + horner X ep0000111011011.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111011011 : Branch 1 (-473761639/2000000 : ℚ) vp000011101101 := by
  apply branch_checked idp0000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-473761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-474761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011011
theorem coverp000011101101 : Covers (-473761639/2000000 : ℚ) vp000011101101 := join_branches bp0000111011010 bp0000111011011
private noncomputable def vp00001110110011_0 : Blocks := edgeBlocks% "full/vectors/00001110110011-V-0000.bin"
noncomputable def vp00001110110011 : Blocks := vp00001110110011_0
theorem coverp00001110110011 : Covers (-473261639/500000 : ℚ) vp00001110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110110010_0 : Blocks := edgeBlocks% "full/vectors/00001110110010-V-0000.bin"
noncomputable def vp00001110110010 : Blocks := vp00001110110010_0
theorem coverp00001110110010 : Covers (-472761639/500000 : ℚ) vp00001110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011001_0 : Blocks := edgeBlocks% "full/vectors/0000111011001-V-0000.bin"
noncomputable def vp0000111011001 : Blocks := vp0000111011001_0
private theorem bp00001110110010 : Branch 0 (-472761639/1000000 : ℚ) vp0000111011001 := by
  apply branch_left_normalized (c:=vp00001110110010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-472761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-472761639/500000 : ℚ) by norm_num]
  exact coverp00001110110010
private noncomputable def ep00001110110011_0 : Blocks := edgeBlocks% "full/vectors/00001110110011-E-0000.bin"
noncomputable def ep00001110110011 : Blocks := ep00001110110011_0
private theorem idp00001110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011001.list =
    C ((2:ℤ)^69) * horner X vp00001110110011.list + horner X ep00001110110011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110110011 : Branch 1 (-472761639/1000000 : ℚ) vp0000111011001 := by
  apply branch_checked idp00001110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-472761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-473261639/500000 : ℚ) by norm_num]
  exact coverp00001110110011
theorem coverp0000111011001 : Covers (-472761639/1000000 : ℚ) vp0000111011001 := join_branches bp00001110110010 bp00001110110011
private noncomputable def vp00001110110001_0 : Blocks := edgeBlocks% "full/vectors/00001110110001-V-0000.bin"
noncomputable def vp00001110110001 : Blocks := vp00001110110001_0
theorem coverp00001110110001 : Covers (-472261639/500000 : ℚ) vp00001110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110110000_0 : Blocks := edgeBlocks% "full/vectors/00001110110000-V-0000.bin"
noncomputable def vp00001110110000 : Blocks := vp00001110110000_0
theorem coverp00001110110000 : Covers (-471761639/500000 : ℚ) vp00001110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111011000_0 : Blocks := edgeBlocks% "full/vectors/0000111011000-V-0000.bin"
noncomputable def vp0000111011000 : Blocks := vp0000111011000_0
private theorem bp00001110110000 : Branch 0 (-471761639/1000000 : ℚ) vp0000111011000 := by
  apply branch_left_normalized (c:=vp00001110110000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-471761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-471761639/500000 : ℚ) by norm_num]
  exact coverp00001110110000
private noncomputable def ep00001110110001_0 : Blocks := edgeBlocks% "full/vectors/00001110110001-E-0000.bin"
noncomputable def ep00001110110001 : Blocks := ep00001110110001_0
private theorem idp00001110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011000.list =
    C ((2:ℤ)^69) * horner X vp00001110110001.list + horner X ep00001110110001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110110001 : Branch 1 (-471761639/1000000 : ℚ) vp0000111011000 := by
  apply branch_checked idp00001110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-471761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-472261639/500000 : ℚ) by norm_num]
  exact coverp00001110110001
theorem coverp0000111011000 : Covers (-471761639/1000000 : ℚ) vp0000111011000 := join_branches bp00001110110000 bp00001110110001
private noncomputable def vp000011101100_0 : Blocks := edgeBlocks% "full/vectors/000011101100-V-0000.bin"
noncomputable def vp000011101100 : Blocks := vp000011101100_0
private theorem bp0000111011000 : Branch 0 (-471761639/2000000 : ℚ) vp000011101100 := by
  apply branch_left_normalized (c:=vp0000111011000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-471761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-471761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011000
private noncomputable def ep0000111011001_0 : Blocks := edgeBlocks% "full/vectors/0000111011001-E-0000.bin"
noncomputable def ep0000111011001 : Blocks := ep0000111011001_0
private theorem idp0000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101100.list =
    C ((2:ℤ)^118) * horner X vp0000111011001.list + horner X ep0000111011001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111011001 : Branch 1 (-471761639/2000000 : ℚ) vp000011101100 := by
  apply branch_checked idp0000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-471761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-472761639/1000000 : ℚ) by norm_num]
  exact coverp0000111011001
theorem coverp000011101100 : Covers (-471761639/2000000 : ℚ) vp000011101100 := join_branches bp0000111011000 bp0000111011001
private noncomputable def vp00001110110_0 : Blocks := edgeBlocks% "full/vectors/00001110110-V-0000.bin"
private noncomputable def vp00001110110_1 : Blocks := edgeBlocks% "full/vectors/00001110110-V-0001.bin"
noncomputable def vp00001110110 : Blocks := (Blocks.join vp00001110110_0 vp00001110110_1)
private theorem bp000011101100 : Branch 0 (-471761639/4000000 : ℚ) vp00001110110 := by
  apply branch_left_normalized (c:=vp000011101100) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-471761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-471761639/2000000 : ℚ) by norm_num]
  exact coverp000011101100
private noncomputable def ep000011101101_0 : Blocks := edgeBlocks% "full/vectors/000011101101-E-0000.bin"
private noncomputable def ep000011101101_1 : Blocks := edgeBlocks% "full/vectors/000011101101-E-0001.bin"
noncomputable def ep000011101101 : Blocks := (Blocks.join ep000011101101_0 ep000011101101_1)
private theorem idp000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110110.list =
    C ((2:ℤ)^216) * horner X vp000011101101.list + horner X ep000011101101.list := by
  exact edge_identity (B := (2:ℤ)^402) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011101101 : Branch 1 (-471761639/4000000 : ℚ) vp00001110110 := by
  apply branch_checked idp000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-471761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-473761639/2000000 : ℚ) by norm_num]
  exact coverp000011101101
theorem coverp00001110110 : Covers (-471761639/4000000 : ℚ) vp00001110110 := join_branches bp000011101100 bp000011101101
private noncomputable def vp0000111011_0 : Blocks := edgeBlocks% "full/vectors/0000111011-V-0000.bin"
private noncomputable def vp0000111011_1 : Blocks := edgeBlocks% "full/vectors/0000111011-V-0001.bin"
private noncomputable def vp0000111011_2 : Blocks := edgeBlocks% "full/vectors/0000111011-V-0002.bin"
noncomputable def vp0000111011 : Blocks := (Blocks.join vp0000111011_0 (Blocks.join vp0000111011_1 vp0000111011_2))
private theorem bp00001110110 : Branch 0 (-471761639/8000000 : ℚ) vp0000111011 := by
  apply branch_left_normalized (c:=vp00001110110) (k:=0) (m:=203) (by decide +kernel)
  rw [show 2*(-471761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-471761639/4000000 : ℚ) by norm_num]
  exact coverp00001110110
private noncomputable def ep00001110111_0 : Blocks := edgeBlocks% "full/vectors/00001110111-E-0000.bin"
private noncomputable def ep00001110111_1 : Blocks := edgeBlocks% "full/vectors/00001110111-E-0001.bin"
private noncomputable def ep00001110111_2 : Blocks := edgeBlocks% "full/vectors/00001110111-E-0002.bin"
noncomputable def ep00001110111 : Blocks := (Blocks.join ep00001110111_0 (Blocks.join ep00001110111_1 ep00001110111_2))
private theorem idp00001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111011.list =
    C ((2:ℤ)^408) * horner X vp00001110111.list + horner X ep00001110111.list := by
  exact edge_identity (B := (2:ℤ)^678) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110111 : Branch 1 (-471761639/8000000 : ℚ) vp0000111011 := by
  apply branch_checked idp00001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-471761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-475761639/4000000 : ℚ) by norm_num]
  exact coverp00001110111
theorem coverp0000111011 : Covers (-471761639/8000000 : ℚ) vp0000111011 := join_branches bp00001110110 bp00001110111
private noncomputable def vp00001110101111_0 : Blocks := edgeBlocks% "full/vectors/00001110101111-V-0000.bin"
noncomputable def vp00001110101111 : Blocks := vp00001110101111_0
theorem coverp00001110101111 : Covers (-471261639/500000 : ℚ) vp00001110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110101110_0 : Blocks := edgeBlocks% "full/vectors/00001110101110-V-0000.bin"
noncomputable def vp00001110101110 : Blocks := vp00001110101110_0
theorem coverp00001110101110 : Covers (-470761639/500000 : ℚ) vp00001110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010111_0 : Blocks := edgeBlocks% "full/vectors/0000111010111-V-0000.bin"
noncomputable def vp0000111010111 : Blocks := vp0000111010111_0
private theorem bp00001110101110 : Branch 0 (-470761639/1000000 : ℚ) vp0000111010111 := by
  apply branch_left_normalized (c:=vp00001110101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-470761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-470761639/500000 : ℚ) by norm_num]
  exact coverp00001110101110
private noncomputable def ep00001110101111_0 : Blocks := edgeBlocks% "full/vectors/00001110101111-E-0000.bin"
noncomputable def ep00001110101111 : Blocks := ep00001110101111_0
private theorem idp00001110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010111.list =
    C ((2:ℤ)^68) * horner X vp00001110101111.list + horner X ep00001110101111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110101111 : Branch 1 (-470761639/1000000 : ℚ) vp0000111010111 := by
  apply branch_checked idp00001110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-470761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-471261639/500000 : ℚ) by norm_num]
  exact coverp00001110101111
theorem coverp0000111010111 : Covers (-470761639/1000000 : ℚ) vp0000111010111 := join_branches bp00001110101110 bp00001110101111
private noncomputable def vp00001110101101_0 : Blocks := edgeBlocks% "full/vectors/00001110101101-V-0000.bin"
noncomputable def vp00001110101101 : Blocks := vp00001110101101_0
theorem coverp00001110101101 : Covers (-470261639/500000 : ℚ) vp00001110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110101100_0 : Blocks := edgeBlocks% "full/vectors/00001110101100-V-0000.bin"
noncomputable def vp00001110101100 : Blocks := vp00001110101100_0
theorem coverp00001110101100 : Covers (-469761639/500000 : ℚ) vp00001110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010110_0 : Blocks := edgeBlocks% "full/vectors/0000111010110-V-0000.bin"
noncomputable def vp0000111010110 : Blocks := vp0000111010110_0
private theorem bp00001110101100 : Branch 0 (-469761639/1000000 : ℚ) vp0000111010110 := by
  apply branch_left_normalized (c:=vp00001110101100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-469761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-469761639/500000 : ℚ) by norm_num]
  exact coverp00001110101100
private noncomputable def ep00001110101101_0 : Blocks := edgeBlocks% "full/vectors/00001110101101-E-0000.bin"
noncomputable def ep00001110101101 : Blocks := ep00001110101101_0
private theorem idp00001110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010110.list =
    C ((2:ℤ)^69) * horner X vp00001110101101.list + horner X ep00001110101101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110101101 : Branch 1 (-469761639/1000000 : ℚ) vp0000111010110 := by
  apply branch_checked idp00001110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-469761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-470261639/500000 : ℚ) by norm_num]
  exact coverp00001110101101
theorem coverp0000111010110 : Covers (-469761639/1000000 : ℚ) vp0000111010110 := join_branches bp00001110101100 bp00001110101101
private noncomputable def vp000011101011_0 : Blocks := edgeBlocks% "full/vectors/000011101011-V-0000.bin"
noncomputable def vp000011101011 : Blocks := vp000011101011_0
private theorem bp0000111010110 : Branch 0 (-469761639/2000000 : ℚ) vp000011101011 := by
  apply branch_left_normalized (c:=vp0000111010110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-469761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-469761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010110
private noncomputable def ep0000111010111_0 : Blocks := edgeBlocks% "full/vectors/0000111010111-E-0000.bin"
noncomputable def ep0000111010111 : Blocks := ep0000111010111_0
private theorem idp0000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101011.list =
    C ((2:ℤ)^119) * horner X vp0000111010111.list + horner X ep0000111010111.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111010111 : Branch 1 (-469761639/2000000 : ℚ) vp000011101011 := by
  apply branch_checked idp0000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-469761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-470761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010111
theorem coverp000011101011 : Covers (-469761639/2000000 : ℚ) vp000011101011 := join_branches bp0000111010110 bp0000111010111
private noncomputable def vp00001110101011_0 : Blocks := edgeBlocks% "full/vectors/00001110101011-V-0000.bin"
noncomputable def vp00001110101011 : Blocks := vp00001110101011_0
theorem coverp00001110101011 : Covers (-469261639/500000 : ℚ) vp00001110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110101010_0 : Blocks := edgeBlocks% "full/vectors/00001110101010-V-0000.bin"
noncomputable def vp00001110101010 : Blocks := vp00001110101010_0
theorem coverp00001110101010 : Covers (-468761639/500000 : ℚ) vp00001110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010101_0 : Blocks := edgeBlocks% "full/vectors/0000111010101-V-0000.bin"
noncomputable def vp0000111010101 : Blocks := vp0000111010101_0
private theorem bp00001110101010 : Branch 0 (-468761639/1000000 : ℚ) vp0000111010101 := by
  apply branch_left_normalized (c:=vp00001110101010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-468761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-468761639/500000 : ℚ) by norm_num]
  exact coverp00001110101010
private noncomputable def ep00001110101011_0 : Blocks := edgeBlocks% "full/vectors/00001110101011-E-0000.bin"
noncomputable def ep00001110101011 : Blocks := ep00001110101011_0
private theorem idp00001110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010101.list =
    C ((2:ℤ)^69) * horner X vp00001110101011.list + horner X ep00001110101011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110101011 : Branch 1 (-468761639/1000000 : ℚ) vp0000111010101 := by
  apply branch_checked idp00001110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-468761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-469261639/500000 : ℚ) by norm_num]
  exact coverp00001110101011
theorem coverp0000111010101 : Covers (-468761639/1000000 : ℚ) vp0000111010101 := join_branches bp00001110101010 bp00001110101011
private noncomputable def vp00001110101001_0 : Blocks := edgeBlocks% "full/vectors/00001110101001-V-0000.bin"
noncomputable def vp00001110101001 : Blocks := vp00001110101001_0
theorem coverp00001110101001 : Covers (-468261639/500000 : ℚ) vp00001110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110101000_0 : Blocks := edgeBlocks% "full/vectors/00001110101000-V-0000.bin"
noncomputable def vp00001110101000 : Blocks := vp00001110101000_0
theorem coverp00001110101000 : Covers (-467761639/500000 : ℚ) vp00001110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010100_0 : Blocks := edgeBlocks% "full/vectors/0000111010100-V-0000.bin"
noncomputable def vp0000111010100 : Blocks := vp0000111010100_0
private theorem bp00001110101000 : Branch 0 (-467761639/1000000 : ℚ) vp0000111010100 := by
  apply branch_left_normalized (c:=vp00001110101000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-467761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-467761639/500000 : ℚ) by norm_num]
  exact coverp00001110101000
private noncomputable def ep00001110101001_0 : Blocks := edgeBlocks% "full/vectors/00001110101001-E-0000.bin"
noncomputable def ep00001110101001 : Blocks := ep00001110101001_0
private theorem idp00001110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010100.list =
    C ((2:ℤ)^70) * horner X vp00001110101001.list + horner X ep00001110101001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110101001 : Branch 1 (-467761639/1000000 : ℚ) vp0000111010100 := by
  apply branch_checked idp00001110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-467761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-468261639/500000 : ℚ) by norm_num]
  exact coverp00001110101001
theorem coverp0000111010100 : Covers (-467761639/1000000 : ℚ) vp0000111010100 := join_branches bp00001110101000 bp00001110101001
private noncomputable def vp000011101010_0 : Blocks := edgeBlocks% "full/vectors/000011101010-V-0000.bin"
noncomputable def vp000011101010 : Blocks := vp000011101010_0
private theorem bp0000111010100 : Branch 0 (-467761639/2000000 : ℚ) vp000011101010 := by
  apply branch_left_normalized (c:=vp0000111010100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-467761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-467761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010100
private noncomputable def ep0000111010101_0 : Blocks := edgeBlocks% "full/vectors/0000111010101-E-0000.bin"
noncomputable def ep0000111010101 : Blocks := ep0000111010101_0
private theorem idp0000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101010.list =
    C ((2:ℤ)^119) * horner X vp0000111010101.list + horner X ep0000111010101.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111010101 : Branch 1 (-467761639/2000000 : ℚ) vp000011101010 := by
  apply branch_checked idp0000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-467761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-468761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010101
theorem coverp000011101010 : Covers (-467761639/2000000 : ℚ) vp000011101010 := join_branches bp0000111010100 bp0000111010101
private noncomputable def vp00001110101_0 : Blocks := edgeBlocks% "full/vectors/00001110101-V-0000.bin"
private noncomputable def vp00001110101_1 : Blocks := edgeBlocks% "full/vectors/00001110101-V-0001.bin"
noncomputable def vp00001110101 : Blocks := (Blocks.join vp00001110101_0 vp00001110101_1)
private theorem bp000011101010 : Branch 0 (-467761639/4000000 : ℚ) vp00001110101 := by
  apply branch_left_normalized (c:=vp000011101010) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-467761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-467761639/2000000 : ℚ) by norm_num]
  exact coverp000011101010
private noncomputable def ep000011101011_0 : Blocks := edgeBlocks% "full/vectors/000011101011-E-0000.bin"
private noncomputable def ep000011101011_1 : Blocks := edgeBlocks% "full/vectors/000011101011-E-0001.bin"
noncomputable def ep000011101011 : Blocks := (Blocks.join ep000011101011_0 ep000011101011_1)
private theorem idp000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110101.list =
    C ((2:ℤ)^215) * horner X vp000011101011.list + horner X ep000011101011.list := by
  exact edge_identity (B := (2:ℤ)^401) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011101011 : Branch 1 (-467761639/4000000 : ℚ) vp00001110101 := by
  apply branch_checked idp000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-467761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-469761639/2000000 : ℚ) by norm_num]
  exact coverp000011101011
theorem coverp00001110101 : Covers (-467761639/4000000 : ℚ) vp00001110101 := join_branches bp000011101010 bp000011101011
private noncomputable def vp00001110100111_0 : Blocks := edgeBlocks% "full/vectors/00001110100111-V-0000.bin"
noncomputable def vp00001110100111 : Blocks := vp00001110100111_0
theorem coverp00001110100111 : Covers (-467261639/500000 : ℚ) vp00001110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110100110_0 : Blocks := edgeBlocks% "full/vectors/00001110100110-V-0000.bin"
noncomputable def vp00001110100110 : Blocks := vp00001110100110_0
theorem coverp00001110100110 : Covers (-466761639/500000 : ℚ) vp00001110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010011_0 : Blocks := edgeBlocks% "full/vectors/0000111010011-V-0000.bin"
noncomputable def vp0000111010011 : Blocks := vp0000111010011_0
private theorem bp00001110100110 : Branch 0 (-466761639/1000000 : ℚ) vp0000111010011 := by
  apply branch_left_normalized (c:=vp00001110100110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-466761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-466761639/500000 : ℚ) by norm_num]
  exact coverp00001110100110
private noncomputable def ep00001110100111_0 : Blocks := edgeBlocks% "full/vectors/00001110100111-E-0000.bin"
noncomputable def ep00001110100111 : Blocks := ep00001110100111_0
private theorem idp00001110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010011.list =
    C ((2:ℤ)^70) * horner X vp00001110100111.list + horner X ep00001110100111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110100111 : Branch 1 (-466761639/1000000 : ℚ) vp0000111010011 := by
  apply branch_checked idp00001110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-466761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-467261639/500000 : ℚ) by norm_num]
  exact coverp00001110100111
theorem coverp0000111010011 : Covers (-466761639/1000000 : ℚ) vp0000111010011 := join_branches bp00001110100110 bp00001110100111
private noncomputable def vp00001110100101_0 : Blocks := edgeBlocks% "full/vectors/00001110100101-V-0000.bin"
noncomputable def vp00001110100101 : Blocks := vp00001110100101_0
theorem coverp00001110100101 : Covers (-466261639/500000 : ℚ) vp00001110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110100100_0 : Blocks := edgeBlocks% "full/vectors/00001110100100-V-0000.bin"
noncomputable def vp00001110100100 : Blocks := vp00001110100100_0
theorem coverp00001110100100 : Covers (-465761639/500000 : ℚ) vp00001110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010010_0 : Blocks := edgeBlocks% "full/vectors/0000111010010-V-0000.bin"
noncomputable def vp0000111010010 : Blocks := vp0000111010010_0
private theorem bp00001110100100 : Branch 0 (-465761639/1000000 : ℚ) vp0000111010010 := by
  apply branch_left_normalized (c:=vp00001110100100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-465761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-465761639/500000 : ℚ) by norm_num]
  exact coverp00001110100100
private noncomputable def ep00001110100101_0 : Blocks := edgeBlocks% "full/vectors/00001110100101-E-0000.bin"
noncomputable def ep00001110100101 : Blocks := ep00001110100101_0
private theorem idp00001110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010010.list =
    C ((2:ℤ)^69) * horner X vp00001110100101.list + horner X ep00001110100101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110100101 : Branch 1 (-465761639/1000000 : ℚ) vp0000111010010 := by
  apply branch_checked idp00001110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-465761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-466261639/500000 : ℚ) by norm_num]
  exact coverp00001110100101
theorem coverp0000111010010 : Covers (-465761639/1000000 : ℚ) vp0000111010010 := join_branches bp00001110100100 bp00001110100101
private noncomputable def vp000011101001_0 : Blocks := edgeBlocks% "full/vectors/000011101001-V-0000.bin"
noncomputable def vp000011101001 : Blocks := vp000011101001_0
private theorem bp0000111010010 : Branch 0 (-465761639/2000000 : ℚ) vp000011101001 := by
  apply branch_left_normalized (c:=vp0000111010010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-465761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-465761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010010
private noncomputable def ep0000111010011_0 : Blocks := edgeBlocks% "full/vectors/0000111010011-E-0000.bin"
noncomputable def ep0000111010011 : Blocks := ep0000111010011_0
private theorem idp0000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101001.list =
    C ((2:ℤ)^119) * horner X vp0000111010011.list + horner X ep0000111010011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111010011 : Branch 1 (-465761639/2000000 : ℚ) vp000011101001 := by
  apply branch_checked idp0000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-465761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-466761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010011
theorem coverp000011101001 : Covers (-465761639/2000000 : ℚ) vp000011101001 := join_branches bp0000111010010 bp0000111010011
private noncomputable def vp00001110100011_0 : Blocks := edgeBlocks% "full/vectors/00001110100011-V-0000.bin"
noncomputable def vp00001110100011 : Blocks := vp00001110100011_0
theorem coverp00001110100011 : Covers (-465261639/500000 : ℚ) vp00001110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110100010_0 : Blocks := edgeBlocks% "full/vectors/00001110100010-V-0000.bin"
noncomputable def vp00001110100010 : Blocks := vp00001110100010_0
theorem coverp00001110100010 : Covers (-464761639/500000 : ℚ) vp00001110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010001_0 : Blocks := edgeBlocks% "full/vectors/0000111010001-V-0000.bin"
noncomputable def vp0000111010001 : Blocks := vp0000111010001_0
private theorem bp00001110100010 : Branch 0 (-464761639/1000000 : ℚ) vp0000111010001 := by
  apply branch_left_normalized (c:=vp00001110100010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-464761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-464761639/500000 : ℚ) by norm_num]
  exact coverp00001110100010
private noncomputable def ep00001110100011_0 : Blocks := edgeBlocks% "full/vectors/00001110100011-E-0000.bin"
noncomputable def ep00001110100011 : Blocks := ep00001110100011_0
private theorem idp00001110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010001.list =
    C ((2:ℤ)^69) * horner X vp00001110100011.list + horner X ep00001110100011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110100011 : Branch 1 (-464761639/1000000 : ℚ) vp0000111010001 := by
  apply branch_checked idp00001110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-464761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-465261639/500000 : ℚ) by norm_num]
  exact coverp00001110100011
theorem coverp0000111010001 : Covers (-464761639/1000000 : ℚ) vp0000111010001 := join_branches bp00001110100010 bp00001110100011
private noncomputable def vp00001110100001_0 : Blocks := edgeBlocks% "full/vectors/00001110100001-V-0000.bin"
noncomputable def vp00001110100001 : Blocks := vp00001110100001_0
theorem coverp00001110100001 : Covers (-464261639/500000 : ℚ) vp00001110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110100000_0 : Blocks := edgeBlocks% "full/vectors/00001110100000-V-0000.bin"
noncomputable def vp00001110100000 : Blocks := vp00001110100000_0
theorem coverp00001110100000 : Covers (-463761639/500000 : ℚ) vp00001110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111010000_0 : Blocks := edgeBlocks% "full/vectors/0000111010000-V-0000.bin"
noncomputable def vp0000111010000 : Blocks := vp0000111010000_0
private theorem bp00001110100000 : Branch 0 (-463761639/1000000 : ℚ) vp0000111010000 := by
  apply branch_left_normalized (c:=vp00001110100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-463761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-463761639/500000 : ℚ) by norm_num]
  exact coverp00001110100000
private noncomputable def ep00001110100001_0 : Blocks := edgeBlocks% "full/vectors/00001110100001-E-0000.bin"
noncomputable def ep00001110100001 : Blocks := ep00001110100001_0
private theorem idp00001110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010000.list =
    C ((2:ℤ)^70) * horner X vp00001110100001.list + horner X ep00001110100001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110100001 : Branch 1 (-463761639/1000000 : ℚ) vp0000111010000 := by
  apply branch_checked idp00001110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-463761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-464261639/500000 : ℚ) by norm_num]
  exact coverp00001110100001
theorem coverp0000111010000 : Covers (-463761639/1000000 : ℚ) vp0000111010000 := join_branches bp00001110100000 bp00001110100001
private noncomputable def vp000011101000_0 : Blocks := edgeBlocks% "full/vectors/000011101000-V-0000.bin"
noncomputable def vp000011101000 : Blocks := vp000011101000_0
private theorem bp0000111010000 : Branch 0 (-463761639/2000000 : ℚ) vp000011101000 := by
  apply branch_left_normalized (c:=vp0000111010000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-463761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-463761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010000
private noncomputable def ep0000111010001_0 : Blocks := edgeBlocks% "full/vectors/0000111010001-E-0000.bin"
noncomputable def ep0000111010001 : Blocks := ep0000111010001_0
private theorem idp0000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101000.list =
    C ((2:ℤ)^120) * horner X vp0000111010001.list + horner X ep0000111010001.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111010001 : Branch 1 (-463761639/2000000 : ℚ) vp000011101000 := by
  apply branch_checked idp0000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-463761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-464761639/1000000 : ℚ) by norm_num]
  exact coverp0000111010001
theorem coverp000011101000 : Covers (-463761639/2000000 : ℚ) vp000011101000 := join_branches bp0000111010000 bp0000111010001
private noncomputable def vp00001110100_0 : Blocks := edgeBlocks% "full/vectors/00001110100-V-0000.bin"
private noncomputable def vp00001110100_1 : Blocks := edgeBlocks% "full/vectors/00001110100-V-0001.bin"
noncomputable def vp00001110100 : Blocks := (Blocks.join vp00001110100_0 vp00001110100_1)
private theorem bp000011101000 : Branch 0 (-463761639/4000000 : ℚ) vp00001110100 := by
  apply branch_left_normalized (c:=vp000011101000) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-463761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-463761639/2000000 : ℚ) by norm_num]
  exact coverp000011101000
private noncomputable def ep000011101001_0 : Blocks := edgeBlocks% "full/vectors/000011101001-E-0000.bin"
private noncomputable def ep000011101001_1 : Blocks := edgeBlocks% "full/vectors/000011101001-E-0001.bin"
noncomputable def ep000011101001 : Blocks := (Blocks.join ep000011101001_0 ep000011101001_1)
private theorem idp000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110100.list =
    C ((2:ℤ)^216) * horner X vp000011101001.list + horner X ep000011101001.list := by
  exact edge_identity (B := (2:ℤ)^403) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011101001 : Branch 1 (-463761639/4000000 : ℚ) vp00001110100 := by
  apply branch_checked idp000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-463761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-465761639/2000000 : ℚ) by norm_num]
  exact coverp000011101001
theorem coverp00001110100 : Covers (-463761639/4000000 : ℚ) vp00001110100 := join_branches bp000011101000 bp000011101001
private noncomputable def vp0000111010_0 : Blocks := edgeBlocks% "full/vectors/0000111010-V-0000.bin"
private noncomputable def vp0000111010_1 : Blocks := edgeBlocks% "full/vectors/0000111010-V-0001.bin"
private noncomputable def vp0000111010_2 : Blocks := edgeBlocks% "full/vectors/0000111010-V-0002.bin"
private noncomputable def vp0000111010_3 : Blocks := edgeBlocks% "full/vectors/0000111010-V-0003.bin"
noncomputable def vp0000111010 : Blocks := (Blocks.join (Blocks.join vp0000111010_0 vp0000111010_1) (Blocks.join vp0000111010_2 vp0000111010_3))
private theorem bp00001110100 : Branch 0 (-463761639/8000000 : ℚ) vp0000111010 := by
  apply branch_left_normalized (c:=vp00001110100) (k:=0) (m:=204) (by decide +kernel)
  rw [show 2*(-463761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-463761639/4000000 : ℚ) by norm_num]
  exact coverp00001110100
private noncomputable def ep00001110101_0 : Blocks := edgeBlocks% "full/vectors/00001110101-E-0000.bin"
private noncomputable def ep00001110101_1 : Blocks := edgeBlocks% "full/vectors/00001110101-E-0001.bin"
private noncomputable def ep00001110101_2 : Blocks := edgeBlocks% "full/vectors/00001110101-E-0002.bin"
private noncomputable def ep00001110101_3 : Blocks := edgeBlocks% "full/vectors/00001110101-E-0003.bin"
noncomputable def ep00001110101 : Blocks := (Blocks.join (Blocks.join ep00001110101_0 ep00001110101_1) (Blocks.join ep00001110101_2 ep00001110101_3))
private theorem idp00001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111010.list =
    C ((2:ℤ)^411) * horner X vp00001110101.list + horner X ep00001110101.list := by
  exact edge_identity (B := (2:ℤ)^682) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110101 : Branch 1 (-463761639/8000000 : ℚ) vp0000111010 := by
  apply branch_checked idp00001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-463761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-467761639/4000000 : ℚ) by norm_num]
  exact coverp00001110101
theorem coverp0000111010 : Covers (-463761639/8000000 : ℚ) vp0000111010 := join_branches bp00001110100 bp00001110101
private noncomputable def vp000011101_0 : Blocks := edgeBlocks% "full/vectors/000011101-V-0000.bin"
private noncomputable def vp000011101_1 : Blocks := edgeBlocks% "full/vectors/000011101-V-0001.bin"
private noncomputable def vp000011101_2 : Blocks := edgeBlocks% "full/vectors/000011101-V-0002.bin"
private noncomputable def vp000011101_3 : Blocks := edgeBlocks% "full/vectors/000011101-V-0003.bin"
private noncomputable def vp000011101_4 : Blocks := edgeBlocks% "full/vectors/000011101-V-0004.bin"
private noncomputable def vp000011101_5 : Blocks := edgeBlocks% "full/vectors/000011101-V-0005.bin"
noncomputable def vp000011101 : Blocks := (Blocks.join (Blocks.join vp000011101_0 (Blocks.join vp000011101_1 vp000011101_2)) (Blocks.join vp000011101_3 (Blocks.join vp000011101_4 vp000011101_5)))
private theorem bp0000111010 : Branch 0 (-463761639/16000000 : ℚ) vp000011101 := by
  apply branch_left_normalized (c:=vp0000111010) (k:=0) (m:=386) (by decide +kernel)
  rw [show 2*(-463761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-463761639/8000000 : ℚ) by norm_num]
  exact coverp0000111010
private noncomputable def ep0000111011_0 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0000.bin"
private noncomputable def ep0000111011_1 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0001.bin"
private noncomputable def ep0000111011_2 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0002.bin"
private noncomputable def ep0000111011_3 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0003.bin"
private noncomputable def ep0000111011_4 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0004.bin"
private noncomputable def ep0000111011_5 : Blocks := edgeBlocks% "full/vectors/0000111011-E-0005.bin"
noncomputable def ep0000111011 : Blocks := (Blocks.join (Blocks.join ep0000111011_0 (Blocks.join ep0000111011_1 ep0000111011_2)) (Blocks.join ep0000111011_3 (Blocks.join ep0000111011_4 ep0000111011_5)))
private theorem idp0000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011101.list =
    C ((2:ℤ)^792) * horner X vp0000111011.list + horner X ep0000111011.list := by
  exact edge_identity (B := (2:ℤ)^1234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111011 : Branch 1 (-463761639/16000000 : ℚ) vp000011101 := by
  apply branch_checked idp0000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-463761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-471761639/8000000 : ℚ) by norm_num]
  exact coverp0000111011
theorem coverp000011101 : Covers (-463761639/16000000 : ℚ) vp000011101 := join_branches bp0000111010 bp0000111011
private noncomputable def vp00001110011111_0 : Blocks := edgeBlocks% "full/vectors/00001110011111-V-0000.bin"
noncomputable def vp00001110011111 : Blocks := vp00001110011111_0
theorem coverp00001110011111 : Covers (-463261639/500000 : ℚ) vp00001110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110011110_0 : Blocks := edgeBlocks% "full/vectors/00001110011110-V-0000.bin"
noncomputable def vp00001110011110 : Blocks := vp00001110011110_0
theorem coverp00001110011110 : Covers (-462761639/500000 : ℚ) vp00001110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000111001111-V-0000.bin"
noncomputable def vp0000111001111 : Blocks := vp0000111001111_0
private theorem bp00001110011110 : Branch 0 (-462761639/1000000 : ℚ) vp0000111001111 := by
  apply branch_left_normalized (c:=vp00001110011110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-462761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-462761639/500000 : ℚ) by norm_num]
  exact coverp00001110011110
private noncomputable def ep00001110011111_0 : Blocks := edgeBlocks% "full/vectors/00001110011111-E-0000.bin"
noncomputable def ep00001110011111 : Blocks := ep00001110011111_0
private theorem idp00001110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001111.list =
    C ((2:ℤ)^70) * horner X vp00001110011111.list + horner X ep00001110011111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110011111 : Branch 1 (-462761639/1000000 : ℚ) vp0000111001111 := by
  apply branch_checked idp00001110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-462761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-463261639/500000 : ℚ) by norm_num]
  exact coverp00001110011111
theorem coverp0000111001111 : Covers (-462761639/1000000 : ℚ) vp0000111001111 := join_branches bp00001110011110 bp00001110011111
private noncomputable def vp00001110011101_0 : Blocks := edgeBlocks% "full/vectors/00001110011101-V-0000.bin"
noncomputable def vp00001110011101 : Blocks := vp00001110011101_0
theorem coverp00001110011101 : Covers (-462261639/500000 : ℚ) vp00001110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110011100_0 : Blocks := edgeBlocks% "full/vectors/00001110011100-V-0000.bin"
noncomputable def vp00001110011100 : Blocks := vp00001110011100_0
theorem coverp00001110011100 : Covers (-461761639/500000 : ℚ) vp00001110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001110_0 : Blocks := edgeBlocks% "full/vectors/0000111001110-V-0000.bin"
noncomputable def vp0000111001110 : Blocks := vp0000111001110_0
private theorem bp00001110011100 : Branch 0 (-461761639/1000000 : ℚ) vp0000111001110 := by
  apply branch_left_normalized (c:=vp00001110011100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-461761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-461761639/500000 : ℚ) by norm_num]
  exact coverp00001110011100
private noncomputable def ep00001110011101_0 : Blocks := edgeBlocks% "full/vectors/00001110011101-E-0000.bin"
noncomputable def ep00001110011101 : Blocks := ep00001110011101_0
private theorem idp00001110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001110.list =
    C ((2:ℤ)^70) * horner X vp00001110011101.list + horner X ep00001110011101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110011101 : Branch 1 (-461761639/1000000 : ℚ) vp0000111001110 := by
  apply branch_checked idp00001110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-461761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-462261639/500000 : ℚ) by norm_num]
  exact coverp00001110011101
theorem coverp0000111001110 : Covers (-461761639/1000000 : ℚ) vp0000111001110 := join_branches bp00001110011100 bp00001110011101
private noncomputable def vp000011100111_0 : Blocks := edgeBlocks% "full/vectors/000011100111-V-0000.bin"
noncomputable def vp000011100111 : Blocks := vp000011100111_0
private theorem bp0000111001110 : Branch 0 (-461761639/2000000 : ℚ) vp000011100111 := by
  apply branch_left_normalized (c:=vp0000111001110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-461761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-461761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001110
private noncomputable def ep0000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000111001111-E-0000.bin"
noncomputable def ep0000111001111 : Blocks := ep0000111001111_0
private theorem idp0000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100111.list =
    C ((2:ℤ)^120) * horner X vp0000111001111.list + horner X ep0000111001111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111001111 : Branch 1 (-461761639/2000000 : ℚ) vp000011100111 := by
  apply branch_checked idp0000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-461761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-462761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001111
theorem coverp000011100111 : Covers (-461761639/2000000 : ℚ) vp000011100111 := join_branches bp0000111001110 bp0000111001111
private noncomputable def vp00001110011011_0 : Blocks := edgeBlocks% "full/vectors/00001110011011-V-0000.bin"
noncomputable def vp00001110011011 : Blocks := vp00001110011011_0
theorem coverp00001110011011 : Covers (-461261639/500000 : ℚ) vp00001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110011010_0 : Blocks := edgeBlocks% "full/vectors/00001110011010-V-0000.bin"
noncomputable def vp00001110011010 : Blocks := vp00001110011010_0
theorem coverp00001110011010 : Covers (-460761639/500000 : ℚ) vp00001110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001101_0 : Blocks := edgeBlocks% "full/vectors/0000111001101-V-0000.bin"
noncomputable def vp0000111001101 : Blocks := vp0000111001101_0
private theorem bp00001110011010 : Branch 0 (-460761639/1000000 : ℚ) vp0000111001101 := by
  apply branch_left_normalized (c:=vp00001110011010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-460761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-460761639/500000 : ℚ) by norm_num]
  exact coverp00001110011010
private noncomputable def ep00001110011011_0 : Blocks := edgeBlocks% "full/vectors/00001110011011-E-0000.bin"
noncomputable def ep00001110011011 : Blocks := ep00001110011011_0
private theorem idp00001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001101.list =
    C ((2:ℤ)^70) * horner X vp00001110011011.list + horner X ep00001110011011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110011011 : Branch 1 (-460761639/1000000 : ℚ) vp0000111001101 := by
  apply branch_checked idp00001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-460761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-461261639/500000 : ℚ) by norm_num]
  exact coverp00001110011011
theorem coverp0000111001101 : Covers (-460761639/1000000 : ℚ) vp0000111001101 := join_branches bp00001110011010 bp00001110011011
private noncomputable def vp00001110011001_0 : Blocks := edgeBlocks% "full/vectors/00001110011001-V-0000.bin"
noncomputable def vp00001110011001 : Blocks := vp00001110011001_0
theorem coverp00001110011001 : Covers (-460261639/500000 : ℚ) vp00001110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110011000_0 : Blocks := edgeBlocks% "full/vectors/00001110011000-V-0000.bin"
noncomputable def vp00001110011000 : Blocks := vp00001110011000_0
theorem coverp00001110011000 : Covers (-459761639/500000 : ℚ) vp00001110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001100_0 : Blocks := edgeBlocks% "full/vectors/0000111001100-V-0000.bin"
noncomputable def vp0000111001100 : Blocks := vp0000111001100_0
private theorem bp00001110011000 : Branch 0 (-459761639/1000000 : ℚ) vp0000111001100 := by
  apply branch_left_normalized (c:=vp00001110011000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-459761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-459761639/500000 : ℚ) by norm_num]
  exact coverp00001110011000
private noncomputable def ep00001110011001_0 : Blocks := edgeBlocks% "full/vectors/00001110011001-E-0000.bin"
noncomputable def ep00001110011001 : Blocks := ep00001110011001_0
private theorem idp00001110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001100.list =
    C ((2:ℤ)^69) * horner X vp00001110011001.list + horner X ep00001110011001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110011001 : Branch 1 (-459761639/1000000 : ℚ) vp0000111001100 := by
  apply branch_checked idp00001110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-459761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-460261639/500000 : ℚ) by norm_num]
  exact coverp00001110011001
theorem coverp0000111001100 : Covers (-459761639/1000000 : ℚ) vp0000111001100 := join_branches bp00001110011000 bp00001110011001
private noncomputable def vp000011100110_0 : Blocks := edgeBlocks% "full/vectors/000011100110-V-0000.bin"
noncomputable def vp000011100110 : Blocks := vp000011100110_0
private theorem bp0000111001100 : Branch 0 (-459761639/2000000 : ℚ) vp000011100110 := by
  apply branch_left_normalized (c:=vp0000111001100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-459761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-459761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001100
private noncomputable def ep0000111001101_0 : Blocks := edgeBlocks% "full/vectors/0000111001101-E-0000.bin"
noncomputable def ep0000111001101 : Blocks := ep0000111001101_0
private theorem idp0000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100110.list =
    C ((2:ℤ)^119) * horner X vp0000111001101.list + horner X ep0000111001101.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111001101 : Branch 1 (-459761639/2000000 : ℚ) vp000011100110 := by
  apply branch_checked idp0000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-459761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-460761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001101
theorem coverp000011100110 : Covers (-459761639/2000000 : ℚ) vp000011100110 := join_branches bp0000111001100 bp0000111001101
private noncomputable def vp00001110011_0 : Blocks := edgeBlocks% "full/vectors/00001110011-V-0000.bin"
private noncomputable def vp00001110011_1 : Blocks := edgeBlocks% "full/vectors/00001110011-V-0001.bin"
noncomputable def vp00001110011 : Blocks := (Blocks.join vp00001110011_0 vp00001110011_1)
private theorem bp000011100110 : Branch 0 (-459761639/4000000 : ℚ) vp00001110011 := by
  apply branch_left_normalized (c:=vp000011100110) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-459761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-459761639/2000000 : ℚ) by norm_num]
  exact coverp000011100110
private noncomputable def ep000011100111_0 : Blocks := edgeBlocks% "full/vectors/000011100111-E-0000.bin"
private noncomputable def ep000011100111_1 : Blocks := edgeBlocks% "full/vectors/000011100111-E-0001.bin"
noncomputable def ep000011100111 : Blocks := (Blocks.join ep000011100111_0 ep000011100111_1)
private theorem idp000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110011.list =
    C ((2:ℤ)^219) * horner X vp000011100111.list + horner X ep000011100111.list := by
  exact edge_identity (B := (2:ℤ)^406) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011100111 : Branch 1 (-459761639/4000000 : ℚ) vp00001110011 := by
  apply branch_checked idp000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-459761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-461761639/2000000 : ℚ) by norm_num]
  exact coverp000011100111
theorem coverp00001110011 : Covers (-459761639/4000000 : ℚ) vp00001110011 := join_branches bp000011100110 bp000011100111
private noncomputable def vp00001110010111_0 : Blocks := edgeBlocks% "full/vectors/00001110010111-V-0000.bin"
noncomputable def vp00001110010111 : Blocks := vp00001110010111_0
theorem coverp00001110010111 : Covers (-459261639/500000 : ℚ) vp00001110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110010110_0 : Blocks := edgeBlocks% "full/vectors/00001110010110-V-0000.bin"
noncomputable def vp00001110010110 : Blocks := vp00001110010110_0
theorem coverp00001110010110 : Covers (-458761639/500000 : ℚ) vp00001110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000111001011-V-0000.bin"
noncomputable def vp0000111001011 : Blocks := vp0000111001011_0
private theorem bp00001110010110 : Branch 0 (-458761639/1000000 : ℚ) vp0000111001011 := by
  apply branch_left_normalized (c:=vp00001110010110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-458761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-458761639/500000 : ℚ) by norm_num]
  exact coverp00001110010110
private noncomputable def ep00001110010111_0 : Blocks := edgeBlocks% "full/vectors/00001110010111-E-0000.bin"
noncomputable def ep00001110010111 : Blocks := ep00001110010111_0
private theorem idp00001110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001011.list =
    C ((2:ℤ)^70) * horner X vp00001110010111.list + horner X ep00001110010111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110010111 : Branch 1 (-458761639/1000000 : ℚ) vp0000111001011 := by
  apply branch_checked idp00001110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-458761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-459261639/500000 : ℚ) by norm_num]
  exact coverp00001110010111
theorem coverp0000111001011 : Covers (-458761639/1000000 : ℚ) vp0000111001011 := join_branches bp00001110010110 bp00001110010111
private noncomputable def vp00001110010101_0 : Blocks := edgeBlocks% "full/vectors/00001110010101-V-0000.bin"
noncomputable def vp00001110010101 : Blocks := vp00001110010101_0
theorem coverp00001110010101 : Covers (-458261639/500000 : ℚ) vp00001110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110010100_0 : Blocks := edgeBlocks% "full/vectors/00001110010100-V-0000.bin"
noncomputable def vp00001110010100 : Blocks := vp00001110010100_0
theorem coverp00001110010100 : Covers (-457761639/500000 : ℚ) vp00001110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001010_0 : Blocks := edgeBlocks% "full/vectors/0000111001010-V-0000.bin"
noncomputable def vp0000111001010 : Blocks := vp0000111001010_0
private theorem bp00001110010100 : Branch 0 (-457761639/1000000 : ℚ) vp0000111001010 := by
  apply branch_left_normalized (c:=vp00001110010100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-457761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-457761639/500000 : ℚ) by norm_num]
  exact coverp00001110010100
private noncomputable def ep00001110010101_0 : Blocks := edgeBlocks% "full/vectors/00001110010101-E-0000.bin"
noncomputable def ep00001110010101 : Blocks := ep00001110010101_0
private theorem idp00001110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001010.list =
    C ((2:ℤ)^69) * horner X vp00001110010101.list + horner X ep00001110010101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110010101 : Branch 1 (-457761639/1000000 : ℚ) vp0000111001010 := by
  apply branch_checked idp00001110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-457761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-458261639/500000 : ℚ) by norm_num]
  exact coverp00001110010101
theorem coverp0000111001010 : Covers (-457761639/1000000 : ℚ) vp0000111001010 := join_branches bp00001110010100 bp00001110010101
private noncomputable def vp000011100101_0 : Blocks := edgeBlocks% "full/vectors/000011100101-V-0000.bin"
noncomputable def vp000011100101 : Blocks := vp000011100101_0
private theorem bp0000111001010 : Branch 0 (-457761639/2000000 : ℚ) vp000011100101 := by
  apply branch_left_normalized (c:=vp0000111001010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-457761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-457761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001010
private noncomputable def ep0000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000111001011-E-0000.bin"
noncomputable def ep0000111001011 : Blocks := ep0000111001011_0
private theorem idp0000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100101.list =
    C ((2:ℤ)^119) * horner X vp0000111001011.list + horner X ep0000111001011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111001011 : Branch 1 (-457761639/2000000 : ℚ) vp000011100101 := by
  apply branch_checked idp0000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-457761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-458761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001011
theorem coverp000011100101 : Covers (-457761639/2000000 : ℚ) vp000011100101 := join_branches bp0000111001010 bp0000111001011
private noncomputable def vp00001110010011_0 : Blocks := edgeBlocks% "full/vectors/00001110010011-V-0000.bin"
noncomputable def vp00001110010011 : Blocks := vp00001110010011_0
theorem coverp00001110010011 : Covers (-457261639/500000 : ℚ) vp00001110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110010010_0 : Blocks := edgeBlocks% "full/vectors/00001110010010-V-0000.bin"
noncomputable def vp00001110010010 : Blocks := vp00001110010010_0
theorem coverp00001110010010 : Covers (-456761639/500000 : ℚ) vp00001110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001001_0 : Blocks := edgeBlocks% "full/vectors/0000111001001-V-0000.bin"
noncomputable def vp0000111001001 : Blocks := vp0000111001001_0
private theorem bp00001110010010 : Branch 0 (-456761639/1000000 : ℚ) vp0000111001001 := by
  apply branch_left_normalized (c:=vp00001110010010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-456761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-456761639/500000 : ℚ) by norm_num]
  exact coverp00001110010010
private noncomputable def ep00001110010011_0 : Blocks := edgeBlocks% "full/vectors/00001110010011-E-0000.bin"
noncomputable def ep00001110010011 : Blocks := ep00001110010011_0
private theorem idp00001110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001001.list =
    C ((2:ℤ)^69) * horner X vp00001110010011.list + horner X ep00001110010011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110010011 : Branch 1 (-456761639/1000000 : ℚ) vp0000111001001 := by
  apply branch_checked idp00001110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-456761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-457261639/500000 : ℚ) by norm_num]
  exact coverp00001110010011
theorem coverp0000111001001 : Covers (-456761639/1000000 : ℚ) vp0000111001001 := join_branches bp00001110010010 bp00001110010011
private noncomputable def vp00001110010001_0 : Blocks := edgeBlocks% "full/vectors/00001110010001-V-0000.bin"
noncomputable def vp00001110010001 : Blocks := vp00001110010001_0
theorem coverp00001110010001 : Covers (-456261639/500000 : ℚ) vp00001110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110010000_0 : Blocks := edgeBlocks% "full/vectors/00001110010000-V-0000.bin"
noncomputable def vp00001110010000 : Blocks := vp00001110010000_0
theorem coverp00001110010000 : Covers (-455761639/500000 : ℚ) vp00001110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111001000_0 : Blocks := edgeBlocks% "full/vectors/0000111001000-V-0000.bin"
noncomputable def vp0000111001000 : Blocks := vp0000111001000_0
private theorem bp00001110010000 : Branch 0 (-455761639/1000000 : ℚ) vp0000111001000 := by
  apply branch_left_normalized (c:=vp00001110010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-455761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-455761639/500000 : ℚ) by norm_num]
  exact coverp00001110010000
private noncomputable def ep00001110010001_0 : Blocks := edgeBlocks% "full/vectors/00001110010001-E-0000.bin"
noncomputable def ep00001110010001 : Blocks := ep00001110010001_0
private theorem idp00001110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001000.list =
    C ((2:ℤ)^69) * horner X vp00001110010001.list + horner X ep00001110010001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110010001 : Branch 1 (-455761639/1000000 : ℚ) vp0000111001000 := by
  apply branch_checked idp00001110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-455761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-456261639/500000 : ℚ) by norm_num]
  exact coverp00001110010001
theorem coverp0000111001000 : Covers (-455761639/1000000 : ℚ) vp0000111001000 := join_branches bp00001110010000 bp00001110010001
private noncomputable def vp000011100100_0 : Blocks := edgeBlocks% "full/vectors/000011100100-V-0000.bin"
noncomputable def vp000011100100 : Blocks := vp000011100100_0
private theorem bp0000111001000 : Branch 0 (-455761639/2000000 : ℚ) vp000011100100 := by
  apply branch_left_normalized (c:=vp0000111001000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-455761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-455761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001000
private noncomputable def ep0000111001001_0 : Blocks := edgeBlocks% "full/vectors/0000111001001-E-0000.bin"
noncomputable def ep0000111001001 : Blocks := ep0000111001001_0
private theorem idp0000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100100.list =
    C ((2:ℤ)^120) * horner X vp0000111001001.list + horner X ep0000111001001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111001001 : Branch 1 (-455761639/2000000 : ℚ) vp000011100100 := by
  apply branch_checked idp0000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-455761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-456761639/1000000 : ℚ) by norm_num]
  exact coverp0000111001001
theorem coverp000011100100 : Covers (-455761639/2000000 : ℚ) vp000011100100 := join_branches bp0000111001000 bp0000111001001
private noncomputable def vp00001110010_0 : Blocks := edgeBlocks% "full/vectors/00001110010-V-0000.bin"
private noncomputable def vp00001110010_1 : Blocks := edgeBlocks% "full/vectors/00001110010-V-0001.bin"
noncomputable def vp00001110010 : Blocks := (Blocks.join vp00001110010_0 vp00001110010_1)
private theorem bp000011100100 : Branch 0 (-455761639/4000000 : ℚ) vp00001110010 := by
  apply branch_left_normalized (c:=vp000011100100) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-455761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-455761639/2000000 : ℚ) by norm_num]
  exact coverp000011100100
private noncomputable def ep000011100101_0 : Blocks := edgeBlocks% "full/vectors/000011100101-E-0000.bin"
private noncomputable def ep000011100101_1 : Blocks := edgeBlocks% "full/vectors/000011100101-E-0001.bin"
noncomputable def ep000011100101 : Blocks := (Blocks.join ep000011100101_0 ep000011100101_1)
private theorem idp000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110010.list =
    C ((2:ℤ)^219) * horner X vp000011100101.list + horner X ep000011100101.list := by
  exact edge_identity (B := (2:ℤ)^405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011100101 : Branch 1 (-455761639/4000000 : ℚ) vp00001110010 := by
  apply branch_checked idp000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-455761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-457761639/2000000 : ℚ) by norm_num]
  exact coverp000011100101
theorem coverp00001110010 : Covers (-455761639/4000000 : ℚ) vp00001110010 := join_branches bp000011100100 bp000011100101
private noncomputable def vp0000111001_0 : Blocks := edgeBlocks% "full/vectors/0000111001-V-0000.bin"
private noncomputable def vp0000111001_1 : Blocks := edgeBlocks% "full/vectors/0000111001-V-0001.bin"
private noncomputable def vp0000111001_2 : Blocks := edgeBlocks% "full/vectors/0000111001-V-0002.bin"
private noncomputable def vp0000111001_3 : Blocks := edgeBlocks% "full/vectors/0000111001-V-0003.bin"
noncomputable def vp0000111001 : Blocks := (Blocks.join (Blocks.join vp0000111001_0 vp0000111001_1) (Blocks.join vp0000111001_2 vp0000111001_3))
private theorem bp00001110010 : Branch 0 (-455761639/8000000 : ℚ) vp0000111001 := by
  apply branch_left_normalized (c:=vp00001110010) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-455761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-455761639/4000000 : ℚ) by norm_num]
  exact coverp00001110010
private noncomputable def ep00001110011_0 : Blocks := edgeBlocks% "full/vectors/00001110011-E-0000.bin"
private noncomputable def ep00001110011_1 : Blocks := edgeBlocks% "full/vectors/00001110011-E-0001.bin"
private noncomputable def ep00001110011_2 : Blocks := edgeBlocks% "full/vectors/00001110011-E-0002.bin"
private noncomputable def ep00001110011_3 : Blocks := edgeBlocks% "full/vectors/00001110011-E-0003.bin"
noncomputable def ep00001110011 : Blocks := (Blocks.join (Blocks.join ep00001110011_0 ep00001110011_1) (Blocks.join ep00001110011_2 ep00001110011_3))
private theorem idp00001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111001.list =
    C ((2:ℤ)^412) * horner X vp00001110011.list + horner X ep00001110011.list := by
  exact edge_identity (B := (2:ℤ)^686) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110011 : Branch 1 (-455761639/8000000 : ℚ) vp0000111001 := by
  apply branch_checked idp00001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-455761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-459761639/4000000 : ℚ) by norm_num]
  exact coverp00001110011
theorem coverp0000111001 : Covers (-455761639/8000000 : ℚ) vp0000111001 := join_branches bp00001110010 bp00001110011
private noncomputable def vp00001110001111_0 : Blocks := edgeBlocks% "full/vectors/00001110001111-V-0000.bin"
noncomputable def vp00001110001111 : Blocks := vp00001110001111_0
theorem coverp00001110001111 : Covers (-455261639/500000 : ℚ) vp00001110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110001110_0 : Blocks := edgeBlocks% "full/vectors/00001110001110-V-0000.bin"
noncomputable def vp00001110001110 : Blocks := vp00001110001110_0
theorem coverp00001110001110 : Covers (-454761639/500000 : ℚ) vp00001110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000111000111-V-0000.bin"
noncomputable def vp0000111000111 : Blocks := vp0000111000111_0
private theorem bp00001110001110 : Branch 0 (-454761639/1000000 : ℚ) vp0000111000111 := by
  apply branch_left_normalized (c:=vp00001110001110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-454761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-454761639/500000 : ℚ) by norm_num]
  exact coverp00001110001110
private noncomputable def ep00001110001111_0 : Blocks := edgeBlocks% "full/vectors/00001110001111-E-0000.bin"
noncomputable def ep00001110001111 : Blocks := ep00001110001111_0
private theorem idp00001110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000111.list =
    C ((2:ℤ)^70) * horner X vp00001110001111.list + horner X ep00001110001111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110001111 : Branch 1 (-454761639/1000000 : ℚ) vp0000111000111 := by
  apply branch_checked idp00001110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-454761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-455261639/500000 : ℚ) by norm_num]
  exact coverp00001110001111
theorem coverp0000111000111 : Covers (-454761639/1000000 : ℚ) vp0000111000111 := join_branches bp00001110001110 bp00001110001111
private noncomputable def vp00001110001101_0 : Blocks := edgeBlocks% "full/vectors/00001110001101-V-0000.bin"
noncomputable def vp00001110001101 : Blocks := vp00001110001101_0
theorem coverp00001110001101 : Covers (-454261639/500000 : ℚ) vp00001110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110001100_0 : Blocks := edgeBlocks% "full/vectors/00001110001100-V-0000.bin"
noncomputable def vp00001110001100 : Blocks := vp00001110001100_0
theorem coverp00001110001100 : Covers (-453761639/500000 : ℚ) vp00001110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000110_0 : Blocks := edgeBlocks% "full/vectors/0000111000110-V-0000.bin"
noncomputable def vp0000111000110 : Blocks := vp0000111000110_0
private theorem bp00001110001100 : Branch 0 (-453761639/1000000 : ℚ) vp0000111000110 := by
  apply branch_left_normalized (c:=vp00001110001100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-453761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-453761639/500000 : ℚ) by norm_num]
  exact coverp00001110001100
private noncomputable def ep00001110001101_0 : Blocks := edgeBlocks% "full/vectors/00001110001101-E-0000.bin"
noncomputable def ep00001110001101 : Blocks := ep00001110001101_0
private theorem idp00001110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000110.list =
    C ((2:ℤ)^69) * horner X vp00001110001101.list + horner X ep00001110001101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110001101 : Branch 1 (-453761639/1000000 : ℚ) vp0000111000110 := by
  apply branch_checked idp00001110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-453761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-454261639/500000 : ℚ) by norm_num]
  exact coverp00001110001101
theorem coverp0000111000110 : Covers (-453761639/1000000 : ℚ) vp0000111000110 := join_branches bp00001110001100 bp00001110001101
private noncomputable def vp000011100011_0 : Blocks := edgeBlocks% "full/vectors/000011100011-V-0000.bin"
noncomputable def vp000011100011 : Blocks := vp000011100011_0
private theorem bp0000111000110 : Branch 0 (-453761639/2000000 : ℚ) vp000011100011 := by
  apply branch_left_normalized (c:=vp0000111000110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-453761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-453761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000110
private noncomputable def ep0000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000111000111-E-0000.bin"
noncomputable def ep0000111000111 : Blocks := ep0000111000111_0
private theorem idp0000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100011.list =
    C ((2:ℤ)^119) * horner X vp0000111000111.list + horner X ep0000111000111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111000111 : Branch 1 (-453761639/2000000 : ℚ) vp000011100011 := by
  apply branch_checked idp0000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-453761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-454761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000111
theorem coverp000011100011 : Covers (-453761639/2000000 : ℚ) vp000011100011 := join_branches bp0000111000110 bp0000111000111
private noncomputable def vp00001110001011_0 : Blocks := edgeBlocks% "full/vectors/00001110001011-V-0000.bin"
noncomputable def vp00001110001011 : Blocks := vp00001110001011_0
theorem coverp00001110001011 : Covers (-453261639/500000 : ℚ) vp00001110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110001010_0 : Blocks := edgeBlocks% "full/vectors/00001110001010-V-0000.bin"
noncomputable def vp00001110001010 : Blocks := vp00001110001010_0
theorem coverp00001110001010 : Covers (-452761639/500000 : ℚ) vp00001110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000111000101-V-0000.bin"
noncomputable def vp0000111000101 : Blocks := vp0000111000101_0
private theorem bp00001110001010 : Branch 0 (-452761639/1000000 : ℚ) vp0000111000101 := by
  apply branch_left_normalized (c:=vp00001110001010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-452761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-452761639/500000 : ℚ) by norm_num]
  exact coverp00001110001010
private noncomputable def ep00001110001011_0 : Blocks := edgeBlocks% "full/vectors/00001110001011-E-0000.bin"
noncomputable def ep00001110001011 : Blocks := ep00001110001011_0
private theorem idp00001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000101.list =
    C ((2:ℤ)^69) * horner X vp00001110001011.list + horner X ep00001110001011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110001011 : Branch 1 (-452761639/1000000 : ℚ) vp0000111000101 := by
  apply branch_checked idp00001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-452761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-453261639/500000 : ℚ) by norm_num]
  exact coverp00001110001011
theorem coverp0000111000101 : Covers (-452761639/1000000 : ℚ) vp0000111000101 := join_branches bp00001110001010 bp00001110001011
private noncomputable def vp00001110001001_0 : Blocks := edgeBlocks% "full/vectors/00001110001001-V-0000.bin"
noncomputable def vp00001110001001 : Blocks := vp00001110001001_0
theorem coverp00001110001001 : Covers (-452261639/500000 : ℚ) vp00001110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110001000_0 : Blocks := edgeBlocks% "full/vectors/00001110001000-V-0000.bin"
noncomputable def vp00001110001000 : Blocks := vp00001110001000_0
theorem coverp00001110001000 : Covers (-451761639/500000 : ℚ) vp00001110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000100_0 : Blocks := edgeBlocks% "full/vectors/0000111000100-V-0000.bin"
noncomputable def vp0000111000100 : Blocks := vp0000111000100_0
private theorem bp00001110001000 : Branch 0 (-451761639/1000000 : ℚ) vp0000111000100 := by
  apply branch_left_normalized (c:=vp00001110001000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-451761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-451761639/500000 : ℚ) by norm_num]
  exact coverp00001110001000
private noncomputable def ep00001110001001_0 : Blocks := edgeBlocks% "full/vectors/00001110001001-E-0000.bin"
noncomputable def ep00001110001001 : Blocks := ep00001110001001_0
private theorem idp00001110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000100.list =
    C ((2:ℤ)^68) * horner X vp00001110001001.list + horner X ep00001110001001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110001001 : Branch 1 (-451761639/1000000 : ℚ) vp0000111000100 := by
  apply branch_checked idp00001110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-451761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-452261639/500000 : ℚ) by norm_num]
  exact coverp00001110001001
theorem coverp0000111000100 : Covers (-451761639/1000000 : ℚ) vp0000111000100 := join_branches bp00001110001000 bp00001110001001
private noncomputable def vp000011100010_0 : Blocks := edgeBlocks% "full/vectors/000011100010-V-0000.bin"
noncomputable def vp000011100010 : Blocks := vp000011100010_0
private theorem bp0000111000100 : Branch 0 (-451761639/2000000 : ℚ) vp000011100010 := by
  apply branch_left_normalized (c:=vp0000111000100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-451761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-451761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000100
private noncomputable def ep0000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000111000101-E-0000.bin"
noncomputable def ep0000111000101 : Blocks := ep0000111000101_0
private theorem idp0000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100010.list =
    C ((2:ℤ)^117) * horner X vp0000111000101.list + horner X ep0000111000101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111000101 : Branch 1 (-451761639/2000000 : ℚ) vp000011100010 := by
  apply branch_checked idp0000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-451761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-452761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000101
theorem coverp000011100010 : Covers (-451761639/2000000 : ℚ) vp000011100010 := join_branches bp0000111000100 bp0000111000101
private noncomputable def vp00001110001_0 : Blocks := edgeBlocks% "full/vectors/00001110001-V-0000.bin"
private noncomputable def vp00001110001_1 : Blocks := edgeBlocks% "full/vectors/00001110001-V-0001.bin"
noncomputable def vp00001110001 : Blocks := (Blocks.join vp00001110001_0 vp00001110001_1)
private theorem bp000011100010 : Branch 0 (-451761639/4000000 : ℚ) vp00001110001 := by
  apply branch_left_normalized (c:=vp000011100010) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-451761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-451761639/2000000 : ℚ) by norm_num]
  exact coverp000011100010
private noncomputable def ep000011100011_0 : Blocks := edgeBlocks% "full/vectors/000011100011-E-0000.bin"
private noncomputable def ep000011100011_1 : Blocks := edgeBlocks% "full/vectors/000011100011-E-0001.bin"
noncomputable def ep000011100011 : Blocks := (Blocks.join ep000011100011_0 ep000011100011_1)
private theorem idp000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110001.list =
    C ((2:ℤ)^214) * horner X vp000011100011.list + horner X ep000011100011.list := by
  exact edge_identity (B := (2:ℤ)^401) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011100011 : Branch 1 (-451761639/4000000 : ℚ) vp00001110001 := by
  apply branch_checked idp000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-451761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-453761639/2000000 : ℚ) by norm_num]
  exact coverp000011100011
theorem coverp00001110001 : Covers (-451761639/4000000 : ℚ) vp00001110001 := join_branches bp000011100010 bp000011100011
private noncomputable def vp00001110000111_0 : Blocks := edgeBlocks% "full/vectors/00001110000111-V-0000.bin"
noncomputable def vp00001110000111 : Blocks := vp00001110000111_0
theorem coverp00001110000111 : Covers (-451261639/500000 : ℚ) vp00001110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110000110_0 : Blocks := edgeBlocks% "full/vectors/00001110000110-V-0000.bin"
noncomputable def vp00001110000110 : Blocks := vp00001110000110_0
theorem coverp00001110000110 : Covers (-450761639/500000 : ℚ) vp00001110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000011_0 : Blocks := edgeBlocks% "full/vectors/0000111000011-V-0000.bin"
noncomputable def vp0000111000011 : Blocks := vp0000111000011_0
private theorem bp00001110000110 : Branch 0 (-450761639/1000000 : ℚ) vp0000111000011 := by
  apply branch_left_normalized (c:=vp00001110000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-450761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-450761639/500000 : ℚ) by norm_num]
  exact coverp00001110000110
private noncomputable def ep00001110000111_0 : Blocks := edgeBlocks% "full/vectors/00001110000111-E-0000.bin"
noncomputable def ep00001110000111 : Blocks := ep00001110000111_0
private theorem idp00001110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000011.list =
    C ((2:ℤ)^67) * horner X vp00001110000111.list + horner X ep00001110000111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110000111 : Branch 1 (-450761639/1000000 : ℚ) vp0000111000011 := by
  apply branch_checked idp00001110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-450761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-451261639/500000 : ℚ) by norm_num]
  exact coverp00001110000111
theorem coverp0000111000011 : Covers (-450761639/1000000 : ℚ) vp0000111000011 := join_branches bp00001110000110 bp00001110000111
private noncomputable def vp00001110000101_0 : Blocks := edgeBlocks% "full/vectors/00001110000101-V-0000.bin"
noncomputable def vp00001110000101 : Blocks := vp00001110000101_0
theorem coverp00001110000101 : Covers (-450261639/500000 : ℚ) vp00001110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110000100_0 : Blocks := edgeBlocks% "full/vectors/00001110000100-V-0000.bin"
noncomputable def vp00001110000100 : Blocks := vp00001110000100_0
theorem coverp00001110000100 : Covers (-449761639/500000 : ℚ) vp00001110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000010_0 : Blocks := edgeBlocks% "full/vectors/0000111000010-V-0000.bin"
noncomputable def vp0000111000010 : Blocks := vp0000111000010_0
private theorem bp00001110000100 : Branch 0 (-449761639/1000000 : ℚ) vp0000111000010 := by
  apply branch_left_normalized (c:=vp00001110000100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-449761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-449761639/500000 : ℚ) by norm_num]
  exact coverp00001110000100
private noncomputable def ep00001110000101_0 : Blocks := edgeBlocks% "full/vectors/00001110000101-E-0000.bin"
noncomputable def ep00001110000101 : Blocks := ep00001110000101_0
private theorem idp00001110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000010.list =
    C ((2:ℤ)^68) * horner X vp00001110000101.list + horner X ep00001110000101.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110000101 : Branch 1 (-449761639/1000000 : ℚ) vp0000111000010 := by
  apply branch_checked idp00001110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-449761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-450261639/500000 : ℚ) by norm_num]
  exact coverp00001110000101
theorem coverp0000111000010 : Covers (-449761639/1000000 : ℚ) vp0000111000010 := join_branches bp00001110000100 bp00001110000101
private noncomputable def vp000011100001_0 : Blocks := edgeBlocks% "full/vectors/000011100001-V-0000.bin"
noncomputable def vp000011100001 : Blocks := vp000011100001_0
private theorem bp0000111000010 : Branch 0 (-449761639/2000000 : ℚ) vp000011100001 := by
  apply branch_left_normalized (c:=vp0000111000010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-449761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-449761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000010
private noncomputable def ep0000111000011_0 : Blocks := edgeBlocks% "full/vectors/0000111000011-E-0000.bin"
noncomputable def ep0000111000011 : Blocks := ep0000111000011_0
private theorem idp0000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100001.list =
    C ((2:ℤ)^118) * horner X vp0000111000011.list + horner X ep0000111000011.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111000011 : Branch 1 (-449761639/2000000 : ℚ) vp000011100001 := by
  apply branch_checked idp0000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-449761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-450761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000011
theorem coverp000011100001 : Covers (-449761639/2000000 : ℚ) vp000011100001 := join_branches bp0000111000010 bp0000111000011
private noncomputable def vp00001110000011_0 : Blocks := edgeBlocks% "full/vectors/00001110000011-V-0000.bin"
noncomputable def vp00001110000011 : Blocks := vp00001110000011_0
theorem coverp00001110000011 : Covers (-449261639/500000 : ℚ) vp00001110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110000010_0 : Blocks := edgeBlocks% "full/vectors/00001110000010-V-0000.bin"
noncomputable def vp00001110000010 : Blocks := vp00001110000010_0
theorem coverp00001110000010 : Covers (-448761639/500000 : ℚ) vp00001110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000001_0 : Blocks := edgeBlocks% "full/vectors/0000111000001-V-0000.bin"
noncomputable def vp0000111000001 : Blocks := vp0000111000001_0
private theorem bp00001110000010 : Branch 0 (-448761639/1000000 : ℚ) vp0000111000001 := by
  apply branch_left_normalized (c:=vp00001110000010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-448761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-448761639/500000 : ℚ) by norm_num]
  exact coverp00001110000010
private noncomputable def ep00001110000011_0 : Blocks := edgeBlocks% "full/vectors/00001110000011-E-0000.bin"
noncomputable def ep00001110000011 : Blocks := ep00001110000011_0
private theorem idp00001110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000001.list =
    C ((2:ℤ)^70) * horner X vp00001110000011.list + horner X ep00001110000011.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110000011 : Branch 1 (-448761639/1000000 : ℚ) vp0000111000001 := by
  apply branch_checked idp00001110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-448761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-449261639/500000 : ℚ) by norm_num]
  exact coverp00001110000011
theorem coverp0000111000001 : Covers (-448761639/1000000 : ℚ) vp0000111000001 := join_branches bp00001110000010 bp00001110000011
private noncomputable def vp00001110000001_0 : Blocks := edgeBlocks% "full/vectors/00001110000001-V-0000.bin"
noncomputable def vp00001110000001 : Blocks := vp00001110000001_0
theorem coverp00001110000001 : Covers (-448261639/500000 : ℚ) vp00001110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001110000000_0 : Blocks := edgeBlocks% "full/vectors/00001110000000-V-0000.bin"
noncomputable def vp00001110000000 : Blocks := vp00001110000000_0
theorem coverp00001110000000 : Covers (-447761639/500000 : ℚ) vp00001110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111000000_0 : Blocks := edgeBlocks% "full/vectors/0000111000000-V-0000.bin"
noncomputable def vp0000111000000 : Blocks := vp0000111000000_0
private theorem bp00001110000000 : Branch 0 (-447761639/1000000 : ℚ) vp0000111000000 := by
  apply branch_left_normalized (c:=vp00001110000000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-447761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/500000 : ℚ) by norm_num]
  exact coverp00001110000000
private noncomputable def ep00001110000001_0 : Blocks := edgeBlocks% "full/vectors/00001110000001-E-0000.bin"
noncomputable def ep00001110000001 : Blocks := ep00001110000001_0
private theorem idp00001110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000000.list =
    C ((2:ℤ)^73) * horner X vp00001110000001.list + horner X ep00001110000001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110000001 : Branch 1 (-447761639/1000000 : ℚ) vp0000111000000 := by
  apply branch_checked idp00001110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-448261639/500000 : ℚ) by norm_num]
  exact coverp00001110000001
theorem coverp0000111000000 : Covers (-447761639/1000000 : ℚ) vp0000111000000 := join_branches bp00001110000000 bp00001110000001
private noncomputable def vp000011100000_0 : Blocks := edgeBlocks% "full/vectors/000011100000-V-0000.bin"
noncomputable def vp000011100000 : Blocks := vp000011100000_0
private theorem bp0000111000000 : Branch 0 (-447761639/2000000 : ℚ) vp000011100000 := by
  apply branch_left_normalized (c:=vp0000111000000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-447761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000000
private noncomputable def ep0000111000001_0 : Blocks := edgeBlocks% "full/vectors/0000111000001-E-0000.bin"
noncomputable def ep0000111000001 : Blocks := ep0000111000001_0
private theorem idp0000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100000.list =
    C ((2:ℤ)^124) * horner X vp0000111000001.list + horner X ep0000111000001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111000001 : Branch 1 (-447761639/2000000 : ℚ) vp000011100000 := by
  apply branch_checked idp0000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-448761639/1000000 : ℚ) by norm_num]
  exact coverp0000111000001
theorem coverp000011100000 : Covers (-447761639/2000000 : ℚ) vp000011100000 := join_branches bp0000111000000 bp0000111000001
private noncomputable def vp00001110000_0 : Blocks := edgeBlocks% "full/vectors/00001110000-V-0000.bin"
private noncomputable def vp00001110000_1 : Blocks := edgeBlocks% "full/vectors/00001110000-V-0001.bin"
noncomputable def vp00001110000 : Blocks := (Blocks.join vp00001110000_0 vp00001110000_1)
private theorem bp000011100000 : Branch 0 (-447761639/4000000 : ℚ) vp00001110000 := by
  apply branch_left_normalized (c:=vp000011100000) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-447761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/2000000 : ℚ) by norm_num]
  exact coverp000011100000
private noncomputable def ep000011100001_0 : Blocks := edgeBlocks% "full/vectors/000011100001-E-0000.bin"
private noncomputable def ep000011100001_1 : Blocks := edgeBlocks% "full/vectors/000011100001-E-0001.bin"
noncomputable def ep000011100001 : Blocks := (Blocks.join ep000011100001_0 ep000011100001_1)
private theorem idp000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110000.list =
    C ((2:ℤ)^225) * horner X vp000011100001.list + horner X ep000011100001.list := by
  exact edge_identity (B := (2:ℤ)^409) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011100001 : Branch 1 (-447761639/4000000 : ℚ) vp00001110000 := by
  apply branch_checked idp000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-449761639/2000000 : ℚ) by norm_num]
  exact coverp000011100001
theorem coverp00001110000 : Covers (-447761639/4000000 : ℚ) vp00001110000 := join_branches bp000011100000 bp000011100001
private noncomputable def vp0000111000_0 : Blocks := edgeBlocks% "full/vectors/0000111000-V-0000.bin"
private noncomputable def vp0000111000_1 : Blocks := edgeBlocks% "full/vectors/0000111000-V-0001.bin"
private noncomputable def vp0000111000_2 : Blocks := edgeBlocks% "full/vectors/0000111000-V-0002.bin"
private noncomputable def vp0000111000_3 : Blocks := edgeBlocks% "full/vectors/0000111000-V-0003.bin"
noncomputable def vp0000111000 : Blocks := (Blocks.join (Blocks.join vp0000111000_0 vp0000111000_1) (Blocks.join vp0000111000_2 vp0000111000_3))
private theorem bp00001110000 : Branch 0 (-447761639/8000000 : ℚ) vp0000111000 := by
  apply branch_left_normalized (c:=vp00001110000) (k:=0) (m:=208) (by decide +kernel)
  rw [show 2*(-447761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/4000000 : ℚ) by norm_num]
  exact coverp00001110000
private noncomputable def ep00001110001_0 : Blocks := edgeBlocks% "full/vectors/00001110001-E-0000.bin"
private noncomputable def ep00001110001_1 : Blocks := edgeBlocks% "full/vectors/00001110001-E-0001.bin"
private noncomputable def ep00001110001_2 : Blocks := edgeBlocks% "full/vectors/00001110001-E-0002.bin"
private noncomputable def ep00001110001_3 : Blocks := edgeBlocks% "full/vectors/00001110001-E-0003.bin"
noncomputable def ep00001110001 : Blocks := (Blocks.join (Blocks.join ep00001110001_0 ep00001110001_1) (Blocks.join ep00001110001_2 ep00001110001_3))
private theorem idp00001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111000.list =
    C ((2:ℤ)^420) * horner X vp00001110001.list + horner X ep00001110001.list := by
  exact edge_identity (B := (2:ℤ)^691) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001110001 : Branch 1 (-447761639/8000000 : ℚ) vp0000111000 := by
  apply branch_checked idp00001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-451761639/4000000 : ℚ) by norm_num]
  exact coverp00001110001
theorem coverp0000111000 : Covers (-447761639/8000000 : ℚ) vp0000111000 := join_branches bp00001110000 bp00001110001
private noncomputable def vp000011100_0 : Blocks := edgeBlocks% "full/vectors/000011100-V-0000.bin"
private noncomputable def vp000011100_1 : Blocks := edgeBlocks% "full/vectors/000011100-V-0001.bin"
private noncomputable def vp000011100_2 : Blocks := edgeBlocks% "full/vectors/000011100-V-0002.bin"
private noncomputable def vp000011100_3 : Blocks := edgeBlocks% "full/vectors/000011100-V-0003.bin"
private noncomputable def vp000011100_4 : Blocks := edgeBlocks% "full/vectors/000011100-V-0004.bin"
private noncomputable def vp000011100_5 : Blocks := edgeBlocks% "full/vectors/000011100-V-0005.bin"
noncomputable def vp000011100 : Blocks := (Blocks.join (Blocks.join vp000011100_0 (Blocks.join vp000011100_1 vp000011100_2)) (Blocks.join vp000011100_3 (Blocks.join vp000011100_4 vp000011100_5)))
private theorem bp0000111000 : Branch 0 (-447761639/16000000 : ℚ) vp000011100 := by
  apply branch_left_normalized (c:=vp0000111000) (k:=0) (m:=392) (by decide +kernel)
  rw [show 2*(-447761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/8000000 : ℚ) by norm_num]
  exact coverp0000111000
private noncomputable def ep0000111001_0 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0000.bin"
private noncomputable def ep0000111001_1 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0001.bin"
private noncomputable def ep0000111001_2 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0002.bin"
private noncomputable def ep0000111001_3 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0003.bin"
private noncomputable def ep0000111001_4 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0004.bin"
private noncomputable def ep0000111001_5 : Blocks := edgeBlocks% "full/vectors/0000111001-E-0005.bin"
noncomputable def ep0000111001 : Blocks := (Blocks.join (Blocks.join ep0000111001_0 (Blocks.join ep0000111001_1 ep0000111001_2)) (Blocks.join ep0000111001_3 (Blocks.join ep0000111001_4 ep0000111001_5)))
private theorem idp0000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011100.list =
    C ((2:ℤ)^806) * horner X vp0000111001.list + horner X ep0000111001.list := by
  exact edge_identity (B := (2:ℤ)^1253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111001 : Branch 1 (-447761639/16000000 : ℚ) vp000011100 := by
  apply branch_checked idp0000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-455761639/8000000 : ℚ) by norm_num]
  exact coverp0000111001
theorem coverp000011100 : Covers (-447761639/16000000 : ℚ) vp000011100 := join_branches bp0000111000 bp0000111001
private noncomputable def vp00001110_0 : Blocks := edgeBlocks% "full/vectors/00001110-V-0000.bin"
private noncomputable def vp00001110_1 : Blocks := edgeBlocks% "full/vectors/00001110-V-0001.bin"
private noncomputable def vp00001110_2 : Blocks := edgeBlocks% "full/vectors/00001110-V-0002.bin"
private noncomputable def vp00001110_3 : Blocks := edgeBlocks% "full/vectors/00001110-V-0003.bin"
private noncomputable def vp00001110_4 : Blocks := edgeBlocks% "full/vectors/00001110-V-0004.bin"
private noncomputable def vp00001110_5 : Blocks := edgeBlocks% "full/vectors/00001110-V-0005.bin"
private noncomputable def vp00001110_6 : Blocks := edgeBlocks% "full/vectors/00001110-V-0006.bin"
private noncomputable def vp00001110_7 : Blocks := edgeBlocks% "full/vectors/00001110-V-0007.bin"
private noncomputable def vp00001110_8 : Blocks := edgeBlocks% "full/vectors/00001110-V-0008.bin"
private noncomputable def vp00001110_9 : Blocks := edgeBlocks% "full/vectors/00001110-V-0009.bin"
private noncomputable def vp00001110_10 : Blocks := edgeBlocks% "full/vectors/00001110-V-0010.bin"
private noncomputable def vp00001110_11 : Blocks := edgeBlocks% "full/vectors/00001110-V-0011.bin"
noncomputable def vp00001110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001110_0 (Blocks.join vp00001110_1 vp00001110_2)) (Blocks.join vp00001110_3 (Blocks.join vp00001110_4 vp00001110_5))) (Blocks.join (Blocks.join vp00001110_6 (Blocks.join vp00001110_7 vp00001110_8)) (Blocks.join vp00001110_9 (Blocks.join vp00001110_10 vp00001110_11))))
private theorem bp000011100 : Branch 0 (-447761639/32000000 : ℚ) vp00001110 := by
  apply branch_left_normalized (c:=vp000011100) (k:=0) (m:=758) (by decide +kernel)
  rw [show 2*(-447761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/16000000 : ℚ) by norm_num]
  exact coverp000011100
private noncomputable def ep000011101_0 : Blocks := edgeBlocks% "full/vectors/000011101-E-0000.bin"
private noncomputable def ep000011101_1 : Blocks := edgeBlocks% "full/vectors/000011101-E-0001.bin"
private noncomputable def ep000011101_2 : Blocks := edgeBlocks% "full/vectors/000011101-E-0002.bin"
private noncomputable def ep000011101_3 : Blocks := edgeBlocks% "full/vectors/000011101-E-0003.bin"
private noncomputable def ep000011101_4 : Blocks := edgeBlocks% "full/vectors/000011101-E-0004.bin"
private noncomputable def ep000011101_5 : Blocks := edgeBlocks% "full/vectors/000011101-E-0005.bin"
private noncomputable def ep000011101_6 : Blocks := edgeBlocks% "full/vectors/000011101-E-0006.bin"
private noncomputable def ep000011101_7 : Blocks := edgeBlocks% "full/vectors/000011101-E-0007.bin"
private noncomputable def ep000011101_8 : Blocks := edgeBlocks% "full/vectors/000011101-E-0008.bin"
private noncomputable def ep000011101_9 : Blocks := edgeBlocks% "full/vectors/000011101-E-0009.bin"
private noncomputable def ep000011101_10 : Blocks := edgeBlocks% "full/vectors/000011101-E-0010.bin"
private noncomputable def ep000011101_11 : Blocks := edgeBlocks% "full/vectors/000011101-E-0011.bin"
noncomputable def ep000011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000011101_0 (Blocks.join ep000011101_1 ep000011101_2)) (Blocks.join ep000011101_3 (Blocks.join ep000011101_4 ep000011101_5))) (Blocks.join (Blocks.join ep000011101_6 (Blocks.join ep000011101_7 ep000011101_8)) (Blocks.join ep000011101_9 (Blocks.join ep000011101_10 ep000011101_11))))
private theorem idp000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001110.list =
    C ((2:ℤ)^1569) * horner X vp000011101.list + horner X ep000011101.list := by
  exact edge_identity (B := (2:ℤ)^2361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011101 : Branch 1 (-447761639/32000000 : ℚ) vp00001110 := by
  apply branch_checked idp000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-463761639/16000000 : ℚ) by norm_num]
  exact coverp000011101
theorem coverp00001110 : Covers (-447761639/32000000 : ℚ) vp00001110 := join_branches bp000011100 bp000011101
private noncomputable def vp0000111_0 : Blocks := edgeBlocks% "full/vectors/0000111-V-0000.bin"
private noncomputable def vp0000111_1 : Blocks := edgeBlocks% "full/vectors/0000111-V-0001.bin"
private noncomputable def vp0000111_2 : Blocks := edgeBlocks% "full/vectors/0000111-V-0002.bin"
private noncomputable def vp0000111_3 : Blocks := edgeBlocks% "full/vectors/0000111-V-0003.bin"
private noncomputable def vp0000111_4 : Blocks := edgeBlocks% "full/vectors/0000111-V-0004.bin"
private noncomputable def vp0000111_5 : Blocks := edgeBlocks% "full/vectors/0000111-V-0005.bin"
private noncomputable def vp0000111_6 : Blocks := edgeBlocks% "full/vectors/0000111-V-0006.bin"
private noncomputable def vp0000111_7 : Blocks := edgeBlocks% "full/vectors/0000111-V-0007.bin"
private noncomputable def vp0000111_8 : Blocks := edgeBlocks% "full/vectors/0000111-V-0008.bin"
private noncomputable def vp0000111_9 : Blocks := edgeBlocks% "full/vectors/0000111-V-0009.bin"
private noncomputable def vp0000111_10 : Blocks := edgeBlocks% "full/vectors/0000111-V-0010.bin"
private noncomputable def vp0000111_11 : Blocks := edgeBlocks% "full/vectors/0000111-V-0011.bin"
private noncomputable def vp0000111_12 : Blocks := edgeBlocks% "full/vectors/0000111-V-0012.bin"
private noncomputable def vp0000111_13 : Blocks := edgeBlocks% "full/vectors/0000111-V-0013.bin"
private noncomputable def vp0000111_14 : Blocks := edgeBlocks% "full/vectors/0000111-V-0014.bin"
private noncomputable def vp0000111_15 : Blocks := edgeBlocks% "full/vectors/0000111-V-0015.bin"
private noncomputable def vp0000111_16 : Blocks := edgeBlocks% "full/vectors/0000111-V-0016.bin"
private noncomputable def vp0000111_17 : Blocks := edgeBlocks% "full/vectors/0000111-V-0017.bin"
private noncomputable def vp0000111_18 : Blocks := edgeBlocks% "full/vectors/0000111-V-0018.bin"
private noncomputable def vp0000111_19 : Blocks := edgeBlocks% "full/vectors/0000111-V-0019.bin"
private noncomputable def vp0000111_20 : Blocks := edgeBlocks% "full/vectors/0000111-V-0020.bin"
private noncomputable def vp0000111_21 : Blocks := edgeBlocks% "full/vectors/0000111-V-0021.bin"
private noncomputable def vp0000111_22 : Blocks := edgeBlocks% "full/vectors/0000111-V-0022.bin"
noncomputable def vp0000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000111_0 vp0000111_1) (Blocks.join vp0000111_2 (Blocks.join vp0000111_3 vp0000111_4))) (Blocks.join (Blocks.join vp0000111_5 (Blocks.join vp0000111_6 vp0000111_7)) (Blocks.join vp0000111_8 (Blocks.join vp0000111_9 vp0000111_10)))) (Blocks.join (Blocks.join (Blocks.join vp0000111_11 (Blocks.join vp0000111_12 vp0000111_13)) (Blocks.join vp0000111_14 (Blocks.join vp0000111_15 vp0000111_16))) (Blocks.join (Blocks.join vp0000111_17 (Blocks.join vp0000111_18 vp0000111_19)) (Blocks.join vp0000111_20 (Blocks.join vp0000111_21 vp0000111_22)))))
private theorem bp00001110 : Branch 0 (-447761639/64000000 : ℚ) vp0000111 := by
  apply branch_left_normalized (c:=vp00001110) (k:=0) (m:=1476) (by decide +kernel)
  rw [show 2*(-447761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-447761639/32000000 : ℚ) by norm_num]
  exact coverp00001110
private noncomputable def ep00001111_0 : Blocks := edgeBlocks% "full/vectors/00001111-E-0000.bin"
private noncomputable def ep00001111_1 : Blocks := edgeBlocks% "full/vectors/00001111-E-0001.bin"
private noncomputable def ep00001111_2 : Blocks := edgeBlocks% "full/vectors/00001111-E-0002.bin"
private noncomputable def ep00001111_3 : Blocks := edgeBlocks% "full/vectors/00001111-E-0003.bin"
private noncomputable def ep00001111_4 : Blocks := edgeBlocks% "full/vectors/00001111-E-0004.bin"
private noncomputable def ep00001111_5 : Blocks := edgeBlocks% "full/vectors/00001111-E-0005.bin"
private noncomputable def ep00001111_6 : Blocks := edgeBlocks% "full/vectors/00001111-E-0006.bin"
private noncomputable def ep00001111_7 : Blocks := edgeBlocks% "full/vectors/00001111-E-0007.bin"
private noncomputable def ep00001111_8 : Blocks := edgeBlocks% "full/vectors/00001111-E-0008.bin"
private noncomputable def ep00001111_9 : Blocks := edgeBlocks% "full/vectors/00001111-E-0009.bin"
private noncomputable def ep00001111_10 : Blocks := edgeBlocks% "full/vectors/00001111-E-0010.bin"
private noncomputable def ep00001111_11 : Blocks := edgeBlocks% "full/vectors/00001111-E-0011.bin"
private noncomputable def ep00001111_12 : Blocks := edgeBlocks% "full/vectors/00001111-E-0012.bin"
private noncomputable def ep00001111_13 : Blocks := edgeBlocks% "full/vectors/00001111-E-0013.bin"
private noncomputable def ep00001111_14 : Blocks := edgeBlocks% "full/vectors/00001111-E-0014.bin"
private noncomputable def ep00001111_15 : Blocks := edgeBlocks% "full/vectors/00001111-E-0015.bin"
private noncomputable def ep00001111_16 : Blocks := edgeBlocks% "full/vectors/00001111-E-0016.bin"
private noncomputable def ep00001111_17 : Blocks := edgeBlocks% "full/vectors/00001111-E-0017.bin"
private noncomputable def ep00001111_18 : Blocks := edgeBlocks% "full/vectors/00001111-E-0018.bin"
private noncomputable def ep00001111_19 : Blocks := edgeBlocks% "full/vectors/00001111-E-0019.bin"
private noncomputable def ep00001111_20 : Blocks := edgeBlocks% "full/vectors/00001111-E-0020.bin"
private noncomputable def ep00001111_21 : Blocks := edgeBlocks% "full/vectors/00001111-E-0021.bin"
private noncomputable def ep00001111_22 : Blocks := edgeBlocks% "full/vectors/00001111-E-0022.bin"
noncomputable def ep00001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00001111_0 ep00001111_1) (Blocks.join ep00001111_2 (Blocks.join ep00001111_3 ep00001111_4))) (Blocks.join (Blocks.join ep00001111_5 (Blocks.join ep00001111_6 ep00001111_7)) (Blocks.join ep00001111_8 (Blocks.join ep00001111_9 ep00001111_10)))) (Blocks.join (Blocks.join (Blocks.join ep00001111_11 (Blocks.join ep00001111_12 ep00001111_13)) (Blocks.join ep00001111_14 (Blocks.join ep00001111_15 ep00001111_16))) (Blocks.join (Blocks.join ep00001111_17 (Blocks.join ep00001111_18 ep00001111_19)) (Blocks.join ep00001111_20 (Blocks.join ep00001111_21 ep00001111_22)))))
private def ptsp00001111 : List ℤ := [((2:ℤ)^4189+0),((2:ℤ)^4189+1)]
private theorem boundp00001111 : 2^vp0000111.size*absSum vp0000111.list + ((2:ℤ)^3049*absSum vp00001111.list+absSum ep00001111.list) < (2:ℤ)^4519 := by decide +kernel
private theorem pointp00001111_0 : fastHom 1 ((2:ℤ)^4189+0) vp0000111 = ((2:ℤ)^3049)*vp00001111.subst ((2:ℤ)^4189+0)+ep00001111.subst ((2:ℤ)^4189+0) := by decide +kernel
private theorem pointp00001111_1 : fastHom 1 ((2:ℤ)^4189+1) vp0000111 = ((2:ℤ)^3049)*vp00001111.subst ((2:ℤ)^4189+1)+ep00001111.subst ((2:ℤ)^4189+1) := by decide +kernel
private theorem checkp00001111 (x:ℤ) (hx:x ∈ ptsp00001111) : fastHom 1 x vp0000111 = ((2:ℤ)^3049)*vp00001111.subst x+ep00001111.subst x := by
  simp only [ptsp00001111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp00001111_0
  · exact pointp00001111_1
private theorem idp00001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111.list =
    C ((2:ℤ)^3049) * horner X vp00001111.list + horner X ep00001111.list := by
  apply edge_identity (B := (2:ℤ)^4519) (by decide) (by positivity) (by positivity) boundp00001111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00001111 (by decide +kernel)
  · have h : ptsp00001111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00001111.trans_le (by decide +kernel)
  · exact checkp00001111
private theorem bp00001111 : Branch 1 (-447761639/64000000 : ℚ) vp0000111 := by
  apply branch_checked idp00001111 (by positivity) (by decide +kernel)
  rw [show 2*(-447761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-479761639/32000000 : ℚ) by norm_num]
  exact coverp00001111
theorem coverp0000111 : Covers (-447761639/64000000 : ℚ) vp0000111 := join_branches bp00001110 bp00001111
end NextProof.EdgeFull

