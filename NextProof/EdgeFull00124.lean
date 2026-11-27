import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00123

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp011010111111_0 : Blocks := edgeBlocks% "full/vectors/011010111111-V-0000.bin"
noncomputable def vp011010111111 : Blocks := vp011010111111_0
theorem coverp011010111111 : Covers (-3453761639/2000000 : ℚ) vp011010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp011010111110_0 : Blocks := edgeBlocks% "full/vectors/011010111110-V-0000.bin"
noncomputable def vp011010111110 : Blocks := vp011010111110_0
theorem coverp011010111110 : Covers (-3451761639/2000000 : ℚ) vp011010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011111_0 : Blocks := edgeBlocks% "full/vectors/01101011111-V-0000.bin"
noncomputable def vp01101011111 : Blocks := vp01101011111_0
private theorem bp011010111110 : Branch 0 (-3451761639/4000000 : ℚ) vp01101011111 := by
  apply branch_left_normalized (c:=vp011010111110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3451761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3451761639/2000000 : ℚ) by norm_num]
  exact coverp011010111110
private noncomputable def ep011010111111_0 : Blocks := edgeBlocks% "full/vectors/011010111111-E-0000.bin"
noncomputable def ep011010111111 : Blocks := ep011010111111_0
private theorem idp011010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011111.list =
    C ((2:ℤ)^100) * horner X vp011010111111.list + horner X ep011010111111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010111111 : Branch 1 (-3451761639/4000000 : ℚ) vp01101011111 := by
  apply branch_checked idp011010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3451761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3453761639/2000000 : ℚ) by norm_num]
  exact coverp011010111111
theorem coverp01101011111 : Covers (-3451761639/4000000 : ℚ) vp01101011111 := join_branches bp011010111110 bp011010111111
private noncomputable def vp011010111101_0 : Blocks := edgeBlocks% "full/vectors/011010111101-V-0000.bin"
noncomputable def vp011010111101 : Blocks := vp011010111101_0
theorem coverp011010111101 : Covers (-3449761639/2000000 : ℚ) vp011010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp011010111100_0 : Blocks := edgeBlocks% "full/vectors/011010111100-V-0000.bin"
noncomputable def vp011010111100 : Blocks := vp011010111100_0
theorem coverp011010111100 : Covers (-3447761639/2000000 : ℚ) vp011010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011110_0 : Blocks := edgeBlocks% "full/vectors/01101011110-V-0000.bin"
noncomputable def vp01101011110 : Blocks := vp01101011110_0
private theorem bp011010111100 : Branch 0 (-3447761639/4000000 : ℚ) vp01101011110 := by
  apply branch_left_normalized (c:=vp011010111100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3447761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3447761639/2000000 : ℚ) by norm_num]
  exact coverp011010111100
private noncomputable def ep011010111101_0 : Blocks := edgeBlocks% "full/vectors/011010111101-E-0000.bin"
noncomputable def ep011010111101 : Blocks := ep011010111101_0
private theorem idp011010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011110.list =
    C ((2:ℤ)^101) * horner X vp011010111101.list + horner X ep011010111101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010111101 : Branch 1 (-3447761639/4000000 : ℚ) vp01101011110 := by
  apply branch_checked idp011010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3447761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3449761639/2000000 : ℚ) by norm_num]
  exact coverp011010111101
theorem coverp01101011110 : Covers (-3447761639/4000000 : ℚ) vp01101011110 := join_branches bp011010111100 bp011010111101
private noncomputable def vp0110101111_0 : Blocks := edgeBlocks% "full/vectors/0110101111-V-0000.bin"
private noncomputable def vp0110101111_1 : Blocks := edgeBlocks% "full/vectors/0110101111-V-0001.bin"
noncomputable def vp0110101111 : Blocks := (Blocks.join vp0110101111_0 vp0110101111_1)
private theorem bp01101011110 : Branch 0 (-3447761639/8000000 : ℚ) vp0110101111 := by
  apply branch_left_normalized (c:=vp01101011110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3447761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3447761639/4000000 : ℚ) by norm_num]
  exact coverp01101011110
private noncomputable def ep01101011111_0 : Blocks := edgeBlocks% "full/vectors/01101011111-E-0000.bin"
private noncomputable def ep01101011111_1 : Blocks := edgeBlocks% "full/vectors/01101011111-E-0001.bin"
noncomputable def ep01101011111 : Blocks := (Blocks.join ep01101011111_0 ep01101011111_1)
private theorem idp01101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101111.list =
    C ((2:ℤ)^181) * horner X vp01101011111.list + horner X ep01101011111.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101011111 : Branch 1 (-3447761639/8000000 : ℚ) vp0110101111 := by
  apply branch_checked idp01101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3447761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3451761639/4000000 : ℚ) by norm_num]
  exact coverp01101011111
theorem coverp0110101111 : Covers (-3447761639/8000000 : ℚ) vp0110101111 := join_branches bp01101011110 bp01101011111
private noncomputable def vp011010111011_0 : Blocks := edgeBlocks% "full/vectors/011010111011-V-0000.bin"
noncomputable def vp011010111011 : Blocks := vp011010111011_0
theorem coverp011010111011 : Covers (-3445761639/2000000 : ℚ) vp011010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp011010111010_0 : Blocks := edgeBlocks% "full/vectors/011010111010-V-0000.bin"
noncomputable def vp011010111010 : Blocks := vp011010111010_0
theorem coverp011010111010 : Covers (-3443761639/2000000 : ℚ) vp011010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011101_0 : Blocks := edgeBlocks% "full/vectors/01101011101-V-0000.bin"
noncomputable def vp01101011101 : Blocks := vp01101011101_0
private theorem bp011010111010 : Branch 0 (-3443761639/4000000 : ℚ) vp01101011101 := by
  apply branch_left_normalized (c:=vp011010111010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3443761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3443761639/2000000 : ℚ) by norm_num]
  exact coverp011010111010
private noncomputable def ep011010111011_0 : Blocks := edgeBlocks% "full/vectors/011010111011-E-0000.bin"
noncomputable def ep011010111011 : Blocks := ep011010111011_0
private theorem idp011010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011101.list =
    C ((2:ℤ)^101) * horner X vp011010111011.list + horner X ep011010111011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010111011 : Branch 1 (-3443761639/4000000 : ℚ) vp01101011101 := by
  apply branch_checked idp011010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3443761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3445761639/2000000 : ℚ) by norm_num]
  exact coverp011010111011
theorem coverp01101011101 : Covers (-3443761639/4000000 : ℚ) vp01101011101 := join_branches bp011010111010 bp011010111011
private noncomputable def vp011010111001_0 : Blocks := edgeBlocks% "full/vectors/011010111001-V-0000.bin"
noncomputable def vp011010111001 : Blocks := vp011010111001_0
theorem coverp011010111001 : Covers (-3441761639/2000000 : ℚ) vp011010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp011010111000_0 : Blocks := edgeBlocks% "full/vectors/011010111000-V-0000.bin"
noncomputable def vp011010111000 : Blocks := vp011010111000_0
theorem coverp011010111000 : Covers (-3439761639/2000000 : ℚ) vp011010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011100_0 : Blocks := edgeBlocks% "full/vectors/01101011100-V-0000.bin"
noncomputable def vp01101011100 : Blocks := vp01101011100_0
private theorem bp011010111000 : Branch 0 (-3439761639/4000000 : ℚ) vp01101011100 := by
  apply branch_left_normalized (c:=vp011010111000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3439761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3439761639/2000000 : ℚ) by norm_num]
  exact coverp011010111000
private noncomputable def ep011010111001_0 : Blocks := edgeBlocks% "full/vectors/011010111001-E-0000.bin"
noncomputable def ep011010111001 : Blocks := ep011010111001_0
private theorem idp011010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011100.list =
    C ((2:ℤ)^101) * horner X vp011010111001.list + horner X ep011010111001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010111001 : Branch 1 (-3439761639/4000000 : ℚ) vp01101011100 := by
  apply branch_checked idp011010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3439761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3441761639/2000000 : ℚ) by norm_num]
  exact coverp011010111001
theorem coverp01101011100 : Covers (-3439761639/4000000 : ℚ) vp01101011100 := join_branches bp011010111000 bp011010111001
private noncomputable def vp0110101110_0 : Blocks := edgeBlocks% "full/vectors/0110101110-V-0000.bin"
private noncomputable def vp0110101110_1 : Blocks := edgeBlocks% "full/vectors/0110101110-V-0001.bin"
noncomputable def vp0110101110 : Blocks := (Blocks.join vp0110101110_0 vp0110101110_1)
private theorem bp01101011100 : Branch 0 (-3439761639/8000000 : ℚ) vp0110101110 := by
  apply branch_left_normalized (c:=vp01101011100) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3439761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3439761639/4000000 : ℚ) by norm_num]
  exact coverp01101011100
private noncomputable def ep01101011101_0 : Blocks := edgeBlocks% "full/vectors/01101011101-E-0000.bin"
private noncomputable def ep01101011101_1 : Blocks := edgeBlocks% "full/vectors/01101011101-E-0001.bin"
noncomputable def ep01101011101 : Blocks := (Blocks.join ep01101011101_0 ep01101011101_1)
private theorem idp01101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101110.list =
    C ((2:ℤ)^180) * horner X vp01101011101.list + horner X ep01101011101.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101011101 : Branch 1 (-3439761639/8000000 : ℚ) vp0110101110 := by
  apply branch_checked idp01101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3439761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3443761639/4000000 : ℚ) by norm_num]
  exact coverp01101011101
theorem coverp0110101110 : Covers (-3439761639/8000000 : ℚ) vp0110101110 := join_branches bp01101011100 bp01101011101
private noncomputable def vp011010111_0 : Blocks := edgeBlocks% "full/vectors/011010111-V-0000.bin"
private noncomputable def vp011010111_1 : Blocks := edgeBlocks% "full/vectors/011010111-V-0001.bin"
private noncomputable def vp011010111_2 : Blocks := edgeBlocks% "full/vectors/011010111-V-0002.bin"
noncomputable def vp011010111 : Blocks := (Blocks.join vp011010111_0 (Blocks.join vp011010111_1 vp011010111_2))
private theorem bp0110101110 : Branch 0 (-3439761639/16000000 : ℚ) vp011010111 := by
  apply branch_left_normalized (c:=vp0110101110) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3439761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3439761639/8000000 : ℚ) by norm_num]
  exact coverp0110101110
private noncomputable def ep0110101111_0 : Blocks := edgeBlocks% "full/vectors/0110101111-E-0000.bin"
private noncomputable def ep0110101111_1 : Blocks := edgeBlocks% "full/vectors/0110101111-E-0001.bin"
private noncomputable def ep0110101111_2 : Blocks := edgeBlocks% "full/vectors/0110101111-E-0002.bin"
noncomputable def ep0110101111 : Blocks := (Blocks.join ep0110101111_0 (Blocks.join ep0110101111_1 ep0110101111_2))
private theorem idp0110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010111.list =
    C ((2:ℤ)^337) * horner X vp0110101111.list + horner X ep0110101111.list := by
  exact edge_identity (B := (2:ℤ)^535) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110101111 : Branch 1 (-3439761639/16000000 : ℚ) vp011010111 := by
  apply branch_checked idp0110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3439761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3447761639/8000000 : ℚ) by norm_num]
  exact coverp0110101111
theorem coverp011010111 : Covers (-3439761639/16000000 : ℚ) vp011010111 := join_branches bp0110101110 bp0110101111
private noncomputable def vp011010110111_0 : Blocks := edgeBlocks% "full/vectors/011010110111-V-0000.bin"
noncomputable def vp011010110111 : Blocks := vp011010110111_0
theorem coverp011010110111 : Covers (-3437761639/2000000 : ℚ) vp011010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp011010110110_0 : Blocks := edgeBlocks% "full/vectors/011010110110-V-0000.bin"
noncomputable def vp011010110110 : Blocks := vp011010110110_0
theorem coverp011010110110 : Covers (-3435761639/2000000 : ℚ) vp011010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011011_0 : Blocks := edgeBlocks% "full/vectors/01101011011-V-0000.bin"
noncomputable def vp01101011011 : Blocks := vp01101011011_0
private theorem bp011010110110 : Branch 0 (-3435761639/4000000 : ℚ) vp01101011011 := by
  apply branch_left_normalized (c:=vp011010110110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3435761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3435761639/2000000 : ℚ) by norm_num]
  exact coverp011010110110
private noncomputable def ep011010110111_0 : Blocks := edgeBlocks% "full/vectors/011010110111-E-0000.bin"
noncomputable def ep011010110111 : Blocks := ep011010110111_0
private theorem idp011010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011011.list =
    C ((2:ℤ)^101) * horner X vp011010110111.list + horner X ep011010110111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010110111 : Branch 1 (-3435761639/4000000 : ℚ) vp01101011011 := by
  apply branch_checked idp011010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3435761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3437761639/2000000 : ℚ) by norm_num]
  exact coverp011010110111
theorem coverp01101011011 : Covers (-3435761639/4000000 : ℚ) vp01101011011 := join_branches bp011010110110 bp011010110111
private noncomputable def vp011010110101_0 : Blocks := edgeBlocks% "full/vectors/011010110101-V-0000.bin"
noncomputable def vp011010110101 : Blocks := vp011010110101_0
theorem coverp011010110101 : Covers (-3433761639/2000000 : ℚ) vp011010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp011010110100_0 : Blocks := edgeBlocks% "full/vectors/011010110100-V-0000.bin"
noncomputable def vp011010110100 : Blocks := vp011010110100_0
theorem coverp011010110100 : Covers (-3431761639/2000000 : ℚ) vp011010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011010_0 : Blocks := edgeBlocks% "full/vectors/01101011010-V-0000.bin"
noncomputable def vp01101011010 : Blocks := vp01101011010_0
private theorem bp011010110100 : Branch 0 (-3431761639/4000000 : ℚ) vp01101011010 := by
  apply branch_left_normalized (c:=vp011010110100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3431761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3431761639/2000000 : ℚ) by norm_num]
  exact coverp011010110100
private noncomputable def ep011010110101_0 : Blocks := edgeBlocks% "full/vectors/011010110101-E-0000.bin"
noncomputable def ep011010110101 : Blocks := ep011010110101_0
private theorem idp011010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011010.list =
    C ((2:ℤ)^101) * horner X vp011010110101.list + horner X ep011010110101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010110101 : Branch 1 (-3431761639/4000000 : ℚ) vp01101011010 := by
  apply branch_checked idp011010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3431761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3433761639/2000000 : ℚ) by norm_num]
  exact coverp011010110101
theorem coverp01101011010 : Covers (-3431761639/4000000 : ℚ) vp01101011010 := join_branches bp011010110100 bp011010110101
private noncomputable def vp0110101101_0 : Blocks := edgeBlocks% "full/vectors/0110101101-V-0000.bin"
private noncomputable def vp0110101101_1 : Blocks := edgeBlocks% "full/vectors/0110101101-V-0001.bin"
noncomputable def vp0110101101 : Blocks := (Blocks.join vp0110101101_0 vp0110101101_1)
private theorem bp01101011010 : Branch 0 (-3431761639/8000000 : ℚ) vp0110101101 := by
  apply branch_left_normalized (c:=vp01101011010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3431761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3431761639/4000000 : ℚ) by norm_num]
  exact coverp01101011010
private noncomputable def ep01101011011_0 : Blocks := edgeBlocks% "full/vectors/01101011011-E-0000.bin"
private noncomputable def ep01101011011_1 : Blocks := edgeBlocks% "full/vectors/01101011011-E-0001.bin"
noncomputable def ep01101011011 : Blocks := (Blocks.join ep01101011011_0 ep01101011011_1)
private theorem idp01101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101101.list =
    C ((2:ℤ)^180) * horner X vp01101011011.list + horner X ep01101011011.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101011011 : Branch 1 (-3431761639/8000000 : ℚ) vp0110101101 := by
  apply branch_checked idp01101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3431761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3435761639/4000000 : ℚ) by norm_num]
  exact coverp01101011011
theorem coverp0110101101 : Covers (-3431761639/8000000 : ℚ) vp0110101101 := join_branches bp01101011010 bp01101011011
private noncomputable def vp011010110011_0 : Blocks := edgeBlocks% "full/vectors/011010110011-V-0000.bin"
noncomputable def vp011010110011 : Blocks := vp011010110011_0
theorem coverp011010110011 : Covers (-3429761639/2000000 : ℚ) vp011010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp011010110010_0 : Blocks := edgeBlocks% "full/vectors/011010110010-V-0000.bin"
noncomputable def vp011010110010 : Blocks := vp011010110010_0
theorem coverp011010110010 : Covers (-3427761639/2000000 : ℚ) vp011010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011001_0 : Blocks := edgeBlocks% "full/vectors/01101011001-V-0000.bin"
noncomputable def vp01101011001 : Blocks := vp01101011001_0
private theorem bp011010110010 : Branch 0 (-3427761639/4000000 : ℚ) vp01101011001 := by
  apply branch_left_normalized (c:=vp011010110010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3427761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3427761639/2000000 : ℚ) by norm_num]
  exact coverp011010110010
private noncomputable def ep011010110011_0 : Blocks := edgeBlocks% "full/vectors/011010110011-E-0000.bin"
noncomputable def ep011010110011 : Blocks := ep011010110011_0
private theorem idp011010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011001.list =
    C ((2:ℤ)^101) * horner X vp011010110011.list + horner X ep011010110011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010110011 : Branch 1 (-3427761639/4000000 : ℚ) vp01101011001 := by
  apply branch_checked idp011010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3427761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3429761639/2000000 : ℚ) by norm_num]
  exact coverp011010110011
theorem coverp01101011001 : Covers (-3427761639/4000000 : ℚ) vp01101011001 := join_branches bp011010110010 bp011010110011
private noncomputable def vp011010110001_0 : Blocks := edgeBlocks% "full/vectors/011010110001-V-0000.bin"
noncomputable def vp011010110001 : Blocks := vp011010110001_0
theorem coverp011010110001 : Covers (-3425761639/2000000 : ℚ) vp011010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp011010110000_0 : Blocks := edgeBlocks% "full/vectors/011010110000-V-0000.bin"
noncomputable def vp011010110000 : Blocks := vp011010110000_0
theorem coverp011010110000 : Covers (-3423761639/2000000 : ℚ) vp011010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101011000_0 : Blocks := edgeBlocks% "full/vectors/01101011000-V-0000.bin"
noncomputable def vp01101011000 : Blocks := vp01101011000_0
private theorem bp011010110000 : Branch 0 (-3423761639/4000000 : ℚ) vp01101011000 := by
  apply branch_left_normalized (c:=vp011010110000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3423761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3423761639/2000000 : ℚ) by norm_num]
  exact coverp011010110000
private noncomputable def ep011010110001_0 : Blocks := edgeBlocks% "full/vectors/011010110001-E-0000.bin"
noncomputable def ep011010110001 : Blocks := ep011010110001_0
private theorem idp011010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011000.list =
    C ((2:ℤ)^101) * horner X vp011010110001.list + horner X ep011010110001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010110001 : Branch 1 (-3423761639/4000000 : ℚ) vp01101011000 := by
  apply branch_checked idp011010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3423761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3425761639/2000000 : ℚ) by norm_num]
  exact coverp011010110001
theorem coverp01101011000 : Covers (-3423761639/4000000 : ℚ) vp01101011000 := join_branches bp011010110000 bp011010110001
private noncomputable def vp0110101100_0 : Blocks := edgeBlocks% "full/vectors/0110101100-V-0000.bin"
private noncomputable def vp0110101100_1 : Blocks := edgeBlocks% "full/vectors/0110101100-V-0001.bin"
noncomputable def vp0110101100 : Blocks := (Blocks.join vp0110101100_0 vp0110101100_1)
private theorem bp01101011000 : Branch 0 (-3423761639/8000000 : ℚ) vp0110101100 := by
  apply branch_left_normalized (c:=vp01101011000) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3423761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3423761639/4000000 : ℚ) by norm_num]
  exact coverp01101011000
private noncomputable def ep01101011001_0 : Blocks := edgeBlocks% "full/vectors/01101011001-E-0000.bin"
private noncomputable def ep01101011001_1 : Blocks := edgeBlocks% "full/vectors/01101011001-E-0001.bin"
noncomputable def ep01101011001 : Blocks := (Blocks.join ep01101011001_0 ep01101011001_1)
private theorem idp01101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101100.list =
    C ((2:ℤ)^180) * horner X vp01101011001.list + horner X ep01101011001.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101011001 : Branch 1 (-3423761639/8000000 : ℚ) vp0110101100 := by
  apply branch_checked idp01101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3423761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3427761639/4000000 : ℚ) by norm_num]
  exact coverp01101011001
theorem coverp0110101100 : Covers (-3423761639/8000000 : ℚ) vp0110101100 := join_branches bp01101011000 bp01101011001
private noncomputable def vp011010110_0 : Blocks := edgeBlocks% "full/vectors/011010110-V-0000.bin"
private noncomputable def vp011010110_1 : Blocks := edgeBlocks% "full/vectors/011010110-V-0001.bin"
private noncomputable def vp011010110_2 : Blocks := edgeBlocks% "full/vectors/011010110-V-0002.bin"
noncomputable def vp011010110 : Blocks := (Blocks.join vp011010110_0 (Blocks.join vp011010110_1 vp011010110_2))
private theorem bp0110101100 : Branch 0 (-3423761639/16000000 : ℚ) vp011010110 := by
  apply branch_left_normalized (c:=vp0110101100) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3423761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3423761639/8000000 : ℚ) by norm_num]
  exact coverp0110101100
private noncomputable def ep0110101101_0 : Blocks := edgeBlocks% "full/vectors/0110101101-E-0000.bin"
private noncomputable def ep0110101101_1 : Blocks := edgeBlocks% "full/vectors/0110101101-E-0001.bin"
private noncomputable def ep0110101101_2 : Blocks := edgeBlocks% "full/vectors/0110101101-E-0002.bin"
noncomputable def ep0110101101 : Blocks := (Blocks.join ep0110101101_0 (Blocks.join ep0110101101_1 ep0110101101_2))
private theorem idp0110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010110.list =
    C ((2:ℤ)^337) * horner X vp0110101101.list + horner X ep0110101101.list := by
  exact edge_identity (B := (2:ℤ)^535) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110101101 : Branch 1 (-3423761639/16000000 : ℚ) vp011010110 := by
  apply branch_checked idp0110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3423761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3431761639/8000000 : ℚ) by norm_num]
  exact coverp0110101101
theorem coverp011010110 : Covers (-3423761639/16000000 : ℚ) vp011010110 := join_branches bp0110101100 bp0110101101
private noncomputable def vp01101011_0 : Blocks := edgeBlocks% "full/vectors/01101011-V-0000.bin"
private noncomputable def vp01101011_1 : Blocks := edgeBlocks% "full/vectors/01101011-V-0001.bin"
private noncomputable def vp01101011_2 : Blocks := edgeBlocks% "full/vectors/01101011-V-0002.bin"
private noncomputable def vp01101011_3 : Blocks := edgeBlocks% "full/vectors/01101011-V-0003.bin"
private noncomputable def vp01101011_4 : Blocks := edgeBlocks% "full/vectors/01101011-V-0004.bin"
noncomputable def vp01101011 : Blocks := (Blocks.join (Blocks.join vp01101011_0 vp01101011_1) (Blocks.join vp01101011_2 (Blocks.join vp01101011_3 vp01101011_4)))
private theorem bp011010110 : Branch 0 (-3423761639/32000000 : ℚ) vp01101011 := by
  apply branch_left_normalized (c:=vp011010110) (k:=0) (m:=290) (by decide +kernel)
  rw [show 2*(-3423761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3423761639/16000000 : ℚ) by norm_num]
  exact coverp011010110
private noncomputable def ep011010111_0 : Blocks := edgeBlocks% "full/vectors/011010111-E-0000.bin"
private noncomputable def ep011010111_1 : Blocks := edgeBlocks% "full/vectors/011010111-E-0001.bin"
private noncomputable def ep011010111_2 : Blocks := edgeBlocks% "full/vectors/011010111-E-0002.bin"
private noncomputable def ep011010111_3 : Blocks := edgeBlocks% "full/vectors/011010111-E-0003.bin"
private noncomputable def ep011010111_4 : Blocks := edgeBlocks% "full/vectors/011010111-E-0004.bin"
noncomputable def ep011010111 : Blocks := (Blocks.join (Blocks.join ep011010111_0 ep011010111_1) (Blocks.join ep011010111_2 (Blocks.join ep011010111_3 ep011010111_4)))
private theorem idp011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101011.list =
    C ((2:ℤ)^649) * horner X vp011010111.list + horner X ep011010111.list := by
  exact edge_identity (B := (2:ℤ)^943) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010111 : Branch 1 (-3423761639/32000000 : ℚ) vp01101011 := by
  apply branch_checked idp011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3423761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3439761639/16000000 : ℚ) by norm_num]
  exact coverp011010111
theorem coverp01101011 : Covers (-3423761639/32000000 : ℚ) vp01101011 := join_branches bp011010110 bp011010111
private noncomputable def vp011010101111_0 : Blocks := edgeBlocks% "full/vectors/011010101111-V-0000.bin"
noncomputable def vp011010101111 : Blocks := vp011010101111_0
theorem coverp011010101111 : Covers (-3421761639/2000000 : ℚ) vp011010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp011010101110_0 : Blocks := edgeBlocks% "full/vectors/011010101110-V-0000.bin"
noncomputable def vp011010101110 : Blocks := vp011010101110_0
theorem coverp011010101110 : Covers (-3419761639/2000000 : ℚ) vp011010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010111_0 : Blocks := edgeBlocks% "full/vectors/01101010111-V-0000.bin"
noncomputable def vp01101010111 : Blocks := vp01101010111_0
private theorem bp011010101110 : Branch 0 (-3419761639/4000000 : ℚ) vp01101010111 := by
  apply branch_left_normalized (c:=vp011010101110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3419761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3419761639/2000000 : ℚ) by norm_num]
  exact coverp011010101110
private noncomputable def ep011010101111_0 : Blocks := edgeBlocks% "full/vectors/011010101111-E-0000.bin"
noncomputable def ep011010101111 : Blocks := ep011010101111_0
private theorem idp011010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010111.list =
    C ((2:ℤ)^100) * horner X vp011010101111.list + horner X ep011010101111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010101111 : Branch 1 (-3419761639/4000000 : ℚ) vp01101010111 := by
  apply branch_checked idp011010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3419761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3421761639/2000000 : ℚ) by norm_num]
  exact coverp011010101111
theorem coverp01101010111 : Covers (-3419761639/4000000 : ℚ) vp01101010111 := join_branches bp011010101110 bp011010101111
private noncomputable def vp011010101101_0 : Blocks := edgeBlocks% "full/vectors/011010101101-V-0000.bin"
noncomputable def vp011010101101 : Blocks := vp011010101101_0
theorem coverp011010101101 : Covers (-3417761639/2000000 : ℚ) vp011010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp011010101100_0 : Blocks := edgeBlocks% "full/vectors/011010101100-V-0000.bin"
noncomputable def vp011010101100 : Blocks := vp011010101100_0
theorem coverp011010101100 : Covers (-3415761639/2000000 : ℚ) vp011010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010110_0 : Blocks := edgeBlocks% "full/vectors/01101010110-V-0000.bin"
noncomputable def vp01101010110 : Blocks := vp01101010110_0
private theorem bp011010101100 : Branch 0 (-3415761639/4000000 : ℚ) vp01101010110 := by
  apply branch_left_normalized (c:=vp011010101100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3415761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3415761639/2000000 : ℚ) by norm_num]
  exact coverp011010101100
private noncomputable def ep011010101101_0 : Blocks := edgeBlocks% "full/vectors/011010101101-E-0000.bin"
noncomputable def ep011010101101 : Blocks := ep011010101101_0
private theorem idp011010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010110.list =
    C ((2:ℤ)^100) * horner X vp011010101101.list + horner X ep011010101101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010101101 : Branch 1 (-3415761639/4000000 : ℚ) vp01101010110 := by
  apply branch_checked idp011010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3415761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3417761639/2000000 : ℚ) by norm_num]
  exact coverp011010101101
theorem coverp01101010110 : Covers (-3415761639/4000000 : ℚ) vp01101010110 := join_branches bp011010101100 bp011010101101
private noncomputable def vp0110101011_0 : Blocks := edgeBlocks% "full/vectors/0110101011-V-0000.bin"
private noncomputable def vp0110101011_1 : Blocks := edgeBlocks% "full/vectors/0110101011-V-0001.bin"
noncomputable def vp0110101011 : Blocks := (Blocks.join vp0110101011_0 vp0110101011_1)
private theorem bp01101010110 : Branch 0 (-3415761639/8000000 : ℚ) vp0110101011 := by
  apply branch_left_normalized (c:=vp01101010110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3415761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3415761639/4000000 : ℚ) by norm_num]
  exact coverp01101010110
private noncomputable def ep01101010111_0 : Blocks := edgeBlocks% "full/vectors/01101010111-E-0000.bin"
private noncomputable def ep01101010111_1 : Blocks := edgeBlocks% "full/vectors/01101010111-E-0001.bin"
noncomputable def ep01101010111 : Blocks := (Blocks.join ep01101010111_0 ep01101010111_1)
private theorem idp01101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101011.list =
    C ((2:ℤ)^180) * horner X vp01101010111.list + horner X ep01101010111.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101010111 : Branch 1 (-3415761639/8000000 : ℚ) vp0110101011 := by
  apply branch_checked idp01101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3415761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3419761639/4000000 : ℚ) by norm_num]
  exact coverp01101010111
theorem coverp0110101011 : Covers (-3415761639/8000000 : ℚ) vp0110101011 := join_branches bp01101010110 bp01101010111
private noncomputable def vp011010101011_0 : Blocks := edgeBlocks% "full/vectors/011010101011-V-0000.bin"
noncomputable def vp011010101011 : Blocks := vp011010101011_0
theorem coverp011010101011 : Covers (-3413761639/2000000 : ℚ) vp011010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp011010101010_0 : Blocks := edgeBlocks% "full/vectors/011010101010-V-0000.bin"
noncomputable def vp011010101010 : Blocks := vp011010101010_0
theorem coverp011010101010 : Covers (-3411761639/2000000 : ℚ) vp011010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010101_0 : Blocks := edgeBlocks% "full/vectors/01101010101-V-0000.bin"
noncomputable def vp01101010101 : Blocks := vp01101010101_0
private theorem bp011010101010 : Branch 0 (-3411761639/4000000 : ℚ) vp01101010101 := by
  apply branch_left_normalized (c:=vp011010101010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3411761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3411761639/2000000 : ℚ) by norm_num]
  exact coverp011010101010
private noncomputable def ep011010101011_0 : Blocks := edgeBlocks% "full/vectors/011010101011-E-0000.bin"
noncomputable def ep011010101011 : Blocks := ep011010101011_0
private theorem idp011010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010101.list =
    C ((2:ℤ)^100) * horner X vp011010101011.list + horner X ep011010101011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010101011 : Branch 1 (-3411761639/4000000 : ℚ) vp01101010101 := by
  apply branch_checked idp011010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3411761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3413761639/2000000 : ℚ) by norm_num]
  exact coverp011010101011
theorem coverp01101010101 : Covers (-3411761639/4000000 : ℚ) vp01101010101 := join_branches bp011010101010 bp011010101011
private noncomputable def vp011010101001_0 : Blocks := edgeBlocks% "full/vectors/011010101001-V-0000.bin"
noncomputable def vp011010101001 : Blocks := vp011010101001_0
theorem coverp011010101001 : Covers (-3409761639/2000000 : ℚ) vp011010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp011010101000_0 : Blocks := edgeBlocks% "full/vectors/011010101000-V-0000.bin"
noncomputable def vp011010101000 : Blocks := vp011010101000_0
theorem coverp011010101000 : Covers (-3407761639/2000000 : ℚ) vp011010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010100_0 : Blocks := edgeBlocks% "full/vectors/01101010100-V-0000.bin"
noncomputable def vp01101010100 : Blocks := vp01101010100_0
private theorem bp011010101000 : Branch 0 (-3407761639/4000000 : ℚ) vp01101010100 := by
  apply branch_left_normalized (c:=vp011010101000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3407761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3407761639/2000000 : ℚ) by norm_num]
  exact coverp011010101000
private noncomputable def ep011010101001_0 : Blocks := edgeBlocks% "full/vectors/011010101001-E-0000.bin"
noncomputable def ep011010101001 : Blocks := ep011010101001_0
private theorem idp011010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010100.list =
    C ((2:ℤ)^100) * horner X vp011010101001.list + horner X ep011010101001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010101001 : Branch 1 (-3407761639/4000000 : ℚ) vp01101010100 := by
  apply branch_checked idp011010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3407761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3409761639/2000000 : ℚ) by norm_num]
  exact coverp011010101001
theorem coverp01101010100 : Covers (-3407761639/4000000 : ℚ) vp01101010100 := join_branches bp011010101000 bp011010101001
private noncomputable def vp0110101010_0 : Blocks := edgeBlocks% "full/vectors/0110101010-V-0000.bin"
private noncomputable def vp0110101010_1 : Blocks := edgeBlocks% "full/vectors/0110101010-V-0001.bin"
noncomputable def vp0110101010 : Blocks := (Blocks.join vp0110101010_0 vp0110101010_1)
private theorem bp01101010100 : Branch 0 (-3407761639/8000000 : ℚ) vp0110101010 := by
  apply branch_left_normalized (c:=vp01101010100) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3407761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3407761639/4000000 : ℚ) by norm_num]
  exact coverp01101010100
private noncomputable def ep01101010101_0 : Blocks := edgeBlocks% "full/vectors/01101010101-E-0000.bin"
private noncomputable def ep01101010101_1 : Blocks := edgeBlocks% "full/vectors/01101010101-E-0001.bin"
noncomputable def ep01101010101 : Blocks := (Blocks.join ep01101010101_0 ep01101010101_1)
private theorem idp01101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101010.list =
    C ((2:ℤ)^180) * horner X vp01101010101.list + horner X ep01101010101.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101010101 : Branch 1 (-3407761639/8000000 : ℚ) vp0110101010 := by
  apply branch_checked idp01101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3407761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3411761639/4000000 : ℚ) by norm_num]
  exact coverp01101010101
theorem coverp0110101010 : Covers (-3407761639/8000000 : ℚ) vp0110101010 := join_branches bp01101010100 bp01101010101
private noncomputable def vp011010101_0 : Blocks := edgeBlocks% "full/vectors/011010101-V-0000.bin"
private noncomputable def vp011010101_1 : Blocks := edgeBlocks% "full/vectors/011010101-V-0001.bin"
private noncomputable def vp011010101_2 : Blocks := edgeBlocks% "full/vectors/011010101-V-0002.bin"
noncomputable def vp011010101 : Blocks := (Blocks.join vp011010101_0 (Blocks.join vp011010101_1 vp011010101_2))
private theorem bp0110101010 : Branch 0 (-3407761639/16000000 : ℚ) vp011010101 := by
  apply branch_left_normalized (c:=vp0110101010) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3407761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3407761639/8000000 : ℚ) by norm_num]
  exact coverp0110101010
private noncomputable def ep0110101011_0 : Blocks := edgeBlocks% "full/vectors/0110101011-E-0000.bin"
private noncomputable def ep0110101011_1 : Blocks := edgeBlocks% "full/vectors/0110101011-E-0001.bin"
private noncomputable def ep0110101011_2 : Blocks := edgeBlocks% "full/vectors/0110101011-E-0002.bin"
noncomputable def ep0110101011 : Blocks := (Blocks.join ep0110101011_0 (Blocks.join ep0110101011_1 ep0110101011_2))
private theorem idp0110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010101.list =
    C ((2:ℤ)^338) * horner X vp0110101011.list + horner X ep0110101011.list := by
  exact edge_identity (B := (2:ℤ)^536) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110101011 : Branch 1 (-3407761639/16000000 : ℚ) vp011010101 := by
  apply branch_checked idp0110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3407761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3415761639/8000000 : ℚ) by norm_num]
  exact coverp0110101011
theorem coverp011010101 : Covers (-3407761639/16000000 : ℚ) vp011010101 := join_branches bp0110101010 bp0110101011
private noncomputable def vp011010100111_0 : Blocks := edgeBlocks% "full/vectors/011010100111-V-0000.bin"
noncomputable def vp011010100111 : Blocks := vp011010100111_0
theorem coverp011010100111 : Covers (-3405761639/2000000 : ℚ) vp011010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp011010100110_0 : Blocks := edgeBlocks% "full/vectors/011010100110-V-0000.bin"
noncomputable def vp011010100110 : Blocks := vp011010100110_0
theorem coverp011010100110 : Covers (-3403761639/2000000 : ℚ) vp011010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010011_0 : Blocks := edgeBlocks% "full/vectors/01101010011-V-0000.bin"
noncomputable def vp01101010011 : Blocks := vp01101010011_0
private theorem bp011010100110 : Branch 0 (-3403761639/4000000 : ℚ) vp01101010011 := by
  apply branch_left_normalized (c:=vp011010100110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3403761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3403761639/2000000 : ℚ) by norm_num]
  exact coverp011010100110
private noncomputable def ep011010100111_0 : Blocks := edgeBlocks% "full/vectors/011010100111-E-0000.bin"
noncomputable def ep011010100111 : Blocks := ep011010100111_0
private theorem idp011010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010011.list =
    C ((2:ℤ)^100) * horner X vp011010100111.list + horner X ep011010100111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010100111 : Branch 1 (-3403761639/4000000 : ℚ) vp01101010011 := by
  apply branch_checked idp011010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3403761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3405761639/2000000 : ℚ) by norm_num]
  exact coverp011010100111
theorem coverp01101010011 : Covers (-3403761639/4000000 : ℚ) vp01101010011 := join_branches bp011010100110 bp011010100111
private noncomputable def vp011010100101_0 : Blocks := edgeBlocks% "full/vectors/011010100101-V-0000.bin"
noncomputable def vp011010100101 : Blocks := vp011010100101_0
theorem coverp011010100101 : Covers (-3401761639/2000000 : ℚ) vp011010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp011010100100_0 : Blocks := edgeBlocks% "full/vectors/011010100100-V-0000.bin"
noncomputable def vp011010100100 : Blocks := vp011010100100_0
theorem coverp011010100100 : Covers (-3399761639/2000000 : ℚ) vp011010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010010_0 : Blocks := edgeBlocks% "full/vectors/01101010010-V-0000.bin"
noncomputable def vp01101010010 : Blocks := vp01101010010_0
private theorem bp011010100100 : Branch 0 (-3399761639/4000000 : ℚ) vp01101010010 := by
  apply branch_left_normalized (c:=vp011010100100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3399761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3399761639/2000000 : ℚ) by norm_num]
  exact coverp011010100100
private noncomputable def ep011010100101_0 : Blocks := edgeBlocks% "full/vectors/011010100101-E-0000.bin"
noncomputable def ep011010100101 : Blocks := ep011010100101_0
private theorem idp011010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010010.list =
    C ((2:ℤ)^100) * horner X vp011010100101.list + horner X ep011010100101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010100101 : Branch 1 (-3399761639/4000000 : ℚ) vp01101010010 := by
  apply branch_checked idp011010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3399761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3401761639/2000000 : ℚ) by norm_num]
  exact coverp011010100101
theorem coverp01101010010 : Covers (-3399761639/4000000 : ℚ) vp01101010010 := join_branches bp011010100100 bp011010100101
private noncomputable def vp0110101001_0 : Blocks := edgeBlocks% "full/vectors/0110101001-V-0000.bin"
private noncomputable def vp0110101001_1 : Blocks := edgeBlocks% "full/vectors/0110101001-V-0001.bin"
noncomputable def vp0110101001 : Blocks := (Blocks.join vp0110101001_0 vp0110101001_1)
private theorem bp01101010010 : Branch 0 (-3399761639/8000000 : ℚ) vp0110101001 := by
  apply branch_left_normalized (c:=vp01101010010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3399761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3399761639/4000000 : ℚ) by norm_num]
  exact coverp01101010010
private noncomputable def ep01101010011_0 : Blocks := edgeBlocks% "full/vectors/01101010011-E-0000.bin"
private noncomputable def ep01101010011_1 : Blocks := edgeBlocks% "full/vectors/01101010011-E-0001.bin"
noncomputable def ep01101010011 : Blocks := (Blocks.join ep01101010011_0 ep01101010011_1)
private theorem idp01101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101001.list =
    C ((2:ℤ)^180) * horner X vp01101010011.list + horner X ep01101010011.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101010011 : Branch 1 (-3399761639/8000000 : ℚ) vp0110101001 := by
  apply branch_checked idp01101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3399761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3403761639/4000000 : ℚ) by norm_num]
  exact coverp01101010011
theorem coverp0110101001 : Covers (-3399761639/8000000 : ℚ) vp0110101001 := join_branches bp01101010010 bp01101010011
private noncomputable def vp011010100011_0 : Blocks := edgeBlocks% "full/vectors/011010100011-V-0000.bin"
noncomputable def vp011010100011 : Blocks := vp011010100011_0
theorem coverp011010100011 : Covers (-3397761639/2000000 : ℚ) vp011010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp011010100010_0 : Blocks := edgeBlocks% "full/vectors/011010100010-V-0000.bin"
noncomputable def vp011010100010 : Blocks := vp011010100010_0
theorem coverp011010100010 : Covers (-3395761639/2000000 : ℚ) vp011010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010001_0 : Blocks := edgeBlocks% "full/vectors/01101010001-V-0000.bin"
noncomputable def vp01101010001 : Blocks := vp01101010001_0
private theorem bp011010100010 : Branch 0 (-3395761639/4000000 : ℚ) vp01101010001 := by
  apply branch_left_normalized (c:=vp011010100010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3395761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3395761639/2000000 : ℚ) by norm_num]
  exact coverp011010100010
private noncomputable def ep011010100011_0 : Blocks := edgeBlocks% "full/vectors/011010100011-E-0000.bin"
noncomputable def ep011010100011 : Blocks := ep011010100011_0
private theorem idp011010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010001.list =
    C ((2:ℤ)^101) * horner X vp011010100011.list + horner X ep011010100011.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010100011 : Branch 1 (-3395761639/4000000 : ℚ) vp01101010001 := by
  apply branch_checked idp011010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3395761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3397761639/2000000 : ℚ) by norm_num]
  exact coverp011010100011
theorem coverp01101010001 : Covers (-3395761639/4000000 : ℚ) vp01101010001 := join_branches bp011010100010 bp011010100011
private noncomputable def vp011010100001_0 : Blocks := edgeBlocks% "full/vectors/011010100001-V-0000.bin"
noncomputable def vp011010100001 : Blocks := vp011010100001_0
theorem coverp011010100001 : Covers (-3393761639/2000000 : ℚ) vp011010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp011010100000_0 : Blocks := edgeBlocks% "full/vectors/011010100000-V-0000.bin"
noncomputable def vp011010100000 : Blocks := vp011010100000_0
theorem coverp011010100000 : Covers (-3391761639/2000000 : ℚ) vp011010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101010000_0 : Blocks := edgeBlocks% "full/vectors/01101010000-V-0000.bin"
noncomputable def vp01101010000 : Blocks := vp01101010000_0
private theorem bp011010100000 : Branch 0 (-3391761639/4000000 : ℚ) vp01101010000 := by
  apply branch_left_normalized (c:=vp011010100000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3391761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3391761639/2000000 : ℚ) by norm_num]
  exact coverp011010100000
private noncomputable def ep011010100001_0 : Blocks := edgeBlocks% "full/vectors/011010100001-E-0000.bin"
noncomputable def ep011010100001 : Blocks := ep011010100001_0
private theorem idp011010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010000.list =
    C ((2:ℤ)^101) * horner X vp011010100001.list + horner X ep011010100001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010100001 : Branch 1 (-3391761639/4000000 : ℚ) vp01101010000 := by
  apply branch_checked idp011010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3391761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3393761639/2000000 : ℚ) by norm_num]
  exact coverp011010100001
theorem coverp01101010000 : Covers (-3391761639/4000000 : ℚ) vp01101010000 := join_branches bp011010100000 bp011010100001
private noncomputable def vp0110101000_0 : Blocks := edgeBlocks% "full/vectors/0110101000-V-0000.bin"
private noncomputable def vp0110101000_1 : Blocks := edgeBlocks% "full/vectors/0110101000-V-0001.bin"
noncomputable def vp0110101000 : Blocks := (Blocks.join vp0110101000_0 vp0110101000_1)
private theorem bp01101010000 : Branch 0 (-3391761639/8000000 : ℚ) vp0110101000 := by
  apply branch_left_normalized (c:=vp01101010000) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3391761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3391761639/4000000 : ℚ) by norm_num]
  exact coverp01101010000
private noncomputable def ep01101010001_0 : Blocks := edgeBlocks% "full/vectors/01101010001-E-0000.bin"
private noncomputable def ep01101010001_1 : Blocks := edgeBlocks% "full/vectors/01101010001-E-0001.bin"
noncomputable def ep01101010001 : Blocks := (Blocks.join ep01101010001_0 ep01101010001_1)
private theorem idp01101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101000.list =
    C ((2:ℤ)^180) * horner X vp01101010001.list + horner X ep01101010001.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101010001 : Branch 1 (-3391761639/8000000 : ℚ) vp0110101000 := by
  apply branch_checked idp01101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3391761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3395761639/4000000 : ℚ) by norm_num]
  exact coverp01101010001
theorem coverp0110101000 : Covers (-3391761639/8000000 : ℚ) vp0110101000 := join_branches bp01101010000 bp01101010001
private noncomputable def vp011010100_0 : Blocks := edgeBlocks% "full/vectors/011010100-V-0000.bin"
private noncomputable def vp011010100_1 : Blocks := edgeBlocks% "full/vectors/011010100-V-0001.bin"
private noncomputable def vp011010100_2 : Blocks := edgeBlocks% "full/vectors/011010100-V-0002.bin"
noncomputable def vp011010100 : Blocks := (Blocks.join vp011010100_0 (Blocks.join vp011010100_1 vp011010100_2))
private theorem bp0110101000 : Branch 0 (-3391761639/16000000 : ℚ) vp011010100 := by
  apply branch_left_normalized (c:=vp0110101000) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3391761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3391761639/8000000 : ℚ) by norm_num]
  exact coverp0110101000
private noncomputable def ep0110101001_0 : Blocks := edgeBlocks% "full/vectors/0110101001-E-0000.bin"
private noncomputable def ep0110101001_1 : Blocks := edgeBlocks% "full/vectors/0110101001-E-0001.bin"
private noncomputable def ep0110101001_2 : Blocks := edgeBlocks% "full/vectors/0110101001-E-0002.bin"
noncomputable def ep0110101001 : Blocks := (Blocks.join ep0110101001_0 (Blocks.join ep0110101001_1 ep0110101001_2))
private theorem idp0110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010100.list =
    C ((2:ℤ)^340) * horner X vp0110101001.list + horner X ep0110101001.list := by
  exact edge_identity (B := (2:ℤ)^538) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110101001 : Branch 1 (-3391761639/16000000 : ℚ) vp011010100 := by
  apply branch_checked idp0110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3391761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3399761639/8000000 : ℚ) by norm_num]
  exact coverp0110101001
theorem coverp011010100 : Covers (-3391761639/16000000 : ℚ) vp011010100 := join_branches bp0110101000 bp0110101001
private noncomputable def vp01101010_0 : Blocks := edgeBlocks% "full/vectors/01101010-V-0000.bin"
private noncomputable def vp01101010_1 : Blocks := edgeBlocks% "full/vectors/01101010-V-0001.bin"
private noncomputable def vp01101010_2 : Blocks := edgeBlocks% "full/vectors/01101010-V-0002.bin"
private noncomputable def vp01101010_3 : Blocks := edgeBlocks% "full/vectors/01101010-V-0003.bin"
private noncomputable def vp01101010_4 : Blocks := edgeBlocks% "full/vectors/01101010-V-0004.bin"
noncomputable def vp01101010 : Blocks := (Blocks.join (Blocks.join vp01101010_0 vp01101010_1) (Blocks.join vp01101010_2 (Blocks.join vp01101010_3 vp01101010_4)))
private theorem bp011010100 : Branch 0 (-3391761639/32000000 : ℚ) vp01101010 := by
  apply branch_left_normalized (c:=vp011010100) (k:=0) (m:=292) (by decide +kernel)
  rw [show 2*(-3391761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3391761639/16000000 : ℚ) by norm_num]
  exact coverp011010100
private noncomputable def ep011010101_0 : Blocks := edgeBlocks% "full/vectors/011010101-E-0000.bin"
private noncomputable def ep011010101_1 : Blocks := edgeBlocks% "full/vectors/011010101-E-0001.bin"
private noncomputable def ep011010101_2 : Blocks := edgeBlocks% "full/vectors/011010101-E-0002.bin"
private noncomputable def ep011010101_3 : Blocks := edgeBlocks% "full/vectors/011010101-E-0003.bin"
private noncomputable def ep011010101_4 : Blocks := edgeBlocks% "full/vectors/011010101-E-0004.bin"
noncomputable def ep011010101 : Blocks := (Blocks.join (Blocks.join ep011010101_0 ep011010101_1) (Blocks.join ep011010101_2 (Blocks.join ep011010101_3 ep011010101_4)))
private theorem idp011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101010.list =
    C ((2:ℤ)^653) * horner X vp011010101.list + horner X ep011010101.list := by
  exact edge_identity (B := (2:ℤ)^948) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010101 : Branch 1 (-3391761639/32000000 : ℚ) vp01101010 := by
  apply branch_checked idp011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3391761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3407761639/16000000 : ℚ) by norm_num]
  exact coverp011010101
theorem coverp01101010 : Covers (-3391761639/32000000 : ℚ) vp01101010 := join_branches bp011010100 bp011010101
private noncomputable def vp0110101_0 : Blocks := edgeBlocks% "full/vectors/0110101-V-0000.bin"
private noncomputable def vp0110101_1 : Blocks := edgeBlocks% "full/vectors/0110101-V-0001.bin"
private noncomputable def vp0110101_2 : Blocks := edgeBlocks% "full/vectors/0110101-V-0002.bin"
private noncomputable def vp0110101_3 : Blocks := edgeBlocks% "full/vectors/0110101-V-0003.bin"
private noncomputable def vp0110101_4 : Blocks := edgeBlocks% "full/vectors/0110101-V-0004.bin"
private noncomputable def vp0110101_5 : Blocks := edgeBlocks% "full/vectors/0110101-V-0005.bin"
private noncomputable def vp0110101_6 : Blocks := edgeBlocks% "full/vectors/0110101-V-0006.bin"
private noncomputable def vp0110101_7 : Blocks := edgeBlocks% "full/vectors/0110101-V-0007.bin"
private noncomputable def vp0110101_8 : Blocks := edgeBlocks% "full/vectors/0110101-V-0008.bin"
noncomputable def vp0110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110101_0 vp0110101_1) (Blocks.join vp0110101_2 vp0110101_3)) (Blocks.join (Blocks.join vp0110101_4 vp0110101_5) (Blocks.join vp0110101_6 (Blocks.join vp0110101_7 vp0110101_8))))
private theorem bp01101010 : Branch 0 (-3391761639/64000000 : ℚ) vp0110101 := by
  apply branch_left_normalized (c:=vp01101010) (k:=0) (m:=559) (by decide +kernel)
  rw [show 2*(-3391761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3391761639/32000000 : ℚ) by norm_num]
  exact coverp01101010
private noncomputable def ep01101011_0 : Blocks := edgeBlocks% "full/vectors/01101011-E-0000.bin"
private noncomputable def ep01101011_1 : Blocks := edgeBlocks% "full/vectors/01101011-E-0001.bin"
private noncomputable def ep01101011_2 : Blocks := edgeBlocks% "full/vectors/01101011-E-0002.bin"
private noncomputable def ep01101011_3 : Blocks := edgeBlocks% "full/vectors/01101011-E-0003.bin"
private noncomputable def ep01101011_4 : Blocks := edgeBlocks% "full/vectors/01101011-E-0004.bin"
private noncomputable def ep01101011_5 : Blocks := edgeBlocks% "full/vectors/01101011-E-0005.bin"
private noncomputable def ep01101011_6 : Blocks := edgeBlocks% "full/vectors/01101011-E-0006.bin"
private noncomputable def ep01101011_7 : Blocks := edgeBlocks% "full/vectors/01101011-E-0007.bin"
private noncomputable def ep01101011_8 : Blocks := edgeBlocks% "full/vectors/01101011-E-0008.bin"
noncomputable def ep01101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01101011_0 ep01101011_1) (Blocks.join ep01101011_2 ep01101011_3)) (Blocks.join (Blocks.join ep01101011_4 ep01101011_5) (Blocks.join ep01101011_6 (Blocks.join ep01101011_7 ep01101011_8))))
private theorem idp01101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110101.list =
    C ((2:ℤ)^1272) * horner X vp01101011.list + horner X ep01101011.list := by
  exact edge_identity (B := (2:ℤ)^1759) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101011 : Branch 1 (-3391761639/64000000 : ℚ) vp0110101 := by
  apply branch_checked idp01101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3391761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3423761639/32000000 : ℚ) by norm_num]
  exact coverp01101011
theorem coverp0110101 : Covers (-3391761639/64000000 : ℚ) vp0110101 := join_branches bp01101010 bp01101011
private noncomputable def vp011010011111_0 : Blocks := edgeBlocks% "full/vectors/011010011111-V-0000.bin"
noncomputable def vp011010011111 : Blocks := vp011010011111_0
theorem coverp011010011111 : Covers (-3389761639/2000000 : ℚ) vp011010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp011010011110_0 : Blocks := edgeBlocks% "full/vectors/011010011110-V-0000.bin"
noncomputable def vp011010011110 : Blocks := vp011010011110_0
theorem coverp011010011110 : Covers (-3387761639/2000000 : ℚ) vp011010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101001111_0 : Blocks := edgeBlocks% "full/vectors/01101001111-V-0000.bin"
noncomputable def vp01101001111 : Blocks := vp01101001111_0
private theorem bp011010011110 : Branch 0 (-3387761639/4000000 : ℚ) vp01101001111 := by
  apply branch_left_normalized (c:=vp011010011110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3387761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3387761639/2000000 : ℚ) by norm_num]
  exact coverp011010011110
private noncomputable def ep011010011111_0 : Blocks := edgeBlocks% "full/vectors/011010011111-E-0000.bin"
noncomputable def ep011010011111 : Blocks := ep011010011111_0
private theorem idp011010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101001111.list =
    C ((2:ℤ)^100) * horner X vp011010011111.list + horner X ep011010011111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010011111 : Branch 1 (-3387761639/4000000 : ℚ) vp01101001111 := by
  apply branch_checked idp011010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3387761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3389761639/2000000 : ℚ) by norm_num]
  exact coverp011010011111
theorem coverp01101001111 : Covers (-3387761639/4000000 : ℚ) vp01101001111 := join_branches bp011010011110 bp011010011111
private noncomputable def vp011010011101_0 : Blocks := edgeBlocks% "full/vectors/011010011101-V-0000.bin"
noncomputable def vp011010011101 : Blocks := vp011010011101_0
theorem coverp011010011101 : Covers (-3385761639/2000000 : ℚ) vp011010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp011010011100_0 : Blocks := edgeBlocks% "full/vectors/011010011100-V-0000.bin"
noncomputable def vp011010011100 : Blocks := vp011010011100_0
theorem coverp011010011100 : Covers (-3383761639/2000000 : ℚ) vp011010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101001110_0 : Blocks := edgeBlocks% "full/vectors/01101001110-V-0000.bin"
noncomputable def vp01101001110 : Blocks := vp01101001110_0
private theorem bp011010011100 : Branch 0 (-3383761639/4000000 : ℚ) vp01101001110 := by
  apply branch_left_normalized (c:=vp011010011100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3383761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3383761639/2000000 : ℚ) by norm_num]
  exact coverp011010011100
private noncomputable def ep011010011101_0 : Blocks := edgeBlocks% "full/vectors/011010011101-E-0000.bin"
noncomputable def ep011010011101 : Blocks := ep011010011101_0
private theorem idp011010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101001110.list =
    C ((2:ℤ)^98) * horner X vp011010011101.list + horner X ep011010011101.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010011101 : Branch 1 (-3383761639/4000000 : ℚ) vp01101001110 := by
  apply branch_checked idp011010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3383761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3385761639/2000000 : ℚ) by norm_num]
  exact coverp011010011101
theorem coverp01101001110 : Covers (-3383761639/4000000 : ℚ) vp01101001110 := join_branches bp011010011100 bp011010011101
private noncomputable def vp0110100111_0 : Blocks := edgeBlocks% "full/vectors/0110100111-V-0000.bin"
private noncomputable def vp0110100111_1 : Blocks := edgeBlocks% "full/vectors/0110100111-V-0001.bin"
noncomputable def vp0110100111 : Blocks := (Blocks.join vp0110100111_0 vp0110100111_1)
private theorem bp01101001110 : Branch 0 (-3383761639/8000000 : ℚ) vp0110100111 := by
  apply branch_left_normalized (c:=vp01101001110) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3383761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3383761639/4000000 : ℚ) by norm_num]
  exact coverp01101001110
private noncomputable def ep01101001111_0 : Blocks := edgeBlocks% "full/vectors/01101001111-E-0000.bin"
private noncomputable def ep01101001111_1 : Blocks := edgeBlocks% "full/vectors/01101001111-E-0001.bin"
noncomputable def ep01101001111 : Blocks := (Blocks.join ep01101001111_0 ep01101001111_1)
private theorem idp01101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100111.list =
    C ((2:ℤ)^178) * horner X vp01101001111.list + horner X ep01101001111.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101001111 : Branch 1 (-3383761639/8000000 : ℚ) vp0110100111 := by
  apply branch_checked idp01101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3383761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3387761639/4000000 : ℚ) by norm_num]
  exact coverp01101001111
theorem coverp0110100111 : Covers (-3383761639/8000000 : ℚ) vp0110100111 := join_branches bp01101001110 bp01101001111
private noncomputable def vp01101001101_0 : Blocks := edgeBlocks% "full/vectors/01101001101-V-0000.bin"
noncomputable def vp01101001101 : Blocks := vp01101001101_0
theorem coverp01101001101 : Covers (-3379761639/4000000 : ℚ) vp01101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp01101001100_0 : Blocks := edgeBlocks% "full/vectors/01101001100-V-0000.bin"
noncomputable def vp01101001100 : Blocks := vp01101001100_0
theorem coverp01101001100 : Covers (-3375761639/4000000 : ℚ) vp01101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100110_0 : Blocks := edgeBlocks% "full/vectors/0110100110-V-0000.bin"
private noncomputable def vp0110100110_1 : Blocks := edgeBlocks% "full/vectors/0110100110-V-0001.bin"
noncomputable def vp0110100110 : Blocks := (Blocks.join vp0110100110_0 vp0110100110_1)
private theorem bp01101001100 : Branch 0 (-3375761639/8000000 : ℚ) vp0110100110 := by
  apply branch_left_normalized (c:=vp01101001100) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3375761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3375761639/4000000 : ℚ) by norm_num]
  exact coverp01101001100
private noncomputable def ep01101001101_0 : Blocks := edgeBlocks% "full/vectors/01101001101-E-0000.bin"
private noncomputable def ep01101001101_1 : Blocks := edgeBlocks% "full/vectors/01101001101-E-0001.bin"
noncomputable def ep01101001101 : Blocks := (Blocks.join ep01101001101_0 ep01101001101_1)
private theorem idp01101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100110.list =
    C ((2:ℤ)^176) * horner X vp01101001101.list + horner X ep01101001101.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101001101 : Branch 1 (-3375761639/8000000 : ℚ) vp0110100110 := by
  apply branch_checked idp01101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3375761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3379761639/4000000 : ℚ) by norm_num]
  exact coverp01101001101
theorem coverp0110100110 : Covers (-3375761639/8000000 : ℚ) vp0110100110 := join_branches bp01101001100 bp01101001101
private noncomputable def vp011010011_0 : Blocks := edgeBlocks% "full/vectors/011010011-V-0000.bin"
private noncomputable def vp011010011_1 : Blocks := edgeBlocks% "full/vectors/011010011-V-0001.bin"
private noncomputable def vp011010011_2 : Blocks := edgeBlocks% "full/vectors/011010011-V-0002.bin"
noncomputable def vp011010011 : Blocks := (Blocks.join vp011010011_0 (Blocks.join vp011010011_1 vp011010011_2))
private theorem bp0110100110 : Branch 0 (-3375761639/16000000 : ℚ) vp011010011 := by
  apply branch_left_normalized (c:=vp0110100110) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-3375761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3375761639/8000000 : ℚ) by norm_num]
  exact coverp0110100110
private noncomputable def ep0110100111_0 : Blocks := edgeBlocks% "full/vectors/0110100111-E-0000.bin"
private noncomputable def ep0110100111_1 : Blocks := edgeBlocks% "full/vectors/0110100111-E-0001.bin"
private noncomputable def ep0110100111_2 : Blocks := edgeBlocks% "full/vectors/0110100111-E-0002.bin"
noncomputable def ep0110100111 : Blocks := (Blocks.join ep0110100111_0 (Blocks.join ep0110100111_1 ep0110100111_2))
private theorem idp0110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010011.list =
    C ((2:ℤ)^332) * horner X vp0110100111.list + horner X ep0110100111.list := by
  exact edge_identity (B := (2:ℤ)^528) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110100111 : Branch 1 (-3375761639/16000000 : ℚ) vp011010011 := by
  apply branch_checked idp0110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3375761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3383761639/8000000 : ℚ) by norm_num]
  exact coverp0110100111
theorem coverp011010011 : Covers (-3375761639/16000000 : ℚ) vp011010011 := join_branches bp0110100110 bp0110100111
private noncomputable def vp01101001011_0 : Blocks := edgeBlocks% "full/vectors/01101001011-V-0000.bin"
noncomputable def vp01101001011 : Blocks := vp01101001011_0
theorem coverp01101001011 : Covers (-3371761639/4000000 : ℚ) vp01101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp01101001010_0 : Blocks := edgeBlocks% "full/vectors/01101001010-V-0000.bin"
noncomputable def vp01101001010 : Blocks := vp01101001010_0
theorem coverp01101001010 : Covers (-3367761639/4000000 : ℚ) vp01101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100101_0 : Blocks := edgeBlocks% "full/vectors/0110100101-V-0000.bin"
private noncomputable def vp0110100101_1 : Blocks := edgeBlocks% "full/vectors/0110100101-V-0001.bin"
noncomputable def vp0110100101 : Blocks := (Blocks.join vp0110100101_0 vp0110100101_1)
private theorem bp01101001010 : Branch 0 (-3367761639/8000000 : ℚ) vp0110100101 := by
  apply branch_left_normalized (c:=vp01101001010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3367761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3367761639/4000000 : ℚ) by norm_num]
  exact coverp01101001010
private noncomputable def ep01101001011_0 : Blocks := edgeBlocks% "full/vectors/01101001011-E-0000.bin"
private noncomputable def ep01101001011_1 : Blocks := edgeBlocks% "full/vectors/01101001011-E-0001.bin"
noncomputable def ep01101001011 : Blocks := (Blocks.join ep01101001011_0 ep01101001011_1)
private theorem idp01101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100101.list =
    C ((2:ℤ)^175) * horner X vp01101001011.list + horner X ep01101001011.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101001011 : Branch 1 (-3367761639/8000000 : ℚ) vp0110100101 := by
  apply branch_checked idp01101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3367761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3371761639/4000000 : ℚ) by norm_num]
  exact coverp01101001011
theorem coverp0110100101 : Covers (-3367761639/8000000 : ℚ) vp0110100101 := join_branches bp01101001010 bp01101001011
private noncomputable def vp01101001001_0 : Blocks := edgeBlocks% "full/vectors/01101001001-V-0000.bin"
noncomputable def vp01101001001 : Blocks := vp01101001001_0
theorem coverp01101001001 : Covers (-3363761639/4000000 : ℚ) vp01101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp01101001000_0 : Blocks := edgeBlocks% "full/vectors/01101001000-V-0000.bin"
noncomputable def vp01101001000 : Blocks := vp01101001000_0
theorem coverp01101001000 : Covers (-3359761639/4000000 : ℚ) vp01101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100100_0 : Blocks := edgeBlocks% "full/vectors/0110100100-V-0000.bin"
private noncomputable def vp0110100100_1 : Blocks := edgeBlocks% "full/vectors/0110100100-V-0001.bin"
noncomputable def vp0110100100 : Blocks := (Blocks.join vp0110100100_0 vp0110100100_1)
private theorem bp01101001000 : Branch 0 (-3359761639/8000000 : ℚ) vp0110100100 := by
  apply branch_left_normalized (c:=vp01101001000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3359761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3359761639/4000000 : ℚ) by norm_num]
  exact coverp01101001000
private noncomputable def ep01101001001_0 : Blocks := edgeBlocks% "full/vectors/01101001001-E-0000.bin"
private noncomputable def ep01101001001_1 : Blocks := edgeBlocks% "full/vectors/01101001001-E-0001.bin"
noncomputable def ep01101001001 : Blocks := (Blocks.join ep01101001001_0 ep01101001001_1)
private theorem idp01101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100100.list =
    C ((2:ℤ)^175) * horner X vp01101001001.list + horner X ep01101001001.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101001001 : Branch 1 (-3359761639/8000000 : ℚ) vp0110100100 := by
  apply branch_checked idp01101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3359761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3363761639/4000000 : ℚ) by norm_num]
  exact coverp01101001001
theorem coverp0110100100 : Covers (-3359761639/8000000 : ℚ) vp0110100100 := join_branches bp01101001000 bp01101001001
private noncomputable def vp011010010_0 : Blocks := edgeBlocks% "full/vectors/011010010-V-0000.bin"
private noncomputable def vp011010010_1 : Blocks := edgeBlocks% "full/vectors/011010010-V-0001.bin"
private noncomputable def vp011010010_2 : Blocks := edgeBlocks% "full/vectors/011010010-V-0002.bin"
noncomputable def vp011010010 : Blocks := (Blocks.join vp011010010_0 (Blocks.join vp011010010_1 vp011010010_2))
private theorem bp0110100100 : Branch 0 (-3359761639/16000000 : ℚ) vp011010010 := by
  apply branch_left_normalized (c:=vp0110100100) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-3359761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3359761639/8000000 : ℚ) by norm_num]
  exact coverp0110100100
private noncomputable def ep0110100101_0 : Blocks := edgeBlocks% "full/vectors/0110100101-E-0000.bin"
private noncomputable def ep0110100101_1 : Blocks := edgeBlocks% "full/vectors/0110100101-E-0001.bin"
private noncomputable def ep0110100101_2 : Blocks := edgeBlocks% "full/vectors/0110100101-E-0002.bin"
noncomputable def ep0110100101 : Blocks := (Blocks.join ep0110100101_0 (Blocks.join ep0110100101_1 ep0110100101_2))
private theorem idp0110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010010.list =
    C ((2:ℤ)^333) * horner X vp0110100101.list + horner X ep0110100101.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110100101 : Branch 1 (-3359761639/16000000 : ℚ) vp011010010 := by
  apply branch_checked idp0110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3359761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3367761639/8000000 : ℚ) by norm_num]
  exact coverp0110100101
theorem coverp011010010 : Covers (-3359761639/16000000 : ℚ) vp011010010 := join_branches bp0110100100 bp0110100101
private noncomputable def vp01101001_0 : Blocks := edgeBlocks% "full/vectors/01101001-V-0000.bin"
private noncomputable def vp01101001_1 : Blocks := edgeBlocks% "full/vectors/01101001-V-0001.bin"
private noncomputable def vp01101001_2 : Blocks := edgeBlocks% "full/vectors/01101001-V-0002.bin"
private noncomputable def vp01101001_3 : Blocks := edgeBlocks% "full/vectors/01101001-V-0003.bin"
private noncomputable def vp01101001_4 : Blocks := edgeBlocks% "full/vectors/01101001-V-0004.bin"
noncomputable def vp01101001 : Blocks := (Blocks.join (Blocks.join vp01101001_0 vp01101001_1) (Blocks.join vp01101001_2 (Blocks.join vp01101001_3 vp01101001_4)))
private theorem bp011010010 : Branch 0 (-3359761639/32000000 : ℚ) vp01101001 := by
  apply branch_left_normalized (c:=vp011010010) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-3359761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3359761639/16000000 : ℚ) by norm_num]
  exact coverp011010010
private noncomputable def ep011010011_0 : Blocks := edgeBlocks% "full/vectors/011010011-E-0000.bin"
private noncomputable def ep011010011_1 : Blocks := edgeBlocks% "full/vectors/011010011-E-0001.bin"
private noncomputable def ep011010011_2 : Blocks := edgeBlocks% "full/vectors/011010011-E-0002.bin"
private noncomputable def ep011010011_3 : Blocks := edgeBlocks% "full/vectors/011010011-E-0003.bin"
private noncomputable def ep011010011_4 : Blocks := edgeBlocks% "full/vectors/011010011-E-0004.bin"
noncomputable def ep011010011 : Blocks := (Blocks.join (Blocks.join ep011010011_0 ep011010011_1) (Blocks.join ep011010011_2 (Blocks.join ep011010011_3 ep011010011_4)))
private theorem idp011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101001.list =
    C ((2:ℤ)^645) * horner X vp011010011.list + horner X ep011010011.list := by
  exact edge_identity (B := (2:ℤ)^935) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010011 : Branch 1 (-3359761639/32000000 : ℚ) vp01101001 := by
  apply branch_checked idp011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3359761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3375761639/16000000 : ℚ) by norm_num]
  exact coverp011010011
theorem coverp01101001 : Covers (-3359761639/32000000 : ℚ) vp01101001 := join_branches bp011010010 bp011010011
private noncomputable def vp01101000111_0 : Blocks := edgeBlocks% "full/vectors/01101000111-V-0000.bin"
noncomputable def vp01101000111 : Blocks := vp01101000111_0
theorem coverp01101000111 : Covers (-3355761639/4000000 : ℚ) vp01101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp01101000110_0 : Blocks := edgeBlocks% "full/vectors/01101000110-V-0000.bin"
noncomputable def vp01101000110 : Blocks := vp01101000110_0
theorem coverp01101000110 : Covers (-3351761639/4000000 : ℚ) vp01101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100011_0 : Blocks := edgeBlocks% "full/vectors/0110100011-V-0000.bin"
private noncomputable def vp0110100011_1 : Blocks := edgeBlocks% "full/vectors/0110100011-V-0001.bin"
noncomputable def vp0110100011 : Blocks := (Blocks.join vp0110100011_0 vp0110100011_1)
private theorem bp01101000110 : Branch 0 (-3351761639/8000000 : ℚ) vp0110100011 := by
  apply branch_left_normalized (c:=vp01101000110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3351761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3351761639/4000000 : ℚ) by norm_num]
  exact coverp01101000110
private noncomputable def ep01101000111_0 : Blocks := edgeBlocks% "full/vectors/01101000111-E-0000.bin"
private noncomputable def ep01101000111_1 : Blocks := edgeBlocks% "full/vectors/01101000111-E-0001.bin"
noncomputable def ep01101000111 : Blocks := (Blocks.join ep01101000111_0 ep01101000111_1)
private theorem idp01101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100011.list =
    C ((2:ℤ)^176) * horner X vp01101000111.list + horner X ep01101000111.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101000111 : Branch 1 (-3351761639/8000000 : ℚ) vp0110100011 := by
  apply branch_checked idp01101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3351761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3355761639/4000000 : ℚ) by norm_num]
  exact coverp01101000111
theorem coverp0110100011 : Covers (-3351761639/8000000 : ℚ) vp0110100011 := join_branches bp01101000110 bp01101000111
private noncomputable def vp01101000101_0 : Blocks := edgeBlocks% "full/vectors/01101000101-V-0000.bin"
noncomputable def vp01101000101 : Blocks := vp01101000101_0
theorem coverp01101000101 : Covers (-3347761639/4000000 : ℚ) vp01101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp01101000100_0 : Blocks := edgeBlocks% "full/vectors/01101000100-V-0000.bin"
noncomputable def vp01101000100 : Blocks := vp01101000100_0
theorem coverp01101000100 : Covers (-3343761639/4000000 : ℚ) vp01101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100010_0 : Blocks := edgeBlocks% "full/vectors/0110100010-V-0000.bin"
private noncomputable def vp0110100010_1 : Blocks := edgeBlocks% "full/vectors/0110100010-V-0001.bin"
noncomputable def vp0110100010 : Blocks := (Blocks.join vp0110100010_0 vp0110100010_1)
private theorem bp01101000100 : Branch 0 (-3343761639/8000000 : ℚ) vp0110100010 := by
  apply branch_left_normalized (c:=vp01101000100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3343761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3343761639/4000000 : ℚ) by norm_num]
  exact coverp01101000100
private noncomputable def ep01101000101_0 : Blocks := edgeBlocks% "full/vectors/01101000101-E-0000.bin"
private noncomputable def ep01101000101_1 : Blocks := edgeBlocks% "full/vectors/01101000101-E-0001.bin"
noncomputable def ep01101000101 : Blocks := (Blocks.join ep01101000101_0 ep01101000101_1)
private theorem idp01101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100010.list =
    C ((2:ℤ)^176) * horner X vp01101000101.list + horner X ep01101000101.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101000101 : Branch 1 (-3343761639/8000000 : ℚ) vp0110100010 := by
  apply branch_checked idp01101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3343761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3347761639/4000000 : ℚ) by norm_num]
  exact coverp01101000101
theorem coverp0110100010 : Covers (-3343761639/8000000 : ℚ) vp0110100010 := join_branches bp01101000100 bp01101000101
private noncomputable def vp011010001_0 : Blocks := edgeBlocks% "full/vectors/011010001-V-0000.bin"
private noncomputable def vp011010001_1 : Blocks := edgeBlocks% "full/vectors/011010001-V-0001.bin"
private noncomputable def vp011010001_2 : Blocks := edgeBlocks% "full/vectors/011010001-V-0002.bin"
noncomputable def vp011010001 : Blocks := (Blocks.join vp011010001_0 (Blocks.join vp011010001_1 vp011010001_2))
private theorem bp0110100010 : Branch 0 (-3343761639/16000000 : ℚ) vp011010001 := by
  apply branch_left_normalized (c:=vp0110100010) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-3343761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3343761639/8000000 : ℚ) by norm_num]
  exact coverp0110100010
private noncomputable def ep0110100011_0 : Blocks := edgeBlocks% "full/vectors/0110100011-E-0000.bin"
private noncomputable def ep0110100011_1 : Blocks := edgeBlocks% "full/vectors/0110100011-E-0001.bin"
private noncomputable def ep0110100011_2 : Blocks := edgeBlocks% "full/vectors/0110100011-E-0002.bin"
noncomputable def ep0110100011 : Blocks := (Blocks.join ep0110100011_0 (Blocks.join ep0110100011_1 ep0110100011_2))
private theorem idp0110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010001.list =
    C ((2:ℤ)^336) * horner X vp0110100011.list + horner X ep0110100011.list := by
  exact edge_identity (B := (2:ℤ)^526) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110100011 : Branch 1 (-3343761639/16000000 : ℚ) vp011010001 := by
  apply branch_checked idp0110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3343761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3351761639/8000000 : ℚ) by norm_num]
  exact coverp0110100011
theorem coverp011010001 : Covers (-3343761639/16000000 : ℚ) vp011010001 := join_branches bp0110100010 bp0110100011
private noncomputable def vp01101000011_0 : Blocks := edgeBlocks% "full/vectors/01101000011-V-0000.bin"
noncomputable def vp01101000011 : Blocks := vp01101000011_0
theorem coverp01101000011 : Covers (-3339761639/4000000 : ℚ) vp01101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp01101000010_0 : Blocks := edgeBlocks% "full/vectors/01101000010-V-0000.bin"
noncomputable def vp01101000010 : Blocks := vp01101000010_0
theorem coverp01101000010 : Covers (-3335761639/4000000 : ℚ) vp01101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100001_0 : Blocks := edgeBlocks% "full/vectors/0110100001-V-0000.bin"
private noncomputable def vp0110100001_1 : Blocks := edgeBlocks% "full/vectors/0110100001-V-0001.bin"
noncomputable def vp0110100001 : Blocks := (Blocks.join vp0110100001_0 vp0110100001_1)
private theorem bp01101000010 : Branch 0 (-3335761639/8000000 : ℚ) vp0110100001 := by
  apply branch_left_normalized (c:=vp01101000010) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3335761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3335761639/4000000 : ℚ) by norm_num]
  exact coverp01101000010
private noncomputable def ep01101000011_0 : Blocks := edgeBlocks% "full/vectors/01101000011-E-0000.bin"
private noncomputable def ep01101000011_1 : Blocks := edgeBlocks% "full/vectors/01101000011-E-0001.bin"
noncomputable def ep01101000011 : Blocks := (Blocks.join ep01101000011_0 ep01101000011_1)
private theorem idp01101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100001.list =
    C ((2:ℤ)^178) * horner X vp01101000011.list + horner X ep01101000011.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101000011 : Branch 1 (-3335761639/8000000 : ℚ) vp0110100001 := by
  apply branch_checked idp01101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3335761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3339761639/4000000 : ℚ) by norm_num]
  exact coverp01101000011
theorem coverp0110100001 : Covers (-3335761639/8000000 : ℚ) vp0110100001 := join_branches bp01101000010 bp01101000011
private noncomputable def vp01101000001_0 : Blocks := edgeBlocks% "full/vectors/01101000001-V-0000.bin"
noncomputable def vp01101000001 : Blocks := vp01101000001_0
theorem coverp01101000001 : Covers (-3331761639/4000000 : ℚ) vp01101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp01101000000_0 : Blocks := edgeBlocks% "full/vectors/01101000000-V-0000.bin"
noncomputable def vp01101000000 : Blocks := vp01101000000_0
theorem coverp01101000000 : Covers (-3327761639/4000000 : ℚ) vp01101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0110100000_0 : Blocks := edgeBlocks% "full/vectors/0110100000-V-0000.bin"
private noncomputable def vp0110100000_1 : Blocks := edgeBlocks% "full/vectors/0110100000-V-0001.bin"
noncomputable def vp0110100000 : Blocks := (Blocks.join vp0110100000_0 vp0110100000_1)
private theorem bp01101000000 : Branch 0 (-3327761639/8000000 : ℚ) vp0110100000 := by
  apply branch_left_normalized (c:=vp01101000000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3327761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/4000000 : ℚ) by norm_num]
  exact coverp01101000000
private noncomputable def ep01101000001_0 : Blocks := edgeBlocks% "full/vectors/01101000001-E-0000.bin"
private noncomputable def ep01101000001_1 : Blocks := edgeBlocks% "full/vectors/01101000001-E-0001.bin"
noncomputable def ep01101000001 : Blocks := (Blocks.join ep01101000001_0 ep01101000001_1)
private theorem idp01101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100000.list =
    C ((2:ℤ)^182) * horner X vp01101000001.list + horner X ep01101000001.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101000001 : Branch 1 (-3327761639/8000000 : ℚ) vp0110100000 := by
  apply branch_checked idp01101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3331761639/4000000 : ℚ) by norm_num]
  exact coverp01101000001
theorem coverp0110100000 : Covers (-3327761639/8000000 : ℚ) vp0110100000 := join_branches bp01101000000 bp01101000001
private noncomputable def vp011010000_0 : Blocks := edgeBlocks% "full/vectors/011010000-V-0000.bin"
private noncomputable def vp011010000_1 : Blocks := edgeBlocks% "full/vectors/011010000-V-0001.bin"
private noncomputable def vp011010000_2 : Blocks := edgeBlocks% "full/vectors/011010000-V-0002.bin"
noncomputable def vp011010000 : Blocks := (Blocks.join vp011010000_0 (Blocks.join vp011010000_1 vp011010000_2))
private theorem bp0110100000 : Branch 0 (-3327761639/16000000 : ℚ) vp011010000 := by
  apply branch_left_normalized (c:=vp0110100000) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3327761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/8000000 : ℚ) by norm_num]
  exact coverp0110100000
private noncomputable def ep0110100001_0 : Blocks := edgeBlocks% "full/vectors/0110100001-E-0000.bin"
private noncomputable def ep0110100001_1 : Blocks := edgeBlocks% "full/vectors/0110100001-E-0001.bin"
private noncomputable def ep0110100001_2 : Blocks := edgeBlocks% "full/vectors/0110100001-E-0002.bin"
noncomputable def ep0110100001 : Blocks := (Blocks.join ep0110100001_0 (Blocks.join ep0110100001_1 ep0110100001_2))
private theorem idp0110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010000.list =
    C ((2:ℤ)^343) * horner X vp0110100001.list + horner X ep0110100001.list := by
  exact edge_identity (B := (2:ℤ)^536) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110100001 : Branch 1 (-3327761639/16000000 : ℚ) vp011010000 := by
  apply branch_checked idp0110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3335761639/8000000 : ℚ) by norm_num]
  exact coverp0110100001
theorem coverp011010000 : Covers (-3327761639/16000000 : ℚ) vp011010000 := join_branches bp0110100000 bp0110100001
private noncomputable def vp01101000_0 : Blocks := edgeBlocks% "full/vectors/01101000-V-0000.bin"
private noncomputable def vp01101000_1 : Blocks := edgeBlocks% "full/vectors/01101000-V-0001.bin"
private noncomputable def vp01101000_2 : Blocks := edgeBlocks% "full/vectors/01101000-V-0002.bin"
private noncomputable def vp01101000_3 : Blocks := edgeBlocks% "full/vectors/01101000-V-0003.bin"
private noncomputable def vp01101000_4 : Blocks := edgeBlocks% "full/vectors/01101000-V-0004.bin"
noncomputable def vp01101000 : Blocks := (Blocks.join (Blocks.join vp01101000_0 vp01101000_1) (Blocks.join vp01101000_2 (Blocks.join vp01101000_3 vp01101000_4)))
private theorem bp011010000 : Branch 0 (-3327761639/32000000 : ℚ) vp01101000 := by
  apply branch_left_normalized (c:=vp011010000) (k:=0) (m:=292) (by decide +kernel)
  rw [show 2*(-3327761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/16000000 : ℚ) by norm_num]
  exact coverp011010000
private noncomputable def ep011010001_0 : Blocks := edgeBlocks% "full/vectors/011010001-E-0000.bin"
private noncomputable def ep011010001_1 : Blocks := edgeBlocks% "full/vectors/011010001-E-0001.bin"
private noncomputable def ep011010001_2 : Blocks := edgeBlocks% "full/vectors/011010001-E-0002.bin"
private noncomputable def ep011010001_3 : Blocks := edgeBlocks% "full/vectors/011010001-E-0003.bin"
private noncomputable def ep011010001_4 : Blocks := edgeBlocks% "full/vectors/011010001-E-0004.bin"
noncomputable def ep011010001 : Blocks := (Blocks.join (Blocks.join ep011010001_0 ep011010001_1) (Blocks.join ep011010001_2 (Blocks.join ep011010001_3 ep011010001_4)))
private theorem idp011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101000.list =
    C ((2:ℤ)^661) * horner X vp011010001.list + horner X ep011010001.list := by
  exact edge_identity (B := (2:ℤ)^950) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011010001 : Branch 1 (-3327761639/32000000 : ℚ) vp01101000 := by
  apply branch_checked idp011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3343761639/16000000 : ℚ) by norm_num]
  exact coverp011010001
theorem coverp01101000 : Covers (-3327761639/32000000 : ℚ) vp01101000 := join_branches bp011010000 bp011010001
private noncomputable def vp0110100_0 : Blocks := edgeBlocks% "full/vectors/0110100-V-0000.bin"
private noncomputable def vp0110100_1 : Blocks := edgeBlocks% "full/vectors/0110100-V-0001.bin"
private noncomputable def vp0110100_2 : Blocks := edgeBlocks% "full/vectors/0110100-V-0002.bin"
private noncomputable def vp0110100_3 : Blocks := edgeBlocks% "full/vectors/0110100-V-0003.bin"
private noncomputable def vp0110100_4 : Blocks := edgeBlocks% "full/vectors/0110100-V-0004.bin"
private noncomputable def vp0110100_5 : Blocks := edgeBlocks% "full/vectors/0110100-V-0005.bin"
private noncomputable def vp0110100_6 : Blocks := edgeBlocks% "full/vectors/0110100-V-0006.bin"
private noncomputable def vp0110100_7 : Blocks := edgeBlocks% "full/vectors/0110100-V-0007.bin"
private noncomputable def vp0110100_8 : Blocks := edgeBlocks% "full/vectors/0110100-V-0008.bin"
noncomputable def vp0110100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110100_0 vp0110100_1) (Blocks.join vp0110100_2 vp0110100_3)) (Blocks.join (Blocks.join vp0110100_4 vp0110100_5) (Blocks.join vp0110100_6 (Blocks.join vp0110100_7 vp0110100_8))))
private theorem bp01101000 : Branch 0 (-3327761639/64000000 : ℚ) vp0110100 := by
  apply branch_left_normalized (c:=vp01101000) (k:=0) (m:=562) (by decide +kernel)
  rw [show 2*(-3327761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/32000000 : ℚ) by norm_num]
  exact coverp01101000
private noncomputable def ep01101001_0 : Blocks := edgeBlocks% "full/vectors/01101001-E-0000.bin"
private noncomputable def ep01101001_1 : Blocks := edgeBlocks% "full/vectors/01101001-E-0001.bin"
private noncomputable def ep01101001_2 : Blocks := edgeBlocks% "full/vectors/01101001-E-0002.bin"
private noncomputable def ep01101001_3 : Blocks := edgeBlocks% "full/vectors/01101001-E-0003.bin"
private noncomputable def ep01101001_4 : Blocks := edgeBlocks% "full/vectors/01101001-E-0004.bin"
private noncomputable def ep01101001_5 : Blocks := edgeBlocks% "full/vectors/01101001-E-0005.bin"
private noncomputable def ep01101001_6 : Blocks := edgeBlocks% "full/vectors/01101001-E-0006.bin"
private noncomputable def ep01101001_7 : Blocks := edgeBlocks% "full/vectors/01101001-E-0007.bin"
private noncomputable def ep01101001_8 : Blocks := edgeBlocks% "full/vectors/01101001-E-0008.bin"
noncomputable def ep01101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01101001_0 ep01101001_1) (Blocks.join ep01101001_2 ep01101001_3)) (Blocks.join (Blocks.join ep01101001_4 ep01101001_5) (Blocks.join ep01101001_6 (Blocks.join ep01101001_7 ep01101001_8))))
private theorem idp01101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110100.list =
    C ((2:ℤ)^1285) * horner X vp01101001.list + horner X ep01101001.list := by
  exact edge_identity (B := (2:ℤ)^1768) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101001 : Branch 1 (-3327761639/64000000 : ℚ) vp0110100 := by
  apply branch_checked idp01101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3359761639/32000000 : ℚ) by norm_num]
  exact coverp01101001
theorem coverp0110100 : Covers (-3327761639/64000000 : ℚ) vp0110100 := join_branches bp01101000 bp01101001
private noncomputable def vp011010_0 : Blocks := edgeBlocks% "full/vectors/011010-V-0000.bin"
private noncomputable def vp011010_1 : Blocks := edgeBlocks% "full/vectors/011010-V-0001.bin"
private noncomputable def vp011010_2 : Blocks := edgeBlocks% "full/vectors/011010-V-0002.bin"
private noncomputable def vp011010_3 : Blocks := edgeBlocks% "full/vectors/011010-V-0003.bin"
private noncomputable def vp011010_4 : Blocks := edgeBlocks% "full/vectors/011010-V-0004.bin"
private noncomputable def vp011010_5 : Blocks := edgeBlocks% "full/vectors/011010-V-0005.bin"
private noncomputable def vp011010_6 : Blocks := edgeBlocks% "full/vectors/011010-V-0006.bin"
private noncomputable def vp011010_7 : Blocks := edgeBlocks% "full/vectors/011010-V-0007.bin"
private noncomputable def vp011010_8 : Blocks := edgeBlocks% "full/vectors/011010-V-0008.bin"
private noncomputable def vp011010_9 : Blocks := edgeBlocks% "full/vectors/011010-V-0009.bin"
private noncomputable def vp011010_10 : Blocks := edgeBlocks% "full/vectors/011010-V-0010.bin"
private noncomputable def vp011010_11 : Blocks := edgeBlocks% "full/vectors/011010-V-0011.bin"
private noncomputable def vp011010_12 : Blocks := edgeBlocks% "full/vectors/011010-V-0012.bin"
private noncomputable def vp011010_13 : Blocks := edgeBlocks% "full/vectors/011010-V-0013.bin"
private noncomputable def vp011010_14 : Blocks := edgeBlocks% "full/vectors/011010-V-0014.bin"
private noncomputable def vp011010_15 : Blocks := edgeBlocks% "full/vectors/011010-V-0015.bin"
private noncomputable def vp011010_16 : Blocks := edgeBlocks% "full/vectors/011010-V-0016.bin"
noncomputable def vp011010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011010_0 vp011010_1) (Blocks.join vp011010_2 vp011010_3)) (Blocks.join (Blocks.join vp011010_4 vp011010_5) (Blocks.join vp011010_6 vp011010_7))) (Blocks.join (Blocks.join (Blocks.join vp011010_8 vp011010_9) (Blocks.join vp011010_10 vp011010_11)) (Blocks.join (Blocks.join vp011010_12 vp011010_13) (Blocks.join vp011010_14 (Blocks.join vp011010_15 vp011010_16)))))
private theorem bp0110100 : Branch 0 (-3327761639/128000000 : ℚ) vp011010 := by
  apply branch_left_normalized (c:=vp0110100) (k:=0) (m:=1093) (by decide +kernel)
  rw [show 2*(-3327761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/64000000 : ℚ) by norm_num]
  exact coverp0110100
private noncomputable def ep0110101_0 : Blocks := edgeBlocks% "full/vectors/0110101-E-0000.bin"
private noncomputable def ep0110101_1 : Blocks := edgeBlocks% "full/vectors/0110101-E-0001.bin"
private noncomputable def ep0110101_2 : Blocks := edgeBlocks% "full/vectors/0110101-E-0002.bin"
private noncomputable def ep0110101_3 : Blocks := edgeBlocks% "full/vectors/0110101-E-0003.bin"
private noncomputable def ep0110101_4 : Blocks := edgeBlocks% "full/vectors/0110101-E-0004.bin"
private noncomputable def ep0110101_5 : Blocks := edgeBlocks% "full/vectors/0110101-E-0005.bin"
private noncomputable def ep0110101_6 : Blocks := edgeBlocks% "full/vectors/0110101-E-0006.bin"
private noncomputable def ep0110101_7 : Blocks := edgeBlocks% "full/vectors/0110101-E-0007.bin"
private noncomputable def ep0110101_8 : Blocks := edgeBlocks% "full/vectors/0110101-E-0008.bin"
private noncomputable def ep0110101_9 : Blocks := edgeBlocks% "full/vectors/0110101-E-0009.bin"
private noncomputable def ep0110101_10 : Blocks := edgeBlocks% "full/vectors/0110101-E-0010.bin"
private noncomputable def ep0110101_11 : Blocks := edgeBlocks% "full/vectors/0110101-E-0011.bin"
private noncomputable def ep0110101_12 : Blocks := edgeBlocks% "full/vectors/0110101-E-0012.bin"
private noncomputable def ep0110101_13 : Blocks := edgeBlocks% "full/vectors/0110101-E-0013.bin"
private noncomputable def ep0110101_14 : Blocks := edgeBlocks% "full/vectors/0110101-E-0014.bin"
private noncomputable def ep0110101_15 : Blocks := edgeBlocks% "full/vectors/0110101-E-0015.bin"
private noncomputable def ep0110101_16 : Blocks := edgeBlocks% "full/vectors/0110101-E-0016.bin"
noncomputable def ep0110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0110101_0 ep0110101_1) (Blocks.join ep0110101_2 ep0110101_3)) (Blocks.join (Blocks.join ep0110101_4 ep0110101_5) (Blocks.join ep0110101_6 ep0110101_7))) (Blocks.join (Blocks.join (Blocks.join ep0110101_8 ep0110101_9) (Blocks.join ep0110101_10 ep0110101_11)) (Blocks.join (Blocks.join ep0110101_12 ep0110101_13) (Blocks.join ep0110101_14 (Blocks.join ep0110101_15 ep0110101_16)))))
private theorem idp0110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011010.list =
    C ((2:ℤ)^2498) * horner X vp0110101.list + horner X ep0110101.list := by
  exact edge_identity (B := (2:ℤ)^3375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110101 : Branch 1 (-3327761639/128000000 : ℚ) vp011010 := by
  apply branch_checked idp0110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3391761639/64000000 : ℚ) by norm_num]
  exact coverp0110101
theorem coverp011010 : Covers (-3327761639/128000000 : ℚ) vp011010 := join_branches bp0110100 bp0110101
private noncomputable def vp01101_0 : Blocks := edgeBlocks% "full/vectors/01101-V-0000.bin"
private noncomputable def vp01101_1 : Blocks := edgeBlocks% "full/vectors/01101-V-0001.bin"
private noncomputable def vp01101_2 : Blocks := edgeBlocks% "full/vectors/01101-V-0002.bin"
private noncomputable def vp01101_3 : Blocks := edgeBlocks% "full/vectors/01101-V-0003.bin"
private noncomputable def vp01101_4 : Blocks := edgeBlocks% "full/vectors/01101-V-0004.bin"
private noncomputable def vp01101_5 : Blocks := edgeBlocks% "full/vectors/01101-V-0005.bin"
private noncomputable def vp01101_6 : Blocks := edgeBlocks% "full/vectors/01101-V-0006.bin"
private noncomputable def vp01101_7 : Blocks := edgeBlocks% "full/vectors/01101-V-0007.bin"
private noncomputable def vp01101_8 : Blocks := edgeBlocks% "full/vectors/01101-V-0008.bin"
private noncomputable def vp01101_9 : Blocks := edgeBlocks% "full/vectors/01101-V-0009.bin"
private noncomputable def vp01101_10 : Blocks := edgeBlocks% "full/vectors/01101-V-0010.bin"
private noncomputable def vp01101_11 : Blocks := edgeBlocks% "full/vectors/01101-V-0011.bin"
private noncomputable def vp01101_12 : Blocks := edgeBlocks% "full/vectors/01101-V-0012.bin"
private noncomputable def vp01101_13 : Blocks := edgeBlocks% "full/vectors/01101-V-0013.bin"
private noncomputable def vp01101_14 : Blocks := edgeBlocks% "full/vectors/01101-V-0014.bin"
private noncomputable def vp01101_15 : Blocks := edgeBlocks% "full/vectors/01101-V-0015.bin"
private noncomputable def vp01101_16 : Blocks := edgeBlocks% "full/vectors/01101-V-0016.bin"
private noncomputable def vp01101_17 : Blocks := edgeBlocks% "full/vectors/01101-V-0017.bin"
private noncomputable def vp01101_18 : Blocks := edgeBlocks% "full/vectors/01101-V-0018.bin"
private noncomputable def vp01101_19 : Blocks := edgeBlocks% "full/vectors/01101-V-0019.bin"
private noncomputable def vp01101_20 : Blocks := edgeBlocks% "full/vectors/01101-V-0020.bin"
private noncomputable def vp01101_21 : Blocks := edgeBlocks% "full/vectors/01101-V-0021.bin"
private noncomputable def vp01101_22 : Blocks := edgeBlocks% "full/vectors/01101-V-0022.bin"
private noncomputable def vp01101_23 : Blocks := edgeBlocks% "full/vectors/01101-V-0023.bin"
private noncomputable def vp01101_24 : Blocks := edgeBlocks% "full/vectors/01101-V-0024.bin"
private noncomputable def vp01101_25 : Blocks := edgeBlocks% "full/vectors/01101-V-0025.bin"
private noncomputable def vp01101_26 : Blocks := edgeBlocks% "full/vectors/01101-V-0026.bin"
private noncomputable def vp01101_27 : Blocks := edgeBlocks% "full/vectors/01101-V-0027.bin"
private noncomputable def vp01101_28 : Blocks := edgeBlocks% "full/vectors/01101-V-0028.bin"
private noncomputable def vp01101_29 : Blocks := edgeBlocks% "full/vectors/01101-V-0029.bin"
private noncomputable def vp01101_30 : Blocks := edgeBlocks% "full/vectors/01101-V-0030.bin"
private noncomputable def vp01101_31 : Blocks := edgeBlocks% "full/vectors/01101-V-0031.bin"
private noncomputable def vp01101_32 : Blocks := edgeBlocks% "full/vectors/01101-V-0032.bin"
noncomputable def vp01101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01101_0 vp01101_1) (Blocks.join vp01101_2 vp01101_3)) (Blocks.join (Blocks.join vp01101_4 vp01101_5) (Blocks.join vp01101_6 vp01101_7))) (Blocks.join (Blocks.join (Blocks.join vp01101_8 vp01101_9) (Blocks.join vp01101_10 vp01101_11)) (Blocks.join (Blocks.join vp01101_12 vp01101_13) (Blocks.join vp01101_14 vp01101_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01101_16 vp01101_17) (Blocks.join vp01101_18 vp01101_19)) (Blocks.join (Blocks.join vp01101_20 vp01101_21) (Blocks.join vp01101_22 vp01101_23))) (Blocks.join (Blocks.join (Blocks.join vp01101_24 vp01101_25) (Blocks.join vp01101_26 vp01101_27)) (Blocks.join (Blocks.join vp01101_28 vp01101_29) (Blocks.join vp01101_30 (Blocks.join vp01101_31 vp01101_32))))))
private theorem bp011010 : Branch 0 (-3327761639/256000000 : ℚ) vp01101 := by
  apply branch_left_normalized (c:=vp011010) (k:=0) (m:=2131) (by decide +kernel)
  rw [show 2*(-3327761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-3327761639/128000000 : ℚ) by norm_num]
  exact coverp011010
private noncomputable def ep011011_0 : Blocks := edgeBlocks% "full/vectors/011011-E-0000.bin"
private noncomputable def ep011011_1 : Blocks := edgeBlocks% "full/vectors/011011-E-0001.bin"
private noncomputable def ep011011_2 : Blocks := edgeBlocks% "full/vectors/011011-E-0002.bin"
private noncomputable def ep011011_3 : Blocks := edgeBlocks% "full/vectors/011011-E-0003.bin"
private noncomputable def ep011011_4 : Blocks := edgeBlocks% "full/vectors/011011-E-0004.bin"
private noncomputable def ep011011_5 : Blocks := edgeBlocks% "full/vectors/011011-E-0005.bin"
private noncomputable def ep011011_6 : Blocks := edgeBlocks% "full/vectors/011011-E-0006.bin"
private noncomputable def ep011011_7 : Blocks := edgeBlocks% "full/vectors/011011-E-0007.bin"
private noncomputable def ep011011_8 : Blocks := edgeBlocks% "full/vectors/011011-E-0008.bin"
private noncomputable def ep011011_9 : Blocks := edgeBlocks% "full/vectors/011011-E-0009.bin"
private noncomputable def ep011011_10 : Blocks := edgeBlocks% "full/vectors/011011-E-0010.bin"
private noncomputable def ep011011_11 : Blocks := edgeBlocks% "full/vectors/011011-E-0011.bin"
private noncomputable def ep011011_12 : Blocks := edgeBlocks% "full/vectors/011011-E-0012.bin"
private noncomputable def ep011011_13 : Blocks := edgeBlocks% "full/vectors/011011-E-0013.bin"
private noncomputable def ep011011_14 : Blocks := edgeBlocks% "full/vectors/011011-E-0014.bin"
private noncomputable def ep011011_15 : Blocks := edgeBlocks% "full/vectors/011011-E-0015.bin"
private noncomputable def ep011011_16 : Blocks := edgeBlocks% "full/vectors/011011-E-0016.bin"
private noncomputable def ep011011_17 : Blocks := edgeBlocks% "full/vectors/011011-E-0017.bin"
private noncomputable def ep011011_18 : Blocks := edgeBlocks% "full/vectors/011011-E-0018.bin"
private noncomputable def ep011011_19 : Blocks := edgeBlocks% "full/vectors/011011-E-0019.bin"
private noncomputable def ep011011_20 : Blocks := edgeBlocks% "full/vectors/011011-E-0020.bin"
private noncomputable def ep011011_21 : Blocks := edgeBlocks% "full/vectors/011011-E-0021.bin"
private noncomputable def ep011011_22 : Blocks := edgeBlocks% "full/vectors/011011-E-0022.bin"
private noncomputable def ep011011_23 : Blocks := edgeBlocks% "full/vectors/011011-E-0023.bin"
private noncomputable def ep011011_24 : Blocks := edgeBlocks% "full/vectors/011011-E-0024.bin"
private noncomputable def ep011011_25 : Blocks := edgeBlocks% "full/vectors/011011-E-0025.bin"
private noncomputable def ep011011_26 : Blocks := edgeBlocks% "full/vectors/011011-E-0026.bin"
private noncomputable def ep011011_27 : Blocks := edgeBlocks% "full/vectors/011011-E-0027.bin"
private noncomputable def ep011011_28 : Blocks := edgeBlocks% "full/vectors/011011-E-0028.bin"
private noncomputable def ep011011_29 : Blocks := edgeBlocks% "full/vectors/011011-E-0029.bin"
private noncomputable def ep011011_30 : Blocks := edgeBlocks% "full/vectors/011011-E-0030.bin"
private noncomputable def ep011011_31 : Blocks := edgeBlocks% "full/vectors/011011-E-0031.bin"
private noncomputable def ep011011_32 : Blocks := edgeBlocks% "full/vectors/011011-E-0032.bin"
noncomputable def ep011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011011_0 ep011011_1) (Blocks.join ep011011_2 ep011011_3)) (Blocks.join (Blocks.join ep011011_4 ep011011_5) (Blocks.join ep011011_6 ep011011_7))) (Blocks.join (Blocks.join (Blocks.join ep011011_8 ep011011_9) (Blocks.join ep011011_10 ep011011_11)) (Blocks.join (Blocks.join ep011011_12 ep011011_13) (Blocks.join ep011011_14 ep011011_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011011_16 ep011011_17) (Blocks.join ep011011_18 ep011011_19)) (Blocks.join (Blocks.join ep011011_20 ep011011_21) (Blocks.join ep011011_22 ep011011_23))) (Blocks.join (Blocks.join (Blocks.join ep011011_24 ep011011_25) (Blocks.join ep011011_26 ep011011_27)) (Blocks.join (Blocks.join ep011011_28 ep011011_29) (Blocks.join ep011011_30 (Blocks.join ep011011_31 ep011011_32))))))
private def ptsp011011 : List ℤ := [((2:ℤ)^2927+0),((2:ℤ)^2927+1),((2:ℤ)^2927+2)]
private theorem boundp011011 : 2^vp01101.size*absSum vp01101.list + ((2:ℤ)^4835*absSum vp011011.list+absSum ep011011.list) < (2:ℤ)^6459 := by decide +kernel
private theorem pointp011011_0 : fastHom 1 ((2:ℤ)^2927+0) vp01101 = ((2:ℤ)^4835)*vp011011.subst ((2:ℤ)^2927+0)+ep011011.subst ((2:ℤ)^2927+0) := by decide +kernel
private theorem pointp011011_1 : fastHom 1 ((2:ℤ)^2927+1) vp01101 = ((2:ℤ)^4835)*vp011011.subst ((2:ℤ)^2927+1)+ep011011.subst ((2:ℤ)^2927+1) := by decide +kernel
private theorem pointp011011_2 : fastHom 1 ((2:ℤ)^2927+2) vp01101 = ((2:ℤ)^4835)*vp011011.subst ((2:ℤ)^2927+2)+ep011011.subst ((2:ℤ)^2927+2) := by decide +kernel
private theorem checkp011011 (x:ℤ) (hx:x ∈ ptsp011011) : fastHom 1 x vp01101 = ((2:ℤ)^4835)*vp011011.subst x+ep011011.subst x := by
  simp only [ptsp011011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp011011_0
  · exact pointp011011_1
  · exact pointp011011_2
private theorem idp011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101.list =
    C ((2:ℤ)^4835) * horner X vp011011.list + horner X ep011011.list := by
  apply edge_identity (B := (2:ℤ)^6459) (by decide) (by positivity) (by positivity) boundp011011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp011011 (by decide +kernel)
  · have h : ptsp011011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp011011.trans_le (by decide +kernel)
  · exact checkp011011
private theorem bp011011 : Branch 1 (-3327761639/256000000 : ℚ) vp01101 := by
  apply branch_checked idp011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3327761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-3455761639/128000000 : ℚ) by norm_num]
  exact coverp011011
theorem coverp01101 : Covers (-3327761639/256000000 : ℚ) vp01101 := join_branches bp011010 bp011011
end NextProof.EdgeFull

