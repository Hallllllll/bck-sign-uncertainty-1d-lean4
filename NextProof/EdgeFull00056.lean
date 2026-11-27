import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00055

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00001011111111_0 : Blocks := edgeBlocks% "full/vectors/00001011111111-V-0000.bin"
noncomputable def vp00001011111111 : Blocks := vp00001011111111_0
theorem coverp00001011111111 : Covers (-383261639/500000 : ℚ) vp00001011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011111110_0 : Blocks := edgeBlocks% "full/vectors/00001011111110-V-0000.bin"
noncomputable def vp00001011111110 : Blocks := vp00001011111110_0
theorem coverp00001011111110 : Covers (-382761639/500000 : ℚ) vp00001011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000101111111-V-0000.bin"
noncomputable def vp0000101111111 : Blocks := vp0000101111111_0
private theorem bp00001011111110 : Branch 0 (-382761639/1000000 : ℚ) vp0000101111111 := by
  apply branch_left_normalized (c:=vp00001011111110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-382761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-382761639/500000 : ℚ) by norm_num]
  exact coverp00001011111110
private noncomputable def ep00001011111111_0 : Blocks := edgeBlocks% "full/vectors/00001011111111-E-0000.bin"
noncomputable def ep00001011111111 : Blocks := ep00001011111111_0
private theorem idp00001011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111111.list =
    C ((2:ℤ)^71) * horner X vp00001011111111.list + horner X ep00001011111111.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011111111 : Branch 1 (-382761639/1000000 : ℚ) vp0000101111111 := by
  apply branch_checked idp00001011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-382761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-383261639/500000 : ℚ) by norm_num]
  exact coverp00001011111111
theorem coverp0000101111111 : Covers (-382761639/1000000 : ℚ) vp0000101111111 := join_branches bp00001011111110 bp00001011111111
private noncomputable def vp00001011111101_0 : Blocks := edgeBlocks% "full/vectors/00001011111101-V-0000.bin"
noncomputable def vp00001011111101 : Blocks := vp00001011111101_0
theorem coverp00001011111101 : Covers (-382261639/500000 : ℚ) vp00001011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011111100_0 : Blocks := edgeBlocks% "full/vectors/00001011111100-V-0000.bin"
noncomputable def vp00001011111100 : Blocks := vp00001011111100_0
theorem coverp00001011111100 : Covers (-381761639/500000 : ℚ) vp00001011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111110_0 : Blocks := edgeBlocks% "full/vectors/0000101111110-V-0000.bin"
noncomputable def vp0000101111110 : Blocks := vp0000101111110_0
private theorem bp00001011111100 : Branch 0 (-381761639/1000000 : ℚ) vp0000101111110 := by
  apply branch_left_normalized (c:=vp00001011111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-381761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-381761639/500000 : ℚ) by norm_num]
  exact coverp00001011111100
private noncomputable def ep00001011111101_0 : Blocks := edgeBlocks% "full/vectors/00001011111101-E-0000.bin"
noncomputable def ep00001011111101 : Blocks := ep00001011111101_0
private theorem idp00001011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111110.list =
    C ((2:ℤ)^70) * horner X vp00001011111101.list + horner X ep00001011111101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011111101 : Branch 1 (-381761639/1000000 : ℚ) vp0000101111110 := by
  apply branch_checked idp00001011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-381761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-382261639/500000 : ℚ) by norm_num]
  exact coverp00001011111101
theorem coverp0000101111110 : Covers (-381761639/1000000 : ℚ) vp0000101111110 := join_branches bp00001011111100 bp00001011111101
private noncomputable def vp000010111111_0 : Blocks := edgeBlocks% "full/vectors/000010111111-V-0000.bin"
noncomputable def vp000010111111 : Blocks := vp000010111111_0
private theorem bp0000101111110 : Branch 0 (-381761639/2000000 : ℚ) vp000010111111 := by
  apply branch_left_normalized (c:=vp0000101111110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-381761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-381761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111110
private noncomputable def ep0000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000101111111-E-0000.bin"
noncomputable def ep0000101111111 : Blocks := ep0000101111111_0
private theorem idp0000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111111.list =
    C ((2:ℤ)^123) * horner X vp0000101111111.list + horner X ep0000101111111.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101111111 : Branch 1 (-381761639/2000000 : ℚ) vp000010111111 := by
  apply branch_checked idp0000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-381761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-382761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111111
theorem coverp000010111111 : Covers (-381761639/2000000 : ℚ) vp000010111111 := join_branches bp0000101111110 bp0000101111111
private noncomputable def vp00001011111011_0 : Blocks := edgeBlocks% "full/vectors/00001011111011-V-0000.bin"
noncomputable def vp00001011111011 : Blocks := vp00001011111011_0
theorem coverp00001011111011 : Covers (-381261639/500000 : ℚ) vp00001011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011111010_0 : Blocks := edgeBlocks% "full/vectors/00001011111010-V-0000.bin"
noncomputable def vp00001011111010 : Blocks := vp00001011111010_0
theorem coverp00001011111010 : Covers (-380761639/500000 : ℚ) vp00001011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111101_0 : Blocks := edgeBlocks% "full/vectors/0000101111101-V-0000.bin"
noncomputable def vp0000101111101 : Blocks := vp0000101111101_0
private theorem bp00001011111010 : Branch 0 (-380761639/1000000 : ℚ) vp0000101111101 := by
  apply branch_left_normalized (c:=vp00001011111010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-380761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-380761639/500000 : ℚ) by norm_num]
  exact coverp00001011111010
private noncomputable def ep00001011111011_0 : Blocks := edgeBlocks% "full/vectors/00001011111011-E-0000.bin"
noncomputable def ep00001011111011 : Blocks := ep00001011111011_0
private theorem idp00001011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111101.list =
    C ((2:ℤ)^70) * horner X vp00001011111011.list + horner X ep00001011111011.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011111011 : Branch 1 (-380761639/1000000 : ℚ) vp0000101111101 := by
  apply branch_checked idp00001011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-380761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-381261639/500000 : ℚ) by norm_num]
  exact coverp00001011111011
theorem coverp0000101111101 : Covers (-380761639/1000000 : ℚ) vp0000101111101 := join_branches bp00001011111010 bp00001011111011
private noncomputable def vp00001011111001_0 : Blocks := edgeBlocks% "full/vectors/00001011111001-V-0000.bin"
noncomputable def vp00001011111001 : Blocks := vp00001011111001_0
theorem coverp00001011111001 : Covers (-380261639/500000 : ℚ) vp00001011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011111000_0 : Blocks := edgeBlocks% "full/vectors/00001011111000-V-0000.bin"
noncomputable def vp00001011111000 : Blocks := vp00001011111000_0
theorem coverp00001011111000 : Covers (-379761639/500000 : ℚ) vp00001011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111100_0 : Blocks := edgeBlocks% "full/vectors/0000101111100-V-0000.bin"
noncomputable def vp0000101111100 : Blocks := vp0000101111100_0
private theorem bp00001011111000 : Branch 0 (-379761639/1000000 : ℚ) vp0000101111100 := by
  apply branch_left_normalized (c:=vp00001011111000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-379761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-379761639/500000 : ℚ) by norm_num]
  exact coverp00001011111000
private noncomputable def ep00001011111001_0 : Blocks := edgeBlocks% "full/vectors/00001011111001-E-0000.bin"
noncomputable def ep00001011111001 : Blocks := ep00001011111001_0
private theorem idp00001011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111100.list =
    C ((2:ℤ)^69) * horner X vp00001011111001.list + horner X ep00001011111001.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011111001 : Branch 1 (-379761639/1000000 : ℚ) vp0000101111100 := by
  apply branch_checked idp00001011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-379761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-380261639/500000 : ℚ) by norm_num]
  exact coverp00001011111001
theorem coverp0000101111100 : Covers (-379761639/1000000 : ℚ) vp0000101111100 := join_branches bp00001011111000 bp00001011111001
private noncomputable def vp000010111110_0 : Blocks := edgeBlocks% "full/vectors/000010111110-V-0000.bin"
noncomputable def vp000010111110 : Blocks := vp000010111110_0
private theorem bp0000101111100 : Branch 0 (-379761639/2000000 : ℚ) vp000010111110 := by
  apply branch_left_normalized (c:=vp0000101111100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-379761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-379761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111100
private noncomputable def ep0000101111101_0 : Blocks := edgeBlocks% "full/vectors/0000101111101-E-0000.bin"
noncomputable def ep0000101111101 : Blocks := ep0000101111101_0
private theorem idp0000101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111110.list =
    C ((2:ℤ)^122) * horner X vp0000101111101.list + horner X ep0000101111101.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101111101 : Branch 1 (-379761639/2000000 : ℚ) vp000010111110 := by
  apply branch_checked idp0000101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-379761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-380761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111101
theorem coverp000010111110 : Covers (-379761639/2000000 : ℚ) vp000010111110 := join_branches bp0000101111100 bp0000101111101
private noncomputable def vp00001011111_0 : Blocks := edgeBlocks% "full/vectors/00001011111-V-0000.bin"
private noncomputable def vp00001011111_1 : Blocks := edgeBlocks% "full/vectors/00001011111-V-0001.bin"
noncomputable def vp00001011111 : Blocks := (Blocks.join vp00001011111_0 vp00001011111_1)
private theorem bp000010111110 : Branch 0 (-379761639/4000000 : ℚ) vp00001011111 := by
  apply branch_left_normalized (c:=vp000010111110) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-379761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-379761639/2000000 : ℚ) by norm_num]
  exact coverp000010111110
private noncomputable def ep000010111111_0 : Blocks := edgeBlocks% "full/vectors/000010111111-E-0000.bin"
private noncomputable def ep000010111111_1 : Blocks := edgeBlocks% "full/vectors/000010111111-E-0001.bin"
noncomputable def ep000010111111 : Blocks := (Blocks.join ep000010111111_0 ep000010111111_1)
private theorem idp000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011111.list =
    C ((2:ℤ)^227) * horner X vp000010111111.list + horner X ep000010111111.list := by
  exact edge_identity (B := (2:ℤ)^419) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010111111 : Branch 1 (-379761639/4000000 : ℚ) vp00001011111 := by
  apply branch_checked idp000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-379761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-381761639/2000000 : ℚ) by norm_num]
  exact coverp000010111111
theorem coverp00001011111 : Covers (-379761639/4000000 : ℚ) vp00001011111 := join_branches bp000010111110 bp000010111111
private noncomputable def vp00001011110111_0 : Blocks := edgeBlocks% "full/vectors/00001011110111-V-0000.bin"
noncomputable def vp00001011110111 : Blocks := vp00001011110111_0
theorem coverp00001011110111 : Covers (-379261639/500000 : ℚ) vp00001011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011110110_0 : Blocks := edgeBlocks% "full/vectors/00001011110110-V-0000.bin"
noncomputable def vp00001011110110 : Blocks := vp00001011110110_0
theorem coverp00001011110110 : Covers (-378761639/500000 : ℚ) vp00001011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000101111011-V-0000.bin"
noncomputable def vp0000101111011 : Blocks := vp0000101111011_0
private theorem bp00001011110110 : Branch 0 (-378761639/1000000 : ℚ) vp0000101111011 := by
  apply branch_left_normalized (c:=vp00001011110110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-378761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-378761639/500000 : ℚ) by norm_num]
  exact coverp00001011110110
private noncomputable def ep00001011110111_0 : Blocks := edgeBlocks% "full/vectors/00001011110111-E-0000.bin"
noncomputable def ep00001011110111 : Blocks := ep00001011110111_0
private theorem idp00001011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111011.list =
    C ((2:ℤ)^69) * horner X vp00001011110111.list + horner X ep00001011110111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011110111 : Branch 1 (-378761639/1000000 : ℚ) vp0000101111011 := by
  apply branch_checked idp00001011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-378761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-379261639/500000 : ℚ) by norm_num]
  exact coverp00001011110111
theorem coverp0000101111011 : Covers (-378761639/1000000 : ℚ) vp0000101111011 := join_branches bp00001011110110 bp00001011110111
private noncomputable def vp00001011110101_0 : Blocks := edgeBlocks% "full/vectors/00001011110101-V-0000.bin"
noncomputable def vp00001011110101 : Blocks := vp00001011110101_0
theorem coverp00001011110101 : Covers (-378261639/500000 : ℚ) vp00001011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011110100_0 : Blocks := edgeBlocks% "full/vectors/00001011110100-V-0000.bin"
noncomputable def vp00001011110100 : Blocks := vp00001011110100_0
theorem coverp00001011110100 : Covers (-377761639/500000 : ℚ) vp00001011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111010_0 : Blocks := edgeBlocks% "full/vectors/0000101111010-V-0000.bin"
noncomputable def vp0000101111010 : Blocks := vp0000101111010_0
private theorem bp00001011110100 : Branch 0 (-377761639/1000000 : ℚ) vp0000101111010 := by
  apply branch_left_normalized (c:=vp00001011110100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-377761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-377761639/500000 : ℚ) by norm_num]
  exact coverp00001011110100
private noncomputable def ep00001011110101_0 : Blocks := edgeBlocks% "full/vectors/00001011110101-E-0000.bin"
noncomputable def ep00001011110101 : Blocks := ep00001011110101_0
private theorem idp00001011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111010.list =
    C ((2:ℤ)^68) * horner X vp00001011110101.list + horner X ep00001011110101.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011110101 : Branch 1 (-377761639/1000000 : ℚ) vp0000101111010 := by
  apply branch_checked idp00001011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-377761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-378261639/500000 : ℚ) by norm_num]
  exact coverp00001011110101
theorem coverp0000101111010 : Covers (-377761639/1000000 : ℚ) vp0000101111010 := join_branches bp00001011110100 bp00001011110101
private noncomputable def vp000010111101_0 : Blocks := edgeBlocks% "full/vectors/000010111101-V-0000.bin"
noncomputable def vp000010111101 : Blocks := vp000010111101_0
private theorem bp0000101111010 : Branch 0 (-377761639/2000000 : ℚ) vp000010111101 := by
  apply branch_left_normalized (c:=vp0000101111010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-377761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-377761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111010
private noncomputable def ep0000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000101111011-E-0000.bin"
noncomputable def ep0000101111011 : Blocks := ep0000101111011_0
private theorem idp0000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111101.list =
    C ((2:ℤ)^123) * horner X vp0000101111011.list + horner X ep0000101111011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101111011 : Branch 1 (-377761639/2000000 : ℚ) vp000010111101 := by
  apply branch_checked idp0000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-377761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-378761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111011
theorem coverp000010111101 : Covers (-377761639/2000000 : ℚ) vp000010111101 := join_branches bp0000101111010 bp0000101111011
private noncomputable def vp0000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000101111001-V-0000.bin"
noncomputable def vp0000101111001 : Blocks := vp0000101111001_0
theorem coverp0000101111001 : Covers (-376761639/1000000 : ℚ) vp0000101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101111000_0 : Blocks := edgeBlocks% "full/vectors/0000101111000-V-0000.bin"
noncomputable def vp0000101111000 : Blocks := vp0000101111000_0
theorem coverp0000101111000 : Covers (-375761639/1000000 : ℚ) vp0000101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000010111100_0 : Blocks := edgeBlocks% "full/vectors/000010111100-V-0000.bin"
noncomputable def vp000010111100 : Blocks := vp000010111100_0
private theorem bp0000101111000 : Branch 0 (-375761639/2000000 : ℚ) vp000010111100 := by
  apply branch_left_normalized (c:=vp0000101111000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-375761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-375761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111000
private noncomputable def ep0000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000101111001-E-0000.bin"
noncomputable def ep0000101111001 : Blocks := ep0000101111001_0
private theorem idp0000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111100.list =
    C ((2:ℤ)^124) * horner X vp0000101111001.list + horner X ep0000101111001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101111001 : Branch 1 (-375761639/2000000 : ℚ) vp000010111100 := by
  apply branch_checked idp0000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-375761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-376761639/1000000 : ℚ) by norm_num]
  exact coverp0000101111001
theorem coverp000010111100 : Covers (-375761639/2000000 : ℚ) vp000010111100 := join_branches bp0000101111000 bp0000101111001
private noncomputable def vp00001011110_0 : Blocks := edgeBlocks% "full/vectors/00001011110-V-0000.bin"
private noncomputable def vp00001011110_1 : Blocks := edgeBlocks% "full/vectors/00001011110-V-0001.bin"
noncomputable def vp00001011110 : Blocks := (Blocks.join vp00001011110_0 vp00001011110_1)
private theorem bp000010111100 : Branch 0 (-375761639/4000000 : ℚ) vp00001011110 := by
  apply branch_left_normalized (c:=vp000010111100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-375761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-375761639/2000000 : ℚ) by norm_num]
  exact coverp000010111100
private noncomputable def ep000010111101_0 : Blocks := edgeBlocks% "full/vectors/000010111101-E-0000.bin"
private noncomputable def ep000010111101_1 : Blocks := edgeBlocks% "full/vectors/000010111101-E-0001.bin"
noncomputable def ep000010111101 : Blocks := (Blocks.join ep000010111101_0 ep000010111101_1)
private theorem idp000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011110.list =
    C ((2:ℤ)^230) * horner X vp000010111101.list + horner X ep000010111101.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010111101 : Branch 1 (-375761639/4000000 : ℚ) vp00001011110 := by
  apply branch_checked idp000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-375761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-377761639/2000000 : ℚ) by norm_num]
  exact coverp000010111101
theorem coverp00001011110 : Covers (-375761639/4000000 : ℚ) vp00001011110 := join_branches bp000010111100 bp000010111101
private noncomputable def vp0000101111_0 : Blocks := edgeBlocks% "full/vectors/0000101111-V-0000.bin"
private noncomputable def vp0000101111_1 : Blocks := edgeBlocks% "full/vectors/0000101111-V-0001.bin"
private noncomputable def vp0000101111_2 : Blocks := edgeBlocks% "full/vectors/0000101111-V-0002.bin"
private noncomputable def vp0000101111_3 : Blocks := edgeBlocks% "full/vectors/0000101111-V-0003.bin"
noncomputable def vp0000101111 : Blocks := (Blocks.join (Blocks.join vp0000101111_0 vp0000101111_1) (Blocks.join vp0000101111_2 vp0000101111_3))
private theorem bp00001011110 : Branch 0 (-375761639/8000000 : ℚ) vp0000101111 := by
  apply branch_left_normalized (c:=vp00001011110) (k:=0) (m:=218) (by decide +kernel)
  rw [show 2*(-375761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-375761639/4000000 : ℚ) by norm_num]
  exact coverp00001011110
private noncomputable def ep00001011111_0 : Blocks := edgeBlocks% "full/vectors/00001011111-E-0000.bin"
private noncomputable def ep00001011111_1 : Blocks := edgeBlocks% "full/vectors/00001011111-E-0001.bin"
private noncomputable def ep00001011111_2 : Blocks := edgeBlocks% "full/vectors/00001011111-E-0002.bin"
private noncomputable def ep00001011111_3 : Blocks := edgeBlocks% "full/vectors/00001011111-E-0003.bin"
noncomputable def ep00001011111 : Blocks := (Blocks.join (Blocks.join ep00001011111_0 ep00001011111_1) (Blocks.join ep00001011111_2 ep00001011111_3))
private theorem idp00001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101111.list =
    C ((2:ℤ)^441) * horner X vp00001011111.list + horner X ep00001011111.list := by
  exact edge_identity (B := (2:ℤ)^726) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011111 : Branch 1 (-375761639/8000000 : ℚ) vp0000101111 := by
  apply branch_checked idp00001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-375761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-379761639/4000000 : ℚ) by norm_num]
  exact coverp00001011111
theorem coverp0000101111 : Covers (-375761639/8000000 : ℚ) vp0000101111 := join_branches bp00001011110 bp00001011111
private noncomputable def vp0000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000101110111-V-0000.bin"
noncomputable def vp0000101110111 : Blocks := vp0000101110111_0
theorem coverp0000101110111 : Covers (-374761639/1000000 : ℚ) vp0000101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101110110_0 : Blocks := edgeBlocks% "full/vectors/0000101110110-V-0000.bin"
noncomputable def vp0000101110110 : Blocks := vp0000101110110_0
theorem coverp0000101110110 : Covers (-373761639/1000000 : ℚ) vp0000101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000010111011_0 : Blocks := edgeBlocks% "full/vectors/000010111011-V-0000.bin"
noncomputable def vp000010111011 : Blocks := vp000010111011_0
private theorem bp0000101110110 : Branch 0 (-373761639/2000000 : ℚ) vp000010111011 := by
  apply branch_left_normalized (c:=vp0000101110110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-373761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-373761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110110
private noncomputable def ep0000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000101110111-E-0000.bin"
noncomputable def ep0000101110111 : Blocks := ep0000101110111_0
private theorem idp0000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111011.list =
    C ((2:ℤ)^123) * horner X vp0000101110111.list + horner X ep0000101110111.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101110111 : Branch 1 (-373761639/2000000 : ℚ) vp000010111011 := by
  apply branch_checked idp0000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-373761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-374761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110111
theorem coverp000010111011 : Covers (-373761639/2000000 : ℚ) vp000010111011 := join_branches bp0000101110110 bp0000101110111
private noncomputable def vp0000101110101_0 : Blocks := edgeBlocks% "full/vectors/0000101110101-V-0000.bin"
noncomputable def vp0000101110101 : Blocks := vp0000101110101_0
theorem coverp0000101110101 : Covers (-372761639/1000000 : ℚ) vp0000101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101110100_0 : Blocks := edgeBlocks% "full/vectors/0000101110100-V-0000.bin"
noncomputable def vp0000101110100 : Blocks := vp0000101110100_0
theorem coverp0000101110100 : Covers (-371761639/1000000 : ℚ) vp0000101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000010111010_0 : Blocks := edgeBlocks% "full/vectors/000010111010-V-0000.bin"
noncomputable def vp000010111010 : Blocks := vp000010111010_0
private theorem bp0000101110100 : Branch 0 (-371761639/2000000 : ℚ) vp000010111010 := by
  apply branch_left_normalized (c:=vp0000101110100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-371761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-371761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110100
private noncomputable def ep0000101110101_0 : Blocks := edgeBlocks% "full/vectors/0000101110101-E-0000.bin"
noncomputable def ep0000101110101 : Blocks := ep0000101110101_0
private theorem idp0000101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111010.list =
    C ((2:ℤ)^124) * horner X vp0000101110101.list + horner X ep0000101110101.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101110101 : Branch 1 (-371761639/2000000 : ℚ) vp000010111010 := by
  apply branch_checked idp0000101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-371761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-372761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110101
theorem coverp000010111010 : Covers (-371761639/2000000 : ℚ) vp000010111010 := join_branches bp0000101110100 bp0000101110101
private noncomputable def vp00001011101_0 : Blocks := edgeBlocks% "full/vectors/00001011101-V-0000.bin"
private noncomputable def vp00001011101_1 : Blocks := edgeBlocks% "full/vectors/00001011101-V-0001.bin"
noncomputable def vp00001011101 : Blocks := (Blocks.join vp00001011101_0 vp00001011101_1)
private theorem bp000010111010 : Branch 0 (-371761639/4000000 : ℚ) vp00001011101 := by
  apply branch_left_normalized (c:=vp000010111010) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-371761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-371761639/2000000 : ℚ) by norm_num]
  exact coverp000010111010
private noncomputable def ep000010111011_0 : Blocks := edgeBlocks% "full/vectors/000010111011-E-0000.bin"
private noncomputable def ep000010111011_1 : Blocks := edgeBlocks% "full/vectors/000010111011-E-0001.bin"
noncomputable def ep000010111011 : Blocks := (Blocks.join ep000010111011_0 ep000010111011_1)
private theorem idp000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011101.list =
    C ((2:ℤ)^231) * horner X vp000010111011.list + horner X ep000010111011.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010111011 : Branch 1 (-371761639/4000000 : ℚ) vp00001011101 := by
  apply branch_checked idp000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-371761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-373761639/2000000 : ℚ) by norm_num]
  exact coverp000010111011
theorem coverp00001011101 : Covers (-371761639/4000000 : ℚ) vp00001011101 := join_branches bp000010111010 bp000010111011
private noncomputable def vp0000101110011_0 : Blocks := edgeBlocks% "full/vectors/0000101110011-V-0000.bin"
noncomputable def vp0000101110011 : Blocks := vp0000101110011_0
theorem coverp0000101110011 : Covers (-370761639/1000000 : ℚ) vp0000101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101110010_0 : Blocks := edgeBlocks% "full/vectors/0000101110010-V-0000.bin"
noncomputable def vp0000101110010 : Blocks := vp0000101110010_0
theorem coverp0000101110010 : Covers (-369761639/1000000 : ℚ) vp0000101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000010111001_0 : Blocks := edgeBlocks% "full/vectors/000010111001-V-0000.bin"
noncomputable def vp000010111001 : Blocks := vp000010111001_0
private theorem bp0000101110010 : Branch 0 (-369761639/2000000 : ℚ) vp000010111001 := by
  apply branch_left_normalized (c:=vp0000101110010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-369761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-369761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110010
private noncomputable def ep0000101110011_0 : Blocks := edgeBlocks% "full/vectors/0000101110011-E-0000.bin"
noncomputable def ep0000101110011 : Blocks := ep0000101110011_0
private theorem idp0000101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111001.list =
    C ((2:ℤ)^124) * horner X vp0000101110011.list + horner X ep0000101110011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101110011 : Branch 1 (-369761639/2000000 : ℚ) vp000010111001 := by
  apply branch_checked idp0000101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-369761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-370761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110011
theorem coverp000010111001 : Covers (-369761639/2000000 : ℚ) vp000010111001 := join_branches bp0000101110010 bp0000101110011
private noncomputable def vp0000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000101110001-V-0000.bin"
noncomputable def vp0000101110001 : Blocks := vp0000101110001_0
theorem coverp0000101110001 : Covers (-368761639/1000000 : ℚ) vp0000101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101110000_0 : Blocks := edgeBlocks% "full/vectors/0000101110000-V-0000.bin"
noncomputable def vp0000101110000 : Blocks := vp0000101110000_0
theorem coverp0000101110000 : Covers (-367761639/1000000 : ℚ) vp0000101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000010111000_0 : Blocks := edgeBlocks% "full/vectors/000010111000-V-0000.bin"
noncomputable def vp000010111000 : Blocks := vp000010111000_0
private theorem bp0000101110000 : Branch 0 (-367761639/2000000 : ℚ) vp000010111000 := by
  apply branch_left_normalized (c:=vp0000101110000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-367761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-367761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110000
private noncomputable def ep0000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000101110001-E-0000.bin"
noncomputable def ep0000101110001 : Blocks := ep0000101110001_0
private theorem idp0000101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111000.list =
    C ((2:ℤ)^125) * horner X vp0000101110001.list + horner X ep0000101110001.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101110001 : Branch 1 (-367761639/2000000 : ℚ) vp000010111000 := by
  apply branch_checked idp0000101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-367761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-368761639/1000000 : ℚ) by norm_num]
  exact coverp0000101110001
theorem coverp000010111000 : Covers (-367761639/2000000 : ℚ) vp000010111000 := join_branches bp0000101110000 bp0000101110001
private noncomputable def vp00001011100_0 : Blocks := edgeBlocks% "full/vectors/00001011100-V-0000.bin"
private noncomputable def vp00001011100_1 : Blocks := edgeBlocks% "full/vectors/00001011100-V-0001.bin"
noncomputable def vp00001011100 : Blocks := (Blocks.join vp00001011100_0 vp00001011100_1)
private theorem bp000010111000 : Branch 0 (-367761639/4000000 : ℚ) vp00001011100 := by
  apply branch_left_normalized (c:=vp000010111000) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-367761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-367761639/2000000 : ℚ) by norm_num]
  exact coverp000010111000
private noncomputable def ep000010111001_0 : Blocks := edgeBlocks% "full/vectors/000010111001-E-0000.bin"
private noncomputable def ep000010111001_1 : Blocks := edgeBlocks% "full/vectors/000010111001-E-0001.bin"
noncomputable def ep000010111001 : Blocks := (Blocks.join ep000010111001_0 ep000010111001_1)
private theorem idp000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011100.list =
    C ((2:ℤ)^233) * horner X vp000010111001.list + horner X ep000010111001.list := by
  exact edge_identity (B := (2:ℤ)^420) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010111001 : Branch 1 (-367761639/4000000 : ℚ) vp00001011100 := by
  apply branch_checked idp000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-367761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-369761639/2000000 : ℚ) by norm_num]
  exact coverp000010111001
theorem coverp00001011100 : Covers (-367761639/4000000 : ℚ) vp00001011100 := join_branches bp000010111000 bp000010111001
private noncomputable def vp0000101110_0 : Blocks := edgeBlocks% "full/vectors/0000101110-V-0000.bin"
private noncomputable def vp0000101110_1 : Blocks := edgeBlocks% "full/vectors/0000101110-V-0001.bin"
private noncomputable def vp0000101110_2 : Blocks := edgeBlocks% "full/vectors/0000101110-V-0002.bin"
private noncomputable def vp0000101110_3 : Blocks := edgeBlocks% "full/vectors/0000101110-V-0003.bin"
noncomputable def vp0000101110 : Blocks := (Blocks.join (Blocks.join vp0000101110_0 vp0000101110_1) (Blocks.join vp0000101110_2 vp0000101110_3))
private theorem bp00001011100 : Branch 0 (-367761639/8000000 : ℚ) vp0000101110 := by
  apply branch_left_normalized (c:=vp00001011100) (k:=0) (m:=220) (by decide +kernel)
  rw [show 2*(-367761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-367761639/4000000 : ℚ) by norm_num]
  exact coverp00001011100
private noncomputable def ep00001011101_0 : Blocks := edgeBlocks% "full/vectors/00001011101-E-0000.bin"
private noncomputable def ep00001011101_1 : Blocks := edgeBlocks% "full/vectors/00001011101-E-0001.bin"
private noncomputable def ep00001011101_2 : Blocks := edgeBlocks% "full/vectors/00001011101-E-0002.bin"
private noncomputable def ep00001011101_3 : Blocks := edgeBlocks% "full/vectors/00001011101-E-0003.bin"
noncomputable def ep00001011101 : Blocks := (Blocks.join (Blocks.join ep00001011101_0 ep00001011101_1) (Blocks.join ep00001011101_2 ep00001011101_3))
private theorem idp00001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101110.list =
    C ((2:ℤ)^448) * horner X vp00001011101.list + horner X ep00001011101.list := by
  exact edge_identity (B := (2:ℤ)^732) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011101 : Branch 1 (-367761639/8000000 : ℚ) vp0000101110 := by
  apply branch_checked idp00001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-367761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-371761639/4000000 : ℚ) by norm_num]
  exact coverp00001011101
theorem coverp0000101110 : Covers (-367761639/8000000 : ℚ) vp0000101110 := join_branches bp00001011100 bp00001011101
private noncomputable def vp000010111_0 : Blocks := edgeBlocks% "full/vectors/000010111-V-0000.bin"
private noncomputable def vp000010111_1 : Blocks := edgeBlocks% "full/vectors/000010111-V-0001.bin"
private noncomputable def vp000010111_2 : Blocks := edgeBlocks% "full/vectors/000010111-V-0002.bin"
private noncomputable def vp000010111_3 : Blocks := edgeBlocks% "full/vectors/000010111-V-0003.bin"
private noncomputable def vp000010111_4 : Blocks := edgeBlocks% "full/vectors/000010111-V-0004.bin"
private noncomputable def vp000010111_5 : Blocks := edgeBlocks% "full/vectors/000010111-V-0005.bin"
private noncomputable def vp000010111_6 : Blocks := edgeBlocks% "full/vectors/000010111-V-0006.bin"
noncomputable def vp000010111 : Blocks := (Blocks.join (Blocks.join vp000010111_0 (Blocks.join vp000010111_1 vp000010111_2)) (Blocks.join (Blocks.join vp000010111_3 vp000010111_4) (Blocks.join vp000010111_5 vp000010111_6)))
private theorem bp0000101110 : Branch 0 (-367761639/16000000 : ℚ) vp000010111 := by
  apply branch_left_normalized (c:=vp0000101110) (k:=0) (m:=423) (by decide +kernel)
  rw [show 2*(-367761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-367761639/8000000 : ℚ) by norm_num]
  exact coverp0000101110
private noncomputable def ep0000101111_0 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0000.bin"
private noncomputable def ep0000101111_1 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0001.bin"
private noncomputable def ep0000101111_2 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0002.bin"
private noncomputable def ep0000101111_3 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0003.bin"
private noncomputable def ep0000101111_4 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0004.bin"
private noncomputable def ep0000101111_5 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0005.bin"
private noncomputable def ep0000101111_6 : Blocks := edgeBlocks% "full/vectors/0000101111-E-0006.bin"
noncomputable def ep0000101111 : Blocks := (Blocks.join (Blocks.join ep0000101111_0 (Blocks.join ep0000101111_1 ep0000101111_2)) (Blocks.join (Blocks.join ep0000101111_3 ep0000101111_4) (Blocks.join ep0000101111_5 ep0000101111_6)))
private theorem idp0000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010111.list =
    C ((2:ℤ)^873) * horner X vp0000101111.list + horner X ep0000101111.list := by
  exact edge_identity (B := (2:ℤ)^1351) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101111 : Branch 1 (-367761639/16000000 : ℚ) vp000010111 := by
  apply branch_checked idp0000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-367761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-375761639/8000000 : ℚ) by norm_num]
  exact coverp0000101111
theorem coverp000010111 : Covers (-367761639/16000000 : ℚ) vp000010111 := join_branches bp0000101110 bp0000101111
private noncomputable def vp0000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000101101111-V-0000.bin"
noncomputable def vp0000101101111 : Blocks := vp0000101101111_0
theorem coverp0000101101111 : Covers (-366761639/1000000 : ℚ) vp0000101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101110_0 : Blocks := edgeBlocks% "full/vectors/0000101101110-V-0000.bin"
noncomputable def vp0000101101110 : Blocks := vp0000101101110_0
theorem coverp0000101101110 : Covers (-365761639/1000000 : ℚ) vp0000101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000010110111_0 : Blocks := edgeBlocks% "full/vectors/000010110111-V-0000.bin"
noncomputable def vp000010110111 : Blocks := vp000010110111_0
private theorem bp0000101101110 : Branch 0 (-365761639/2000000 : ℚ) vp000010110111 := by
  apply branch_left_normalized (c:=vp0000101101110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-365761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-365761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101110
private noncomputable def ep0000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000101101111-E-0000.bin"
noncomputable def ep0000101101111 : Blocks := ep0000101101111_0
private theorem idp0000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110111.list =
    C ((2:ℤ)^125) * horner X vp0000101101111.list + horner X ep0000101101111.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101101111 : Branch 1 (-365761639/2000000 : ℚ) vp000010110111 := by
  apply branch_checked idp0000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-365761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-366761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101111
theorem coverp000010110111 : Covers (-365761639/2000000 : ℚ) vp000010110111 := join_branches bp0000101101110 bp0000101101111
private noncomputable def vp0000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000101101101-V-0000.bin"
noncomputable def vp0000101101101 : Blocks := vp0000101101101_0
theorem coverp0000101101101 : Covers (-364761639/1000000 : ℚ) vp0000101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101100_0 : Blocks := edgeBlocks% "full/vectors/0000101101100-V-0000.bin"
noncomputable def vp0000101101100 : Blocks := vp0000101101100_0
theorem coverp0000101101100 : Covers (-363761639/1000000 : ℚ) vp0000101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000010110110_0 : Blocks := edgeBlocks% "full/vectors/000010110110-V-0000.bin"
noncomputable def vp000010110110 : Blocks := vp000010110110_0
private theorem bp0000101101100 : Branch 0 (-363761639/2000000 : ℚ) vp000010110110 := by
  apply branch_left_normalized (c:=vp0000101101100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-363761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-363761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101100
private noncomputable def ep0000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000101101101-E-0000.bin"
noncomputable def ep0000101101101 : Blocks := ep0000101101101_0
private theorem idp0000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110110.list =
    C ((2:ℤ)^127) * horner X vp0000101101101.list + horner X ep0000101101101.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101101101 : Branch 1 (-363761639/2000000 : ℚ) vp000010110110 := by
  apply branch_checked idp0000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-363761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-364761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101101
theorem coverp000010110110 : Covers (-363761639/2000000 : ℚ) vp000010110110 := join_branches bp0000101101100 bp0000101101101
private noncomputable def vp00001011011_0 : Blocks := edgeBlocks% "full/vectors/00001011011-V-0000.bin"
private noncomputable def vp00001011011_1 : Blocks := edgeBlocks% "full/vectors/00001011011-V-0001.bin"
noncomputable def vp00001011011 : Blocks := (Blocks.join vp00001011011_0 vp00001011011_1)
private theorem bp000010110110 : Branch 0 (-363761639/4000000 : ℚ) vp00001011011 := by
  apply branch_left_normalized (c:=vp000010110110) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-363761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-363761639/2000000 : ℚ) by norm_num]
  exact coverp000010110110
private noncomputable def ep000010110111_0 : Blocks := edgeBlocks% "full/vectors/000010110111-E-0000.bin"
private noncomputable def ep000010110111_1 : Blocks := edgeBlocks% "full/vectors/000010110111-E-0001.bin"
noncomputable def ep000010110111 : Blocks := (Blocks.join ep000010110111_0 ep000010110111_1)
private theorem idp000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011011.list =
    C ((2:ℤ)^236) * horner X vp000010110111.list + horner X ep000010110111.list := by
  exact edge_identity (B := (2:ℤ)^425) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110111 : Branch 1 (-363761639/4000000 : ℚ) vp00001011011 := by
  apply branch_checked idp000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-363761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-365761639/2000000 : ℚ) by norm_num]
  exact coverp000010110111
theorem coverp00001011011 : Covers (-363761639/4000000 : ℚ) vp00001011011 := join_branches bp000010110110 bp000010110111
private noncomputable def vp00001011010111_0 : Blocks := edgeBlocks% "full/vectors/00001011010111-V-0000.bin"
noncomputable def vp00001011010111 : Blocks := vp00001011010111_0
theorem coverp00001011010111 : Covers (-363261639/500000 : ℚ) vp00001011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011010110_0 : Blocks := edgeBlocks% "full/vectors/00001011010110-V-0000.bin"
noncomputable def vp00001011010110 : Blocks := vp00001011010110_0
theorem coverp00001011010110 : Covers (-362761639/500000 : ℚ) vp00001011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101011_0 : Blocks := edgeBlocks% "full/vectors/0000101101011-V-0000.bin"
noncomputable def vp0000101101011 : Blocks := vp0000101101011_0
private theorem bp00001011010110 : Branch 0 (-362761639/1000000 : ℚ) vp0000101101011 := by
  apply branch_left_normalized (c:=vp00001011010110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-362761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-362761639/500000 : ℚ) by norm_num]
  exact coverp00001011010110
private noncomputable def ep00001011010111_0 : Blocks := edgeBlocks% "full/vectors/00001011010111-E-0000.bin"
noncomputable def ep00001011010111 : Blocks := ep00001011010111_0
private theorem idp00001011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101101011.list =
    C ((2:ℤ)^72) * horner X vp00001011010111.list + horner X ep00001011010111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011010111 : Branch 1 (-362761639/1000000 : ℚ) vp0000101101011 := by
  apply branch_checked idp00001011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-362761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-363261639/500000 : ℚ) by norm_num]
  exact coverp00001011010111
theorem coverp0000101101011 : Covers (-362761639/1000000 : ℚ) vp0000101101011 := join_branches bp00001011010110 bp00001011010111
private noncomputable def vp00001011010101_0 : Blocks := edgeBlocks% "full/vectors/00001011010101-V-0000.bin"
noncomputable def vp00001011010101 : Blocks := vp00001011010101_0
theorem coverp00001011010101 : Covers (-362261639/500000 : ℚ) vp00001011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011010100_0 : Blocks := edgeBlocks% "full/vectors/00001011010100-V-0000.bin"
noncomputable def vp00001011010100 : Blocks := vp00001011010100_0
theorem coverp00001011010100 : Covers (-361761639/500000 : ℚ) vp00001011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101010_0 : Blocks := edgeBlocks% "full/vectors/0000101101010-V-0000.bin"
noncomputable def vp0000101101010 : Blocks := vp0000101101010_0
private theorem bp00001011010100 : Branch 0 (-361761639/1000000 : ℚ) vp0000101101010 := by
  apply branch_left_normalized (c:=vp00001011010100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-361761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-361761639/500000 : ℚ) by norm_num]
  exact coverp00001011010100
private noncomputable def ep00001011010101_0 : Blocks := edgeBlocks% "full/vectors/00001011010101-E-0000.bin"
noncomputable def ep00001011010101 : Blocks := ep00001011010101_0
private theorem idp00001011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101101010.list =
    C ((2:ℤ)^73) * horner X vp00001011010101.list + horner X ep00001011010101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011010101 : Branch 1 (-361761639/1000000 : ℚ) vp0000101101010 := by
  apply branch_checked idp00001011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-361761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-362261639/500000 : ℚ) by norm_num]
  exact coverp00001011010101
theorem coverp0000101101010 : Covers (-361761639/1000000 : ℚ) vp0000101101010 := join_branches bp00001011010100 bp00001011010101
private noncomputable def vp000010110101_0 : Blocks := edgeBlocks% "full/vectors/000010110101-V-0000.bin"
noncomputable def vp000010110101 : Blocks := vp000010110101_0
private theorem bp0000101101010 : Branch 0 (-361761639/2000000 : ℚ) vp000010110101 := by
  apply branch_left_normalized (c:=vp0000101101010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-361761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-361761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101010
private noncomputable def ep0000101101011_0 : Blocks := edgeBlocks% "full/vectors/0000101101011-E-0000.bin"
noncomputable def ep0000101101011 : Blocks := ep0000101101011_0
private theorem idp0000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110101.list =
    C ((2:ℤ)^129) * horner X vp0000101101011.list + horner X ep0000101101011.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101101011 : Branch 1 (-361761639/2000000 : ℚ) vp000010110101 := by
  apply branch_checked idp0000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-361761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-362761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101011
theorem coverp000010110101 : Covers (-361761639/2000000 : ℚ) vp000010110101 := join_branches bp0000101101010 bp0000101101011
private noncomputable def vp00001011010011_0 : Blocks := edgeBlocks% "full/vectors/00001011010011-V-0000.bin"
noncomputable def vp00001011010011 : Blocks := vp00001011010011_0
theorem coverp00001011010011 : Covers (-361261639/500000 : ℚ) vp00001011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011010010_0 : Blocks := edgeBlocks% "full/vectors/00001011010010-V-0000.bin"
noncomputable def vp00001011010010 : Blocks := vp00001011010010_0
theorem coverp00001011010010 : Covers (-360761639/500000 : ℚ) vp00001011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101001_0 : Blocks := edgeBlocks% "full/vectors/0000101101001-V-0000.bin"
noncomputable def vp0000101101001 : Blocks := vp0000101101001_0
private theorem bp00001011010010 : Branch 0 (-360761639/1000000 : ℚ) vp0000101101001 := by
  apply branch_left_normalized (c:=vp00001011010010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-360761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-360761639/500000 : ℚ) by norm_num]
  exact coverp00001011010010
private noncomputable def ep00001011010011_0 : Blocks := edgeBlocks% "full/vectors/00001011010011-E-0000.bin"
noncomputable def ep00001011010011 : Blocks := ep00001011010011_0
private theorem idp00001011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101101001.list =
    C ((2:ℤ)^74) * horner X vp00001011010011.list + horner X ep00001011010011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011010011 : Branch 1 (-360761639/1000000 : ℚ) vp0000101101001 := by
  apply branch_checked idp00001011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-360761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-361261639/500000 : ℚ) by norm_num]
  exact coverp00001011010011
theorem coverp0000101101001 : Covers (-360761639/1000000 : ℚ) vp0000101101001 := join_branches bp00001011010010 bp00001011010011
private noncomputable def vp00001011010001_0 : Blocks := edgeBlocks% "full/vectors/00001011010001-V-0000.bin"
noncomputable def vp00001011010001 : Blocks := vp00001011010001_0
theorem coverp00001011010001 : Covers (-360261639/500000 : ℚ) vp00001011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011010000_0 : Blocks := edgeBlocks% "full/vectors/00001011010000-V-0000.bin"
noncomputable def vp00001011010000 : Blocks := vp00001011010000_0
theorem coverp00001011010000 : Covers (-359761639/500000 : ℚ) vp00001011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101101000_0 : Blocks := edgeBlocks% "full/vectors/0000101101000-V-0000.bin"
noncomputable def vp0000101101000 : Blocks := vp0000101101000_0
private theorem bp00001011010000 : Branch 0 (-359761639/1000000 : ℚ) vp0000101101000 := by
  apply branch_left_normalized (c:=vp00001011010000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-359761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-359761639/500000 : ℚ) by norm_num]
  exact coverp00001011010000
private noncomputable def ep00001011010001_0 : Blocks := edgeBlocks% "full/vectors/00001011010001-E-0000.bin"
noncomputable def ep00001011010001 : Blocks := ep00001011010001_0
private theorem idp00001011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101101000.list =
    C ((2:ℤ)^75) * horner X vp00001011010001.list + horner X ep00001011010001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011010001 : Branch 1 (-359761639/1000000 : ℚ) vp0000101101000 := by
  apply branch_checked idp00001011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-359761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-360261639/500000 : ℚ) by norm_num]
  exact coverp00001011010001
theorem coverp0000101101000 : Covers (-359761639/1000000 : ℚ) vp0000101101000 := join_branches bp00001011010000 bp00001011010001
private noncomputable def vp000010110100_0 : Blocks := edgeBlocks% "full/vectors/000010110100-V-0000.bin"
noncomputable def vp000010110100 : Blocks := vp000010110100_0
private theorem bp0000101101000 : Branch 0 (-359761639/2000000 : ℚ) vp000010110100 := by
  apply branch_left_normalized (c:=vp0000101101000) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-359761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-359761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101000
private noncomputable def ep0000101101001_0 : Blocks := edgeBlocks% "full/vectors/0000101101001-E-0000.bin"
noncomputable def ep0000101101001 : Blocks := ep0000101101001_0
private theorem idp0000101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110100.list =
    C ((2:ℤ)^130) * horner X vp0000101101001.list + horner X ep0000101101001.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101101001 : Branch 1 (-359761639/2000000 : ℚ) vp000010110100 := by
  apply branch_checked idp0000101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-359761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-360761639/1000000 : ℚ) by norm_num]
  exact coverp0000101101001
theorem coverp000010110100 : Covers (-359761639/2000000 : ℚ) vp000010110100 := join_branches bp0000101101000 bp0000101101001
private noncomputable def vp00001011010_0 : Blocks := edgeBlocks% "full/vectors/00001011010-V-0000.bin"
private noncomputable def vp00001011010_1 : Blocks := edgeBlocks% "full/vectors/00001011010-V-0001.bin"
noncomputable def vp00001011010 : Blocks := (Blocks.join vp00001011010_0 vp00001011010_1)
private theorem bp000010110100 : Branch 0 (-359761639/4000000 : ℚ) vp00001011010 := by
  apply branch_left_normalized (c:=vp000010110100) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-359761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-359761639/2000000 : ℚ) by norm_num]
  exact coverp000010110100
private noncomputable def ep000010110101_0 : Blocks := edgeBlocks% "full/vectors/000010110101-E-0000.bin"
private noncomputable def ep000010110101_1 : Blocks := edgeBlocks% "full/vectors/000010110101-E-0001.bin"
noncomputable def ep000010110101 : Blocks := (Blocks.join ep000010110101_0 ep000010110101_1)
private theorem idp000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011010.list =
    C ((2:ℤ)^241) * horner X vp000010110101.list + horner X ep000010110101.list := by
  exact edge_identity (B := (2:ℤ)^434) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110101 : Branch 1 (-359761639/4000000 : ℚ) vp00001011010 := by
  apply branch_checked idp000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-359761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-361761639/2000000 : ℚ) by norm_num]
  exact coverp000010110101
theorem coverp00001011010 : Covers (-359761639/4000000 : ℚ) vp00001011010 := join_branches bp000010110100 bp000010110101
private noncomputable def vp0000101101_0 : Blocks := edgeBlocks% "full/vectors/0000101101-V-0000.bin"
private noncomputable def vp0000101101_1 : Blocks := edgeBlocks% "full/vectors/0000101101-V-0001.bin"
private noncomputable def vp0000101101_2 : Blocks := edgeBlocks% "full/vectors/0000101101-V-0002.bin"
private noncomputable def vp0000101101_3 : Blocks := edgeBlocks% "full/vectors/0000101101-V-0003.bin"
noncomputable def vp0000101101 : Blocks := (Blocks.join (Blocks.join vp0000101101_0 vp0000101101_1) (Blocks.join vp0000101101_2 vp0000101101_3))
private theorem bp00001011010 : Branch 0 (-359761639/8000000 : ℚ) vp0000101101 := by
  apply branch_left_normalized (c:=vp00001011010) (k:=0) (m:=226) (by decide +kernel)
  rw [show 2*(-359761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-359761639/4000000 : ℚ) by norm_num]
  exact coverp00001011010
private noncomputable def ep00001011011_0 : Blocks := edgeBlocks% "full/vectors/00001011011-E-0000.bin"
private noncomputable def ep00001011011_1 : Blocks := edgeBlocks% "full/vectors/00001011011-E-0001.bin"
private noncomputable def ep00001011011_2 : Blocks := edgeBlocks% "full/vectors/00001011011-E-0002.bin"
private noncomputable def ep00001011011_3 : Blocks := edgeBlocks% "full/vectors/00001011011-E-0003.bin"
noncomputable def ep00001011011 : Blocks := (Blocks.join (Blocks.join ep00001011011_0 ep00001011011_1) (Blocks.join ep00001011011_2 ep00001011011_3))
private theorem idp00001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101101.list =
    C ((2:ℤ)^459) * horner X vp00001011011.list + horner X ep00001011011.list := by
  exact edge_identity (B := (2:ℤ)^748) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011011 : Branch 1 (-359761639/8000000 : ℚ) vp0000101101 := by
  apply branch_checked idp00001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-359761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-363761639/4000000 : ℚ) by norm_num]
  exact coverp00001011011
theorem coverp0000101101 : Covers (-359761639/8000000 : ℚ) vp0000101101 := join_branches bp00001011010 bp00001011011
private noncomputable def vp00001011001111_0 : Blocks := edgeBlocks% "full/vectors/00001011001111-V-0000.bin"
noncomputable def vp00001011001111 : Blocks := vp00001011001111_0
theorem coverp00001011001111 : Covers (-359261639/500000 : ℚ) vp00001011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011001110_0 : Blocks := edgeBlocks% "full/vectors/00001011001110-V-0000.bin"
noncomputable def vp00001011001110 : Blocks := vp00001011001110_0
theorem coverp00001011001110 : Covers (-358761639/500000 : ℚ) vp00001011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000101100111-V-0000.bin"
noncomputable def vp0000101100111 : Blocks := vp0000101100111_0
private theorem bp00001011001110 : Branch 0 (-358761639/1000000 : ℚ) vp0000101100111 := by
  apply branch_left_normalized (c:=vp00001011001110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-358761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-358761639/500000 : ℚ) by norm_num]
  exact coverp00001011001110
private noncomputable def ep00001011001111_0 : Blocks := edgeBlocks% "full/vectors/00001011001111-E-0000.bin"
noncomputable def ep00001011001111 : Blocks := ep00001011001111_0
private theorem idp00001011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100111.list =
    C ((2:ℤ)^76) * horner X vp00001011001111.list + horner X ep00001011001111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011001111 : Branch 1 (-358761639/1000000 : ℚ) vp0000101100111 := by
  apply branch_checked idp00001011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-358761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-359261639/500000 : ℚ) by norm_num]
  exact coverp00001011001111
theorem coverp0000101100111 : Covers (-358761639/1000000 : ℚ) vp0000101100111 := join_branches bp00001011001110 bp00001011001111
private noncomputable def vp00001011001101_0 : Blocks := edgeBlocks% "full/vectors/00001011001101-V-0000.bin"
noncomputable def vp00001011001101 : Blocks := vp00001011001101_0
theorem coverp00001011001101 : Covers (-358261639/500000 : ℚ) vp00001011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011001100_0 : Blocks := edgeBlocks% "full/vectors/00001011001100-V-0000.bin"
noncomputable def vp00001011001100 : Blocks := vp00001011001100_0
theorem coverp00001011001100 : Covers (-357761639/500000 : ℚ) vp00001011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100110_0 : Blocks := edgeBlocks% "full/vectors/0000101100110-V-0000.bin"
noncomputable def vp0000101100110 : Blocks := vp0000101100110_0
private theorem bp00001011001100 : Branch 0 (-357761639/1000000 : ℚ) vp0000101100110 := by
  apply branch_left_normalized (c:=vp00001011001100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-357761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-357761639/500000 : ℚ) by norm_num]
  exact coverp00001011001100
private noncomputable def ep00001011001101_0 : Blocks := edgeBlocks% "full/vectors/00001011001101-E-0000.bin"
noncomputable def ep00001011001101 : Blocks := ep00001011001101_0
private theorem idp00001011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100110.list =
    C ((2:ℤ)^79) * horner X vp00001011001101.list + horner X ep00001011001101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011001101 : Branch 1 (-357761639/1000000 : ℚ) vp0000101100110 := by
  apply branch_checked idp00001011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-357761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-358261639/500000 : ℚ) by norm_num]
  exact coverp00001011001101
theorem coverp0000101100110 : Covers (-357761639/1000000 : ℚ) vp0000101100110 := join_branches bp00001011001100 bp00001011001101
private noncomputable def vp000010110011_0 : Blocks := edgeBlocks% "full/vectors/000010110011-V-0000.bin"
noncomputable def vp000010110011 : Blocks := vp000010110011_0
private theorem bp0000101100110 : Branch 0 (-357761639/2000000 : ℚ) vp000010110011 := by
  apply branch_left_normalized (c:=vp0000101100110) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-357761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-357761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100110
private noncomputable def ep0000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000101100111-E-0000.bin"
noncomputable def ep0000101100111 : Blocks := ep0000101100111_0
private theorem idp0000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110011.list =
    C ((2:ℤ)^136) * horner X vp0000101100111.list + horner X ep0000101100111.list := by
  exact edge_identity (B := (2:ℤ)^284) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101100111 : Branch 1 (-357761639/2000000 : ℚ) vp000010110011 := by
  apply branch_checked idp0000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-357761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-358761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100111
theorem coverp000010110011 : Covers (-357761639/2000000 : ℚ) vp000010110011 := join_branches bp0000101100110 bp0000101100111
private noncomputable def vp00001011001011_0 : Blocks := edgeBlocks% "full/vectors/00001011001011-V-0000.bin"
noncomputable def vp00001011001011 : Blocks := vp00001011001011_0
theorem coverp00001011001011 : Covers (-357261639/500000 : ℚ) vp00001011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011001010_0 : Blocks := edgeBlocks% "full/vectors/00001011001010-V-0000.bin"
noncomputable def vp00001011001010 : Blocks := vp00001011001010_0
theorem coverp00001011001010 : Covers (-356761639/500000 : ℚ) vp00001011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000101100101-V-0000.bin"
noncomputable def vp0000101100101 : Blocks := vp0000101100101_0
private theorem bp00001011001010 : Branch 0 (-356761639/1000000 : ℚ) vp0000101100101 := by
  apply branch_left_normalized (c:=vp00001011001010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-356761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-356761639/500000 : ℚ) by norm_num]
  exact coverp00001011001010
private noncomputable def ep00001011001011_0 : Blocks := edgeBlocks% "full/vectors/00001011001011-E-0000.bin"
noncomputable def ep00001011001011 : Blocks := ep00001011001011_0
private theorem idp00001011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100101.list =
    C ((2:ℤ)^75) * horner X vp00001011001011.list + horner X ep00001011001011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011001011 : Branch 1 (-356761639/1000000 : ℚ) vp0000101100101 := by
  apply branch_checked idp00001011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-356761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-357261639/500000 : ℚ) by norm_num]
  exact coverp00001011001011
theorem coverp0000101100101 : Covers (-356761639/1000000 : ℚ) vp0000101100101 := join_branches bp00001011001010 bp00001011001011
private noncomputable def vp00001011001001_0 : Blocks := edgeBlocks% "full/vectors/00001011001001-V-0000.bin"
noncomputable def vp00001011001001 : Blocks := vp00001011001001_0
theorem coverp00001011001001 : Covers (-356261639/500000 : ℚ) vp00001011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011001000_0 : Blocks := edgeBlocks% "full/vectors/00001011001000-V-0000.bin"
noncomputable def vp00001011001000 : Blocks := vp00001011001000_0
theorem coverp00001011001000 : Covers (-355761639/500000 : ℚ) vp00001011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100100_0 : Blocks := edgeBlocks% "full/vectors/0000101100100-V-0000.bin"
noncomputable def vp0000101100100 : Blocks := vp0000101100100_0
private theorem bp00001011001000 : Branch 0 (-355761639/1000000 : ℚ) vp0000101100100 := by
  apply branch_left_normalized (c:=vp00001011001000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-355761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-355761639/500000 : ℚ) by norm_num]
  exact coverp00001011001000
private noncomputable def ep00001011001001_0 : Blocks := edgeBlocks% "full/vectors/00001011001001-E-0000.bin"
noncomputable def ep00001011001001 : Blocks := ep00001011001001_0
private theorem idp00001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100100.list =
    C ((2:ℤ)^75) * horner X vp00001011001001.list + horner X ep00001011001001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011001001 : Branch 1 (-355761639/1000000 : ℚ) vp0000101100100 := by
  apply branch_checked idp00001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-355761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-356261639/500000 : ℚ) by norm_num]
  exact coverp00001011001001
theorem coverp0000101100100 : Covers (-355761639/1000000 : ℚ) vp0000101100100 := join_branches bp00001011001000 bp00001011001001
private noncomputable def vp000010110010_0 : Blocks := edgeBlocks% "full/vectors/000010110010-V-0000.bin"
noncomputable def vp000010110010 : Blocks := vp000010110010_0
private theorem bp0000101100100 : Branch 0 (-355761639/2000000 : ℚ) vp000010110010 := by
  apply branch_left_normalized (c:=vp0000101100100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-355761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-355761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100100
private noncomputable def ep0000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000101100101-E-0000.bin"
noncomputable def ep0000101100101 : Blocks := ep0000101100101_0
private theorem idp0000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110010.list =
    C ((2:ℤ)^130) * horner X vp0000101100101.list + horner X ep0000101100101.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101100101 : Branch 1 (-355761639/2000000 : ℚ) vp000010110010 := by
  apply branch_checked idp0000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-355761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-356761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100101
theorem coverp000010110010 : Covers (-355761639/2000000 : ℚ) vp000010110010 := join_branches bp0000101100100 bp0000101100101
private noncomputable def vp00001011001_0 : Blocks := edgeBlocks% "full/vectors/00001011001-V-0000.bin"
private noncomputable def vp00001011001_1 : Blocks := edgeBlocks% "full/vectors/00001011001-V-0001.bin"
noncomputable def vp00001011001 : Blocks := (Blocks.join vp00001011001_0 vp00001011001_1)
private theorem bp000010110010 : Branch 0 (-355761639/4000000 : ℚ) vp00001011001 := by
  apply branch_left_normalized (c:=vp000010110010) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-355761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-355761639/2000000 : ℚ) by norm_num]
  exact coverp000010110010
private noncomputable def ep000010110011_0 : Blocks := edgeBlocks% "full/vectors/000010110011-E-0000.bin"
private noncomputable def ep000010110011_1 : Blocks := edgeBlocks% "full/vectors/000010110011-E-0001.bin"
noncomputable def ep000010110011 : Blocks := (Blocks.join ep000010110011_0 ep000010110011_1)
private theorem idp000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011001.list =
    C ((2:ℤ)^240) * horner X vp000010110011.list + horner X ep000010110011.list := by
  exact edge_identity (B := (2:ℤ)^441) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110011 : Branch 1 (-355761639/4000000 : ℚ) vp00001011001 := by
  apply branch_checked idp000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-355761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-357761639/2000000 : ℚ) by norm_num]
  exact coverp000010110011
theorem coverp00001011001 : Covers (-355761639/4000000 : ℚ) vp00001011001 := join_branches bp000010110010 bp000010110011
private noncomputable def vp00001011000111_0 : Blocks := edgeBlocks% "full/vectors/00001011000111-V-0000.bin"
noncomputable def vp00001011000111 : Blocks := vp00001011000111_0
theorem coverp00001011000111 : Covers (-355261639/500000 : ℚ) vp00001011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011000110_0 : Blocks := edgeBlocks% "full/vectors/00001011000110-V-0000.bin"
noncomputable def vp00001011000110 : Blocks := vp00001011000110_0
theorem coverp00001011000110 : Covers (-354761639/500000 : ℚ) vp00001011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000101100011-V-0000.bin"
noncomputable def vp0000101100011 : Blocks := vp0000101100011_0
private theorem bp00001011000110 : Branch 0 (-354761639/1000000 : ℚ) vp0000101100011 := by
  apply branch_left_normalized (c:=vp00001011000110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-354761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-354761639/500000 : ℚ) by norm_num]
  exact coverp00001011000110
private noncomputable def ep00001011000111_0 : Blocks := edgeBlocks% "full/vectors/00001011000111-E-0000.bin"
noncomputable def ep00001011000111 : Blocks := ep00001011000111_0
private theorem idp00001011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100011.list =
    C ((2:ℤ)^76) * horner X vp00001011000111.list + horner X ep00001011000111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011000111 : Branch 1 (-354761639/1000000 : ℚ) vp0000101100011 := by
  apply branch_checked idp00001011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-354761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-355261639/500000 : ℚ) by norm_num]
  exact coverp00001011000111
theorem coverp0000101100011 : Covers (-354761639/1000000 : ℚ) vp0000101100011 := join_branches bp00001011000110 bp00001011000111
private noncomputable def vp00001011000101_0 : Blocks := edgeBlocks% "full/vectors/00001011000101-V-0000.bin"
noncomputable def vp00001011000101 : Blocks := vp00001011000101_0
theorem coverp00001011000101 : Covers (-354261639/500000 : ℚ) vp00001011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011000100_0 : Blocks := edgeBlocks% "full/vectors/00001011000100-V-0000.bin"
noncomputable def vp00001011000100 : Blocks := vp00001011000100_0
theorem coverp00001011000100 : Covers (-353761639/500000 : ℚ) vp00001011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100010_0 : Blocks := edgeBlocks% "full/vectors/0000101100010-V-0000.bin"
noncomputable def vp0000101100010 : Blocks := vp0000101100010_0
private theorem bp00001011000100 : Branch 0 (-353761639/1000000 : ℚ) vp0000101100010 := by
  apply branch_left_normalized (c:=vp00001011000100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-353761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-353761639/500000 : ℚ) by norm_num]
  exact coverp00001011000100
private noncomputable def ep00001011000101_0 : Blocks := edgeBlocks% "full/vectors/00001011000101-E-0000.bin"
noncomputable def ep00001011000101 : Blocks := ep00001011000101_0
private theorem idp00001011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100010.list =
    C ((2:ℤ)^76) * horner X vp00001011000101.list + horner X ep00001011000101.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011000101 : Branch 1 (-353761639/1000000 : ℚ) vp0000101100010 := by
  apply branch_checked idp00001011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-353761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-354261639/500000 : ℚ) by norm_num]
  exact coverp00001011000101
theorem coverp0000101100010 : Covers (-353761639/1000000 : ℚ) vp0000101100010 := join_branches bp00001011000100 bp00001011000101
private noncomputable def vp000010110001_0 : Blocks := edgeBlocks% "full/vectors/000010110001-V-0000.bin"
noncomputable def vp000010110001 : Blocks := vp000010110001_0
private theorem bp0000101100010 : Branch 0 (-353761639/2000000 : ℚ) vp000010110001 := by
  apply branch_left_normalized (c:=vp0000101100010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-353761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-353761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100010
private noncomputable def ep0000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000101100011-E-0000.bin"
noncomputable def ep0000101100011 : Blocks := ep0000101100011_0
private theorem idp0000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110001.list =
    C ((2:ℤ)^133) * horner X vp0000101100011.list + horner X ep0000101100011.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101100011 : Branch 1 (-353761639/2000000 : ℚ) vp000010110001 := by
  apply branch_checked idp0000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-353761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-354761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100011
theorem coverp000010110001 : Covers (-353761639/2000000 : ℚ) vp000010110001 := join_branches bp0000101100010 bp0000101100011
private noncomputable def vp00001011000011_0 : Blocks := edgeBlocks% "full/vectors/00001011000011-V-0000.bin"
noncomputable def vp00001011000011 : Blocks := vp00001011000011_0
theorem coverp00001011000011 : Covers (-353261639/500000 : ℚ) vp00001011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011000010_0 : Blocks := edgeBlocks% "full/vectors/00001011000010-V-0000.bin"
noncomputable def vp00001011000010 : Blocks := vp00001011000010_0
theorem coverp00001011000010 : Covers (-352761639/500000 : ℚ) vp00001011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101100001_0 : Blocks := edgeBlocks% "full/vectors/0000101100001-V-0000.bin"
noncomputable def vp0000101100001 : Blocks := vp0000101100001_0
private theorem bp00001011000010 : Branch 0 (-352761639/1000000 : ℚ) vp0000101100001 := by
  apply branch_left_normalized (c:=vp00001011000010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-352761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-352761639/500000 : ℚ) by norm_num]
  exact coverp00001011000010
private noncomputable def ep00001011000011_0 : Blocks := edgeBlocks% "full/vectors/00001011000011-E-0000.bin"
noncomputable def ep00001011000011 : Blocks := ep00001011000011_0
private theorem idp00001011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100001.list =
    C ((2:ℤ)^78) * horner X vp00001011000011.list + horner X ep00001011000011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011000011 : Branch 1 (-352761639/1000000 : ℚ) vp0000101100001 := by
  apply branch_checked idp00001011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-352761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-353261639/500000 : ℚ) by norm_num]
  exact coverp00001011000011
theorem coverp0000101100001 : Covers (-352761639/1000000 : ℚ) vp0000101100001 := join_branches bp00001011000010 bp00001011000011
private noncomputable def vp000010110000011_0 : Blocks := edgeBlocks% "full/vectors/000010110000011-V-0000.bin"
noncomputable def vp000010110000011 : Blocks := vp000010110000011_0
theorem coverp000010110000011 : Covers (-352511639/250000 : ℚ) vp000010110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010110000010_0 : Blocks := edgeBlocks% "full/vectors/000010110000010-V-0000.bin"
noncomputable def vp000010110000010 : Blocks := vp000010110000010_0
theorem coverp000010110000010 : Covers (-352261639/250000 : ℚ) vp000010110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011000001_0 : Blocks := edgeBlocks% "full/vectors/00001011000001-V-0000.bin"
noncomputable def vp00001011000001 : Blocks := vp00001011000001_0
private theorem bp000010110000010 : Branch 0 (-352261639/500000 : ℚ) vp00001011000001 := by
  apply branch_left_normalized (c:=vp000010110000010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-352261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-352261639/250000 : ℚ) by norm_num]
  exact coverp000010110000010
private noncomputable def ep000010110000011_0 : Blocks := edgeBlocks% "full/vectors/000010110000011-E-0000.bin"
noncomputable def ep000010110000011 : Blocks := ep000010110000011_0
private theorem idp000010110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011000001.list =
    C ((2:ℤ)^48) * horner X vp000010110000011.list + horner X ep000010110000011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110000011 : Branch 1 (-352261639/500000 : ℚ) vp00001011000001 := by
  apply branch_checked idp000010110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-352261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-352511639/250000 : ℚ) by norm_num]
  exact coverp000010110000011
theorem coverp00001011000001 : Covers (-352261639/500000 : ℚ) vp00001011000001 := join_branches bp000010110000010 bp000010110000011
private noncomputable def vp000010110000001_0 : Blocks := edgeBlocks% "full/vectors/000010110000001-V-0000.bin"
noncomputable def vp000010110000001 : Blocks := vp000010110000001_0
theorem coverp000010110000001 : Covers (-352011639/250000 : ℚ) vp000010110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010110000000_0 : Blocks := edgeBlocks% "full/vectors/000010110000000-V-0000.bin"
noncomputable def vp000010110000000 : Blocks := vp000010110000000_0
theorem coverp000010110000000 : Covers (-351761639/250000 : ℚ) vp000010110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001011000000_0 : Blocks := edgeBlocks% "full/vectors/00001011000000-V-0000.bin"
noncomputable def vp00001011000000 : Blocks := vp00001011000000_0
private theorem bp000010110000000 : Branch 0 (-351761639/500000 : ℚ) vp00001011000000 := by
  apply branch_left_normalized (c:=vp000010110000000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-351761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/250000 : ℚ) by norm_num]
  exact coverp000010110000000
private noncomputable def ep000010110000001_0 : Blocks := edgeBlocks% "full/vectors/000010110000001-E-0000.bin"
noncomputable def ep000010110000001 : Blocks := ep000010110000001_0
private theorem idp000010110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011000000.list =
    C ((2:ℤ)^48) * horner X vp000010110000001.list + horner X ep000010110000001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110000001 : Branch 1 (-351761639/500000 : ℚ) vp00001011000000 := by
  apply branch_checked idp000010110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-352011639/250000 : ℚ) by norm_num]
  exact coverp000010110000001
theorem coverp00001011000000 : Covers (-351761639/500000 : ℚ) vp00001011000000 := join_branches bp000010110000000 bp000010110000001
private noncomputable def vp0000101100000_0 : Blocks := edgeBlocks% "full/vectors/0000101100000-V-0000.bin"
noncomputable def vp0000101100000 : Blocks := vp0000101100000_0
private theorem bp00001011000000 : Branch 0 (-351761639/1000000 : ℚ) vp0000101100000 := by
  apply branch_left_normalized (c:=vp00001011000000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-351761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/500000 : ℚ) by norm_num]
  exact coverp00001011000000
private noncomputable def ep00001011000001_0 : Blocks := edgeBlocks% "full/vectors/00001011000001-E-0000.bin"
noncomputable def ep00001011000001 : Blocks := ep00001011000001_0
private theorem idp00001011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100000.list =
    C ((2:ℤ)^77) * horner X vp00001011000001.list + horner X ep00001011000001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011000001 : Branch 1 (-351761639/1000000 : ℚ) vp0000101100000 := by
  apply branch_checked idp00001011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-352261639/500000 : ℚ) by norm_num]
  exact coverp00001011000001
theorem coverp0000101100000 : Covers (-351761639/1000000 : ℚ) vp0000101100000 := join_branches bp00001011000000 bp00001011000001
private noncomputable def vp000010110000_0 : Blocks := edgeBlocks% "full/vectors/000010110000-V-0000.bin"
noncomputable def vp000010110000 : Blocks := vp000010110000_0
private theorem bp0000101100000 : Branch 0 (-351761639/2000000 : ℚ) vp000010110000 := by
  apply branch_left_normalized (c:=vp0000101100000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-351761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100000
private noncomputable def ep0000101100001_0 : Blocks := edgeBlocks% "full/vectors/0000101100001-E-0000.bin"
noncomputable def ep0000101100001 : Blocks := ep0000101100001_0
private theorem idp0000101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110000.list =
    C ((2:ℤ)^134) * horner X vp0000101100001.list + horner X ep0000101100001.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101100001 : Branch 1 (-351761639/2000000 : ℚ) vp000010110000 := by
  apply branch_checked idp0000101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-352761639/1000000 : ℚ) by norm_num]
  exact coverp0000101100001
theorem coverp000010110000 : Covers (-351761639/2000000 : ℚ) vp000010110000 := join_branches bp0000101100000 bp0000101100001
private noncomputable def vp00001011000_0 : Blocks := edgeBlocks% "full/vectors/00001011000-V-0000.bin"
private noncomputable def vp00001011000_1 : Blocks := edgeBlocks% "full/vectors/00001011000-V-0001.bin"
noncomputable def vp00001011000 : Blocks := (Blocks.join vp00001011000_0 vp00001011000_1)
private theorem bp000010110000 : Branch 0 (-351761639/4000000 : ℚ) vp00001011000 := by
  apply branch_left_normalized (c:=vp000010110000) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-351761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/2000000 : ℚ) by norm_num]
  exact coverp000010110000
private noncomputable def ep000010110001_0 : Blocks := edgeBlocks% "full/vectors/000010110001-E-0000.bin"
private noncomputable def ep000010110001_1 : Blocks := edgeBlocks% "full/vectors/000010110001-E-0001.bin"
noncomputable def ep000010110001 : Blocks := (Blocks.join ep000010110001_0 ep000010110001_1)
private theorem idp000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011000.list =
    C ((2:ℤ)^246) * horner X vp000010110001.list + horner X ep000010110001.list := by
  exact edge_identity (B := (2:ℤ)^447) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010110001 : Branch 1 (-351761639/4000000 : ℚ) vp00001011000 := by
  apply branch_checked idp000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-353761639/2000000 : ℚ) by norm_num]
  exact coverp000010110001
theorem coverp00001011000 : Covers (-351761639/4000000 : ℚ) vp00001011000 := join_branches bp000010110000 bp000010110001
private noncomputable def vp0000101100_0 : Blocks := edgeBlocks% "full/vectors/0000101100-V-0000.bin"
private noncomputable def vp0000101100_1 : Blocks := edgeBlocks% "full/vectors/0000101100-V-0001.bin"
private noncomputable def vp0000101100_2 : Blocks := edgeBlocks% "full/vectors/0000101100-V-0002.bin"
private noncomputable def vp0000101100_3 : Blocks := edgeBlocks% "full/vectors/0000101100-V-0003.bin"
noncomputable def vp0000101100 : Blocks := (Blocks.join (Blocks.join vp0000101100_0 vp0000101100_1) (Blocks.join vp0000101100_2 vp0000101100_3))
private theorem bp00001011000 : Branch 0 (-351761639/8000000 : ℚ) vp0000101100 := by
  apply branch_left_normalized (c:=vp00001011000) (k:=0) (m:=232) (by decide +kernel)
  rw [show 2*(-351761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/4000000 : ℚ) by norm_num]
  exact coverp00001011000
private noncomputable def ep00001011001_0 : Blocks := edgeBlocks% "full/vectors/00001011001-E-0000.bin"
private noncomputable def ep00001011001_1 : Blocks := edgeBlocks% "full/vectors/00001011001-E-0001.bin"
private noncomputable def ep00001011001_2 : Blocks := edgeBlocks% "full/vectors/00001011001-E-0002.bin"
private noncomputable def ep00001011001_3 : Blocks := edgeBlocks% "full/vectors/00001011001-E-0003.bin"
noncomputable def ep00001011001 : Blocks := (Blocks.join (Blocks.join ep00001011001_0 ep00001011001_1) (Blocks.join ep00001011001_2 ep00001011001_3))
private theorem idp00001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101100.list =
    C ((2:ℤ)^467) * horner X vp00001011001.list + horner X ep00001011001.list := by
  exact edge_identity (B := (2:ℤ)^766) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001011001 : Branch 1 (-351761639/8000000 : ℚ) vp0000101100 := by
  apply branch_checked idp00001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-355761639/4000000 : ℚ) by norm_num]
  exact coverp00001011001
theorem coverp0000101100 : Covers (-351761639/8000000 : ℚ) vp0000101100 := join_branches bp00001011000 bp00001011001
private noncomputable def vp000010110_0 : Blocks := edgeBlocks% "full/vectors/000010110-V-0000.bin"
private noncomputable def vp000010110_1 : Blocks := edgeBlocks% "full/vectors/000010110-V-0001.bin"
private noncomputable def vp000010110_2 : Blocks := edgeBlocks% "full/vectors/000010110-V-0002.bin"
private noncomputable def vp000010110_3 : Blocks := edgeBlocks% "full/vectors/000010110-V-0003.bin"
private noncomputable def vp000010110_4 : Blocks := edgeBlocks% "full/vectors/000010110-V-0004.bin"
private noncomputable def vp000010110_5 : Blocks := edgeBlocks% "full/vectors/000010110-V-0005.bin"
private noncomputable def vp000010110_6 : Blocks := edgeBlocks% "full/vectors/000010110-V-0006.bin"
noncomputable def vp000010110 : Blocks := (Blocks.join (Blocks.join vp000010110_0 (Blocks.join vp000010110_1 vp000010110_2)) (Blocks.join (Blocks.join vp000010110_3 vp000010110_4) (Blocks.join vp000010110_5 vp000010110_6)))
private theorem bp0000101100 : Branch 0 (-351761639/16000000 : ℚ) vp000010110 := by
  apply branch_left_normalized (c:=vp0000101100) (k:=0) (m:=440) (by decide +kernel)
  rw [show 2*(-351761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/8000000 : ℚ) by norm_num]
  exact coverp0000101100
private noncomputable def ep0000101101_0 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0000.bin"
private noncomputable def ep0000101101_1 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0001.bin"
private noncomputable def ep0000101101_2 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0002.bin"
private noncomputable def ep0000101101_3 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0003.bin"
private noncomputable def ep0000101101_4 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0004.bin"
private noncomputable def ep0000101101_5 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0005.bin"
private noncomputable def ep0000101101_6 : Blocks := edgeBlocks% "full/vectors/0000101101-E-0006.bin"
noncomputable def ep0000101101 : Blocks := (Blocks.join (Blocks.join ep0000101101_0 (Blocks.join ep0000101101_1 ep0000101101_2)) (Blocks.join (Blocks.join ep0000101101_3 ep0000101101_4) (Blocks.join ep0000101101_5 ep0000101101_6)))
private theorem idp0000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010110.list =
    C ((2:ℤ)^905) * horner X vp0000101101.list + horner X ep0000101101.list := by
  exact edge_identity (B := (2:ℤ)^1399) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101101 : Branch 1 (-351761639/16000000 : ℚ) vp000010110 := by
  apply branch_checked idp0000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-359761639/8000000 : ℚ) by norm_num]
  exact coverp0000101101
theorem coverp000010110 : Covers (-351761639/16000000 : ℚ) vp000010110 := join_branches bp0000101100 bp0000101101
private noncomputable def vp00001011_0 : Blocks := edgeBlocks% "full/vectors/00001011-V-0000.bin"
private noncomputable def vp00001011_1 : Blocks := edgeBlocks% "full/vectors/00001011-V-0001.bin"
private noncomputable def vp00001011_2 : Blocks := edgeBlocks% "full/vectors/00001011-V-0002.bin"
private noncomputable def vp00001011_3 : Blocks := edgeBlocks% "full/vectors/00001011-V-0003.bin"
private noncomputable def vp00001011_4 : Blocks := edgeBlocks% "full/vectors/00001011-V-0004.bin"
private noncomputable def vp00001011_5 : Blocks := edgeBlocks% "full/vectors/00001011-V-0005.bin"
private noncomputable def vp00001011_6 : Blocks := edgeBlocks% "full/vectors/00001011-V-0006.bin"
private noncomputable def vp00001011_7 : Blocks := edgeBlocks% "full/vectors/00001011-V-0007.bin"
private noncomputable def vp00001011_8 : Blocks := edgeBlocks% "full/vectors/00001011-V-0008.bin"
private noncomputable def vp00001011_9 : Blocks := edgeBlocks% "full/vectors/00001011-V-0009.bin"
private noncomputable def vp00001011_10 : Blocks := edgeBlocks% "full/vectors/00001011-V-0010.bin"
private noncomputable def vp00001011_11 : Blocks := edgeBlocks% "full/vectors/00001011-V-0011.bin"
private noncomputable def vp00001011_12 : Blocks := edgeBlocks% "full/vectors/00001011-V-0012.bin"
noncomputable def vp00001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001011_0 (Blocks.join vp00001011_1 vp00001011_2)) (Blocks.join vp00001011_3 (Blocks.join vp00001011_4 vp00001011_5))) (Blocks.join (Blocks.join vp00001011_6 (Blocks.join vp00001011_7 vp00001011_8)) (Blocks.join (Blocks.join vp00001011_9 vp00001011_10) (Blocks.join vp00001011_11 vp00001011_12))))
private theorem bp000010110 : Branch 0 (-351761639/32000000 : ℚ) vp00001011 := by
  apply branch_left_normalized (c:=vp000010110) (k:=0) (m:=852) (by decide +kernel)
  rw [show 2*(-351761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-351761639/16000000 : ℚ) by norm_num]
  exact coverp000010110
private noncomputable def ep000010111_0 : Blocks := edgeBlocks% "full/vectors/000010111-E-0000.bin"
private noncomputable def ep000010111_1 : Blocks := edgeBlocks% "full/vectors/000010111-E-0001.bin"
private noncomputable def ep000010111_2 : Blocks := edgeBlocks% "full/vectors/000010111-E-0002.bin"
private noncomputable def ep000010111_3 : Blocks := edgeBlocks% "full/vectors/000010111-E-0003.bin"
private noncomputable def ep000010111_4 : Blocks := edgeBlocks% "full/vectors/000010111-E-0004.bin"
private noncomputable def ep000010111_5 : Blocks := edgeBlocks% "full/vectors/000010111-E-0005.bin"
private noncomputable def ep000010111_6 : Blocks := edgeBlocks% "full/vectors/000010111-E-0006.bin"
private noncomputable def ep000010111_7 : Blocks := edgeBlocks% "full/vectors/000010111-E-0007.bin"
private noncomputable def ep000010111_8 : Blocks := edgeBlocks% "full/vectors/000010111-E-0008.bin"
private noncomputable def ep000010111_9 : Blocks := edgeBlocks% "full/vectors/000010111-E-0009.bin"
private noncomputable def ep000010111_10 : Blocks := edgeBlocks% "full/vectors/000010111-E-0010.bin"
private noncomputable def ep000010111_11 : Blocks := edgeBlocks% "full/vectors/000010111-E-0011.bin"
private noncomputable def ep000010111_12 : Blocks := edgeBlocks% "full/vectors/000010111-E-0012.bin"
noncomputable def ep000010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000010111_0 (Blocks.join ep000010111_1 ep000010111_2)) (Blocks.join ep000010111_3 (Blocks.join ep000010111_4 ep000010111_5))) (Blocks.join (Blocks.join ep000010111_6 (Blocks.join ep000010111_7 ep000010111_8)) (Blocks.join (Blocks.join ep000010111_9 ep000010111_10) (Blocks.join ep000010111_11 ep000010111_12))))
private theorem idp000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001011.list =
    C ((2:ℤ)^1763) * horner X vp000010111.list + horner X ep000010111.list := by
  exact edge_identity (B := (2:ℤ)^2644) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010111 : Branch 1 (-351761639/32000000 : ℚ) vp00001011 := by
  apply branch_checked idp000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-351761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-367761639/16000000 : ℚ) by norm_num]
  exact coverp000010111
theorem coverp00001011 : Covers (-351761639/32000000 : ℚ) vp00001011 := join_branches bp000010110 bp000010111
private noncomputable def vp0000101_0 : Blocks := edgeBlocks% "full/vectors/0000101-V-0000.bin"
private noncomputable def vp0000101_1 : Blocks := edgeBlocks% "full/vectors/0000101-V-0001.bin"
private noncomputable def vp0000101_2 : Blocks := edgeBlocks% "full/vectors/0000101-V-0002.bin"
private noncomputable def vp0000101_3 : Blocks := edgeBlocks% "full/vectors/0000101-V-0003.bin"
private noncomputable def vp0000101_4 : Blocks := edgeBlocks% "full/vectors/0000101-V-0004.bin"
private noncomputable def vp0000101_5 : Blocks := edgeBlocks% "full/vectors/0000101-V-0005.bin"
private noncomputable def vp0000101_6 : Blocks := edgeBlocks% "full/vectors/0000101-V-0006.bin"
private noncomputable def vp0000101_7 : Blocks := edgeBlocks% "full/vectors/0000101-V-0007.bin"
private noncomputable def vp0000101_8 : Blocks := edgeBlocks% "full/vectors/0000101-V-0008.bin"
private noncomputable def vp0000101_9 : Blocks := edgeBlocks% "full/vectors/0000101-V-0009.bin"
private noncomputable def vp0000101_10 : Blocks := edgeBlocks% "full/vectors/0000101-V-0010.bin"
private noncomputable def vp0000101_11 : Blocks := edgeBlocks% "full/vectors/0000101-V-0011.bin"
private noncomputable def vp0000101_12 : Blocks := edgeBlocks% "full/vectors/0000101-V-0012.bin"
private noncomputable def vp0000101_13 : Blocks := edgeBlocks% "full/vectors/0000101-V-0013.bin"
private noncomputable def vp0000101_14 : Blocks := edgeBlocks% "full/vectors/0000101-V-0014.bin"
private noncomputable def vp0000101_15 : Blocks := edgeBlocks% "full/vectors/0000101-V-0015.bin"
private noncomputable def vp0000101_16 : Blocks := edgeBlocks% "full/vectors/0000101-V-0016.bin"
private noncomputable def vp0000101_17 : Blocks := edgeBlocks% "full/vectors/0000101-V-0017.bin"
private noncomputable def vp0000101_18 : Blocks := edgeBlocks% "full/vectors/0000101-V-0018.bin"
private noncomputable def vp0000101_19 : Blocks := edgeBlocks% "full/vectors/0000101-V-0019.bin"
private noncomputable def vp0000101_20 : Blocks := edgeBlocks% "full/vectors/0000101-V-0020.bin"
private noncomputable def vp0000101_21 : Blocks := edgeBlocks% "full/vectors/0000101-V-0021.bin"
private noncomputable def vp0000101_22 : Blocks := edgeBlocks% "full/vectors/0000101-V-0022.bin"
private noncomputable def vp0000101_23 : Blocks := edgeBlocks% "full/vectors/0000101-V-0023.bin"
private noncomputable def vp0000101_24 : Blocks := edgeBlocks% "full/vectors/0000101-V-0024.bin"
private noncomputable def vp0000101_25 : Blocks := edgeBlocks% "full/vectors/0000101-V-0025.bin"
private noncomputable def vp0000101_26 : Blocks := edgeBlocks% "full/vectors/0000101-V-0026.bin"
noncomputable def vp0000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000101_0 (Blocks.join vp0000101_1 vp0000101_2)) (Blocks.join vp0000101_3 (Blocks.join vp0000101_4 vp0000101_5))) (Blocks.join (Blocks.join vp0000101_6 (Blocks.join vp0000101_7 vp0000101_8)) (Blocks.join (Blocks.join vp0000101_9 vp0000101_10) (Blocks.join vp0000101_11 vp0000101_12)))) (Blocks.join (Blocks.join (Blocks.join vp0000101_13 (Blocks.join vp0000101_14 vp0000101_15)) (Blocks.join (Blocks.join vp0000101_16 vp0000101_17) (Blocks.join vp0000101_18 vp0000101_19))) (Blocks.join (Blocks.join vp0000101_20 (Blocks.join vp0000101_21 vp0000101_22)) (Blocks.join (Blocks.join vp0000101_23 vp0000101_24) (Blocks.join vp0000101_25 vp0000101_26)))))
private theorem bp00001010 : Branch 0 (-319761639/64000000 : ℚ) vp0000101 := by
  apply branch_left_normalized (c:=vp00001010) (k:=0) (m:=1729) (by decide +kernel)
  rw [show 2*(-319761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/32000000 : ℚ) by norm_num]
  exact coverp00001010
private noncomputable def ep00001011_0 : Blocks := edgeBlocks% "full/vectors/00001011-E-0000.bin"
private noncomputable def ep00001011_1 : Blocks := edgeBlocks% "full/vectors/00001011-E-0001.bin"
private noncomputable def ep00001011_2 : Blocks := edgeBlocks% "full/vectors/00001011-E-0002.bin"
private noncomputable def ep00001011_3 : Blocks := edgeBlocks% "full/vectors/00001011-E-0003.bin"
private noncomputable def ep00001011_4 : Blocks := edgeBlocks% "full/vectors/00001011-E-0004.bin"
private noncomputable def ep00001011_5 : Blocks := edgeBlocks% "full/vectors/00001011-E-0005.bin"
private noncomputable def ep00001011_6 : Blocks := edgeBlocks% "full/vectors/00001011-E-0006.bin"
private noncomputable def ep00001011_7 : Blocks := edgeBlocks% "full/vectors/00001011-E-0007.bin"
private noncomputable def ep00001011_8 : Blocks := edgeBlocks% "full/vectors/00001011-E-0008.bin"
private noncomputable def ep00001011_9 : Blocks := edgeBlocks% "full/vectors/00001011-E-0009.bin"
private noncomputable def ep00001011_10 : Blocks := edgeBlocks% "full/vectors/00001011-E-0010.bin"
private noncomputable def ep00001011_11 : Blocks := edgeBlocks% "full/vectors/00001011-E-0011.bin"
private noncomputable def ep00001011_12 : Blocks := edgeBlocks% "full/vectors/00001011-E-0012.bin"
private noncomputable def ep00001011_13 : Blocks := edgeBlocks% "full/vectors/00001011-E-0013.bin"
private noncomputable def ep00001011_14 : Blocks := edgeBlocks% "full/vectors/00001011-E-0014.bin"
private noncomputable def ep00001011_15 : Blocks := edgeBlocks% "full/vectors/00001011-E-0015.bin"
private noncomputable def ep00001011_16 : Blocks := edgeBlocks% "full/vectors/00001011-E-0016.bin"
private noncomputable def ep00001011_17 : Blocks := edgeBlocks% "full/vectors/00001011-E-0017.bin"
private noncomputable def ep00001011_18 : Blocks := edgeBlocks% "full/vectors/00001011-E-0018.bin"
private noncomputable def ep00001011_19 : Blocks := edgeBlocks% "full/vectors/00001011-E-0019.bin"
private noncomputable def ep00001011_20 : Blocks := edgeBlocks% "full/vectors/00001011-E-0020.bin"
private noncomputable def ep00001011_21 : Blocks := edgeBlocks% "full/vectors/00001011-E-0021.bin"
private noncomputable def ep00001011_22 : Blocks := edgeBlocks% "full/vectors/00001011-E-0022.bin"
private noncomputable def ep00001011_23 : Blocks := edgeBlocks% "full/vectors/00001011-E-0023.bin"
private noncomputable def ep00001011_24 : Blocks := edgeBlocks% "full/vectors/00001011-E-0024.bin"
private noncomputable def ep00001011_25 : Blocks := edgeBlocks% "full/vectors/00001011-E-0025.bin"
private noncomputable def ep00001011_26 : Blocks := edgeBlocks% "full/vectors/00001011-E-0026.bin"
noncomputable def ep00001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00001011_0 (Blocks.join ep00001011_1 ep00001011_2)) (Blocks.join ep00001011_3 (Blocks.join ep00001011_4 ep00001011_5))) (Blocks.join (Blocks.join ep00001011_6 (Blocks.join ep00001011_7 ep00001011_8)) (Blocks.join (Blocks.join ep00001011_9 ep00001011_10) (Blocks.join ep00001011_11 ep00001011_12)))) (Blocks.join (Blocks.join (Blocks.join ep00001011_13 (Blocks.join ep00001011_14 ep00001011_15)) (Blocks.join (Blocks.join ep00001011_16 ep00001011_17) (Blocks.join ep00001011_18 ep00001011_19))) (Blocks.join (Blocks.join ep00001011_20 (Blocks.join ep00001011_21 ep00001011_22)) (Blocks.join (Blocks.join ep00001011_23 ep00001011_24) (Blocks.join ep00001011_25 ep00001011_26)))))
private def ptsp00001011 : List ℤ := [((2:ℤ)^3582+0),((2:ℤ)^3582+1)]
private theorem boundp00001011 : 2^vp0000101.size*absSum vp0000101.list + ((2:ℤ)^3525*absSum vp00001011.list+absSum ep00001011.list) < (2:ℤ)^5275 := by decide +kernel
private theorem pointp00001011_0 : fastHom 1 ((2:ℤ)^3582+0) vp0000101 = ((2:ℤ)^3525)*vp00001011.subst ((2:ℤ)^3582+0)+ep00001011.subst ((2:ℤ)^3582+0) := by decide +kernel
private theorem pointp00001011_1 : fastHom 1 ((2:ℤ)^3582+1) vp0000101 = ((2:ℤ)^3525)*vp00001011.subst ((2:ℤ)^3582+1)+ep00001011.subst ((2:ℤ)^3582+1) := by decide +kernel
private theorem checkp00001011 (x:ℤ) (hx:x ∈ ptsp00001011) : fastHom 1 x vp0000101 = ((2:ℤ)^3525)*vp00001011.subst x+ep00001011.subst x := by
  simp only [ptsp00001011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp00001011_0
  · exact pointp00001011_1
private theorem idp00001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101.list =
    C ((2:ℤ)^3525) * horner X vp00001011.list + horner X ep00001011.list := by
  apply edge_identity (B := (2:ℤ)^5275) (by decide) (by positivity) (by positivity) boundp00001011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00001011 (by decide +kernel)
  · have h : ptsp00001011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00001011.trans_le (by decide +kernel)
  · exact checkp00001011
private theorem bp00001011 : Branch 1 (-319761639/64000000 : ℚ) vp0000101 := by
  apply branch_checked idp00001011 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-351761639/32000000 : ℚ) by norm_num]
  exact coverp00001011
theorem coverp0000101 : Covers (-319761639/64000000 : ℚ) vp0000101 := join_branches bp00001010 bp00001011
end NextProof.EdgeFull

