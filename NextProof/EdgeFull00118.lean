import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00117

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010110111111_0 : Blocks := edgeBlocks% "full/vectors/010110111111-V-0000.bin"
noncomputable def vp010110111111 : Blocks := vp010110111111_0
theorem coverp010110111111 : Covers (-2941761639/2000000 : ℚ) vp010110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110111110_0 : Blocks := edgeBlocks% "full/vectors/010110111110-V-0000.bin"
noncomputable def vp010110111110 : Blocks := vp010110111110_0
theorem coverp010110111110 : Covers (-2939761639/2000000 : ℚ) vp010110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011111_0 : Blocks := edgeBlocks% "full/vectors/01011011111-V-0000.bin"
noncomputable def vp01011011111 : Blocks := vp01011011111_0
private theorem bp010110111110 : Branch 0 (-2939761639/4000000 : ℚ) vp01011011111 := by
  apply branch_left_normalized (c:=vp010110111110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2939761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2939761639/2000000 : ℚ) by norm_num]
  exact coverp010110111110
private noncomputable def ep010110111111_0 : Blocks := edgeBlocks% "full/vectors/010110111111-E-0000.bin"
noncomputable def ep010110111111 : Blocks := ep010110111111_0
private theorem idp010110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011111.list =
    C ((2:ℤ)^106) * horner X vp010110111111.list + horner X ep010110111111.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110111111 : Branch 1 (-2939761639/4000000 : ℚ) vp01011011111 := by
  apply branch_checked idp010110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2939761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2941761639/2000000 : ℚ) by norm_num]
  exact coverp010110111111
theorem coverp01011011111 : Covers (-2939761639/4000000 : ℚ) vp01011011111 := join_branches bp010110111110 bp010110111111
private noncomputable def vp010110111101_0 : Blocks := edgeBlocks% "full/vectors/010110111101-V-0000.bin"
noncomputable def vp010110111101 : Blocks := vp010110111101_0
theorem coverp010110111101 : Covers (-2937761639/2000000 : ℚ) vp010110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110111100_0 : Blocks := edgeBlocks% "full/vectors/010110111100-V-0000.bin"
noncomputable def vp010110111100 : Blocks := vp010110111100_0
theorem coverp010110111100 : Covers (-2935761639/2000000 : ℚ) vp010110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011110_0 : Blocks := edgeBlocks% "full/vectors/01011011110-V-0000.bin"
noncomputable def vp01011011110 : Blocks := vp01011011110_0
private theorem bp010110111100 : Branch 0 (-2935761639/4000000 : ℚ) vp01011011110 := by
  apply branch_left_normalized (c:=vp010110111100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2935761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2935761639/2000000 : ℚ) by norm_num]
  exact coverp010110111100
private noncomputable def ep010110111101_0 : Blocks := edgeBlocks% "full/vectors/010110111101-E-0000.bin"
noncomputable def ep010110111101 : Blocks := ep010110111101_0
private theorem idp010110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011110.list =
    C ((2:ℤ)^107) * horner X vp010110111101.list + horner X ep010110111101.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110111101 : Branch 1 (-2935761639/4000000 : ℚ) vp01011011110 := by
  apply branch_checked idp010110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2935761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2937761639/2000000 : ℚ) by norm_num]
  exact coverp010110111101
theorem coverp01011011110 : Covers (-2935761639/4000000 : ℚ) vp01011011110 := join_branches bp010110111100 bp010110111101
private noncomputable def vp0101101111_0 : Blocks := edgeBlocks% "full/vectors/0101101111-V-0000.bin"
private noncomputable def vp0101101111_1 : Blocks := edgeBlocks% "full/vectors/0101101111-V-0001.bin"
noncomputable def vp0101101111 : Blocks := (Blocks.join vp0101101111_0 vp0101101111_1)
private theorem bp01011011110 : Branch 0 (-2935761639/8000000 : ℚ) vp0101101111 := by
  apply branch_left_normalized (c:=vp01011011110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2935761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2935761639/4000000 : ℚ) by norm_num]
  exact coverp01011011110
private noncomputable def ep01011011111_0 : Blocks := edgeBlocks% "full/vectors/01011011111-E-0000.bin"
private noncomputable def ep01011011111_1 : Blocks := edgeBlocks% "full/vectors/01011011111-E-0001.bin"
noncomputable def ep01011011111 : Blocks := (Blocks.join ep01011011111_0 ep01011011111_1)
private theorem idp01011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101111.list =
    C ((2:ℤ)^191) * horner X vp01011011111.list + horner X ep01011011111.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011011111 : Branch 1 (-2935761639/8000000 : ℚ) vp0101101111 := by
  apply branch_checked idp01011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2935761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2939761639/4000000 : ℚ) by norm_num]
  exact coverp01011011111
theorem coverp0101101111 : Covers (-2935761639/8000000 : ℚ) vp0101101111 := join_branches bp01011011110 bp01011011111
private noncomputable def vp010110111011_0 : Blocks := edgeBlocks% "full/vectors/010110111011-V-0000.bin"
noncomputable def vp010110111011 : Blocks := vp010110111011_0
theorem coverp010110111011 : Covers (-2933761639/2000000 : ℚ) vp010110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110111010_0 : Blocks := edgeBlocks% "full/vectors/010110111010-V-0000.bin"
noncomputable def vp010110111010 : Blocks := vp010110111010_0
theorem coverp010110111010 : Covers (-2931761639/2000000 : ℚ) vp010110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011101_0 : Blocks := edgeBlocks% "full/vectors/01011011101-V-0000.bin"
noncomputable def vp01011011101 : Blocks := vp01011011101_0
private theorem bp010110111010 : Branch 0 (-2931761639/4000000 : ℚ) vp01011011101 := by
  apply branch_left_normalized (c:=vp010110111010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2931761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2931761639/2000000 : ℚ) by norm_num]
  exact coverp010110111010
private noncomputable def ep010110111011_0 : Blocks := edgeBlocks% "full/vectors/010110111011-E-0000.bin"
noncomputable def ep010110111011 : Blocks := ep010110111011_0
private theorem idp010110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011101.list =
    C ((2:ℤ)^105) * horner X vp010110111011.list + horner X ep010110111011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110111011 : Branch 1 (-2931761639/4000000 : ℚ) vp01011011101 := by
  apply branch_checked idp010110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2931761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2933761639/2000000 : ℚ) by norm_num]
  exact coverp010110111011
theorem coverp01011011101 : Covers (-2931761639/4000000 : ℚ) vp01011011101 := join_branches bp010110111010 bp010110111011
private noncomputable def vp010110111001_0 : Blocks := edgeBlocks% "full/vectors/010110111001-V-0000.bin"
noncomputable def vp010110111001 : Blocks := vp010110111001_0
theorem coverp010110111001 : Covers (-2929761639/2000000 : ℚ) vp010110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110111000_0 : Blocks := edgeBlocks% "full/vectors/010110111000-V-0000.bin"
noncomputable def vp010110111000 : Blocks := vp010110111000_0
theorem coverp010110111000 : Covers (-2927761639/2000000 : ℚ) vp010110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011100_0 : Blocks := edgeBlocks% "full/vectors/01011011100-V-0000.bin"
noncomputable def vp01011011100 : Blocks := vp01011011100_0
private theorem bp010110111000 : Branch 0 (-2927761639/4000000 : ℚ) vp01011011100 := by
  apply branch_left_normalized (c:=vp010110111000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2927761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2927761639/2000000 : ℚ) by norm_num]
  exact coverp010110111000
private noncomputable def ep010110111001_0 : Blocks := edgeBlocks% "full/vectors/010110111001-E-0000.bin"
noncomputable def ep010110111001 : Blocks := ep010110111001_0
private theorem idp010110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011100.list =
    C ((2:ℤ)^105) * horner X vp010110111001.list + horner X ep010110111001.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110111001 : Branch 1 (-2927761639/4000000 : ℚ) vp01011011100 := by
  apply branch_checked idp010110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2927761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2929761639/2000000 : ℚ) by norm_num]
  exact coverp010110111001
theorem coverp01011011100 : Covers (-2927761639/4000000 : ℚ) vp01011011100 := join_branches bp010110111000 bp010110111001
private noncomputable def vp0101101110_0 : Blocks := edgeBlocks% "full/vectors/0101101110-V-0000.bin"
private noncomputable def vp0101101110_1 : Blocks := edgeBlocks% "full/vectors/0101101110-V-0001.bin"
noncomputable def vp0101101110 : Blocks := (Blocks.join vp0101101110_0 vp0101101110_1)
private theorem bp01011011100 : Branch 0 (-2927761639/8000000 : ℚ) vp0101101110 := by
  apply branch_left_normalized (c:=vp01011011100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2927761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2927761639/4000000 : ℚ) by norm_num]
  exact coverp01011011100
private noncomputable def ep01011011101_0 : Blocks := edgeBlocks% "full/vectors/01011011101-E-0000.bin"
private noncomputable def ep01011011101_1 : Blocks := edgeBlocks% "full/vectors/01011011101-E-0001.bin"
noncomputable def ep01011011101 : Blocks := (Blocks.join ep01011011101_0 ep01011011101_1)
private theorem idp01011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101110.list =
    C ((2:ℤ)^191) * horner X vp01011011101.list + horner X ep01011011101.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011011101 : Branch 1 (-2927761639/8000000 : ℚ) vp0101101110 := by
  apply branch_checked idp01011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2927761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2931761639/4000000 : ℚ) by norm_num]
  exact coverp01011011101
theorem coverp0101101110 : Covers (-2927761639/8000000 : ℚ) vp0101101110 := join_branches bp01011011100 bp01011011101
private noncomputable def vp010110111_0 : Blocks := edgeBlocks% "full/vectors/010110111-V-0000.bin"
private noncomputable def vp010110111_1 : Blocks := edgeBlocks% "full/vectors/010110111-V-0001.bin"
private noncomputable def vp010110111_2 : Blocks := edgeBlocks% "full/vectors/010110111-V-0002.bin"
noncomputable def vp010110111 : Blocks := (Blocks.join vp010110111_0 (Blocks.join vp010110111_1 vp010110111_2))
private theorem bp0101101110 : Branch 0 (-2927761639/16000000 : ℚ) vp010110111 := by
  apply branch_left_normalized (c:=vp0101101110) (k:=0) (m:=167) (by decide +kernel)
  rw [show 2*(-2927761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2927761639/8000000 : ℚ) by norm_num]
  exact coverp0101101110
private noncomputable def ep0101101111_0 : Blocks := edgeBlocks% "full/vectors/0101101111-E-0000.bin"
private noncomputable def ep0101101111_1 : Blocks := edgeBlocks% "full/vectors/0101101111-E-0001.bin"
private noncomputable def ep0101101111_2 : Blocks := edgeBlocks% "full/vectors/0101101111-E-0002.bin"
noncomputable def ep0101101111 : Blocks := (Blocks.join ep0101101111_0 (Blocks.join ep0101101111_1 ep0101101111_2))
private theorem idp0101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110111.list =
    C ((2:ℤ)^359) * horner X vp0101101111.list + horner X ep0101101111.list := by
  exact edge_identity (B := (2:ℤ)^568) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101101111 : Branch 1 (-2927761639/16000000 : ℚ) vp010110111 := by
  apply branch_checked idp0101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2927761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2935761639/8000000 : ℚ) by norm_num]
  exact coverp0101101111
theorem coverp010110111 : Covers (-2927761639/16000000 : ℚ) vp010110111 := join_branches bp0101101110 bp0101101111
private noncomputable def vp010110110111_0 : Blocks := edgeBlocks% "full/vectors/010110110111-V-0000.bin"
noncomputable def vp010110110111 : Blocks := vp010110110111_0
theorem coverp010110110111 : Covers (-2925761639/2000000 : ℚ) vp010110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110110110_0 : Blocks := edgeBlocks% "full/vectors/010110110110-V-0000.bin"
noncomputable def vp010110110110 : Blocks := vp010110110110_0
theorem coverp010110110110 : Covers (-2923761639/2000000 : ℚ) vp010110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011011_0 : Blocks := edgeBlocks% "full/vectors/01011011011-V-0000.bin"
noncomputable def vp01011011011 : Blocks := vp01011011011_0
private theorem bp010110110110 : Branch 0 (-2923761639/4000000 : ℚ) vp01011011011 := by
  apply branch_left_normalized (c:=vp010110110110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2923761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2923761639/2000000 : ℚ) by norm_num]
  exact coverp010110110110
private noncomputable def ep010110110111_0 : Blocks := edgeBlocks% "full/vectors/010110110111-E-0000.bin"
noncomputable def ep010110110111 : Blocks := ep010110110111_0
private theorem idp010110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011011.list =
    C ((2:ℤ)^105) * horner X vp010110110111.list + horner X ep010110110111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110110111 : Branch 1 (-2923761639/4000000 : ℚ) vp01011011011 := by
  apply branch_checked idp010110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2923761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2925761639/2000000 : ℚ) by norm_num]
  exact coverp010110110111
theorem coverp01011011011 : Covers (-2923761639/4000000 : ℚ) vp01011011011 := join_branches bp010110110110 bp010110110111
private noncomputable def vp010110110101_0 : Blocks := edgeBlocks% "full/vectors/010110110101-V-0000.bin"
noncomputable def vp010110110101 : Blocks := vp010110110101_0
theorem coverp010110110101 : Covers (-2921761639/2000000 : ℚ) vp010110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110110100_0 : Blocks := edgeBlocks% "full/vectors/010110110100-V-0000.bin"
noncomputable def vp010110110100 : Blocks := vp010110110100_0
theorem coverp010110110100 : Covers (-2919761639/2000000 : ℚ) vp010110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011010_0 : Blocks := edgeBlocks% "full/vectors/01011011010-V-0000.bin"
noncomputable def vp01011011010 : Blocks := vp01011011010_0
private theorem bp010110110100 : Branch 0 (-2919761639/4000000 : ℚ) vp01011011010 := by
  apply branch_left_normalized (c:=vp010110110100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2919761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2919761639/2000000 : ℚ) by norm_num]
  exact coverp010110110100
private noncomputable def ep010110110101_0 : Blocks := edgeBlocks% "full/vectors/010110110101-E-0000.bin"
noncomputable def ep010110110101 : Blocks := ep010110110101_0
private theorem idp010110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011010.list =
    C ((2:ℤ)^106) * horner X vp010110110101.list + horner X ep010110110101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110110101 : Branch 1 (-2919761639/4000000 : ℚ) vp01011011010 := by
  apply branch_checked idp010110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2919761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2921761639/2000000 : ℚ) by norm_num]
  exact coverp010110110101
theorem coverp01011011010 : Covers (-2919761639/4000000 : ℚ) vp01011011010 := join_branches bp010110110100 bp010110110101
private noncomputable def vp0101101101_0 : Blocks := edgeBlocks% "full/vectors/0101101101-V-0000.bin"
private noncomputable def vp0101101101_1 : Blocks := edgeBlocks% "full/vectors/0101101101-V-0001.bin"
noncomputable def vp0101101101 : Blocks := (Blocks.join vp0101101101_0 vp0101101101_1)
private theorem bp01011011010 : Branch 0 (-2919761639/8000000 : ℚ) vp0101101101 := by
  apply branch_left_normalized (c:=vp01011011010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2919761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2919761639/4000000 : ℚ) by norm_num]
  exact coverp01011011010
private noncomputable def ep01011011011_0 : Blocks := edgeBlocks% "full/vectors/01011011011-E-0000.bin"
private noncomputable def ep01011011011_1 : Blocks := edgeBlocks% "full/vectors/01011011011-E-0001.bin"
noncomputable def ep01011011011 : Blocks := (Blocks.join ep01011011011_0 ep01011011011_1)
private theorem idp01011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101101.list =
    C ((2:ℤ)^191) * horner X vp01011011011.list + horner X ep01011011011.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011011011 : Branch 1 (-2919761639/8000000 : ℚ) vp0101101101 := by
  apply branch_checked idp01011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2919761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2923761639/4000000 : ℚ) by norm_num]
  exact coverp01011011011
theorem coverp0101101101 : Covers (-2919761639/8000000 : ℚ) vp0101101101 := join_branches bp01011011010 bp01011011011
private noncomputable def vp010110110011_0 : Blocks := edgeBlocks% "full/vectors/010110110011-V-0000.bin"
noncomputable def vp010110110011 : Blocks := vp010110110011_0
theorem coverp010110110011 : Covers (-2917761639/2000000 : ℚ) vp010110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110110010_0 : Blocks := edgeBlocks% "full/vectors/010110110010-V-0000.bin"
noncomputable def vp010110110010 : Blocks := vp010110110010_0
theorem coverp010110110010 : Covers (-2915761639/2000000 : ℚ) vp010110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011001_0 : Blocks := edgeBlocks% "full/vectors/01011011001-V-0000.bin"
noncomputable def vp01011011001 : Blocks := vp01011011001_0
private theorem bp010110110010 : Branch 0 (-2915761639/4000000 : ℚ) vp01011011001 := by
  apply branch_left_normalized (c:=vp010110110010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2915761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2915761639/2000000 : ℚ) by norm_num]
  exact coverp010110110010
private noncomputable def ep010110110011_0 : Blocks := edgeBlocks% "full/vectors/010110110011-E-0000.bin"
noncomputable def ep010110110011 : Blocks := ep010110110011_0
private theorem idp010110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011001.list =
    C ((2:ℤ)^107) * horner X vp010110110011.list + horner X ep010110110011.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110110011 : Branch 1 (-2915761639/4000000 : ℚ) vp01011011001 := by
  apply branch_checked idp010110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2915761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2917761639/2000000 : ℚ) by norm_num]
  exact coverp010110110011
theorem coverp01011011001 : Covers (-2915761639/4000000 : ℚ) vp01011011001 := join_branches bp010110110010 bp010110110011
private noncomputable def vp010110110001_0 : Blocks := edgeBlocks% "full/vectors/010110110001-V-0000.bin"
noncomputable def vp010110110001 : Blocks := vp010110110001_0
theorem coverp010110110001 : Covers (-2913761639/2000000 : ℚ) vp010110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110110000_0 : Blocks := edgeBlocks% "full/vectors/010110110000-V-0000.bin"
noncomputable def vp010110110000 : Blocks := vp010110110000_0
theorem coverp010110110000 : Covers (-2911761639/2000000 : ℚ) vp010110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011011000_0 : Blocks := edgeBlocks% "full/vectors/01011011000-V-0000.bin"
noncomputable def vp01011011000 : Blocks := vp01011011000_0
private theorem bp010110110000 : Branch 0 (-2911761639/4000000 : ℚ) vp01011011000 := by
  apply branch_left_normalized (c:=vp010110110000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2911761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2911761639/2000000 : ℚ) by norm_num]
  exact coverp010110110000
private noncomputable def ep010110110001_0 : Blocks := edgeBlocks% "full/vectors/010110110001-E-0000.bin"
noncomputable def ep010110110001 : Blocks := ep010110110001_0
private theorem idp010110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011000.list =
    C ((2:ℤ)^106) * horner X vp010110110001.list + horner X ep010110110001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110110001 : Branch 1 (-2911761639/4000000 : ℚ) vp01011011000 := by
  apply branch_checked idp010110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2911761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2913761639/2000000 : ℚ) by norm_num]
  exact coverp010110110001
theorem coverp01011011000 : Covers (-2911761639/4000000 : ℚ) vp01011011000 := join_branches bp010110110000 bp010110110001
private noncomputable def vp0101101100_0 : Blocks := edgeBlocks% "full/vectors/0101101100-V-0000.bin"
private noncomputable def vp0101101100_1 : Blocks := edgeBlocks% "full/vectors/0101101100-V-0001.bin"
noncomputable def vp0101101100 : Blocks := (Blocks.join vp0101101100_0 vp0101101100_1)
private theorem bp01011011000 : Branch 0 (-2911761639/8000000 : ℚ) vp0101101100 := by
  apply branch_left_normalized (c:=vp01011011000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2911761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2911761639/4000000 : ℚ) by norm_num]
  exact coverp01011011000
private noncomputable def ep01011011001_0 : Blocks := edgeBlocks% "full/vectors/01011011001-E-0000.bin"
private noncomputable def ep01011011001_1 : Blocks := edgeBlocks% "full/vectors/01011011001-E-0001.bin"
noncomputable def ep01011011001 : Blocks := (Blocks.join ep01011011001_0 ep01011011001_1)
private theorem idp01011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101100.list =
    C ((2:ℤ)^191) * horner X vp01011011001.list + horner X ep01011011001.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011011001 : Branch 1 (-2911761639/8000000 : ℚ) vp0101101100 := by
  apply branch_checked idp01011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2911761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2915761639/4000000 : ℚ) by norm_num]
  exact coverp01011011001
theorem coverp0101101100 : Covers (-2911761639/8000000 : ℚ) vp0101101100 := join_branches bp01011011000 bp01011011001
private noncomputable def vp010110110_0 : Blocks := edgeBlocks% "full/vectors/010110110-V-0000.bin"
private noncomputable def vp010110110_1 : Blocks := edgeBlocks% "full/vectors/010110110-V-0001.bin"
private noncomputable def vp010110110_2 : Blocks := edgeBlocks% "full/vectors/010110110-V-0002.bin"
noncomputable def vp010110110 : Blocks := (Blocks.join vp010110110_0 (Blocks.join vp010110110_1 vp010110110_2))
private theorem bp0101101100 : Branch 0 (-2911761639/16000000 : ℚ) vp010110110 := by
  apply branch_left_normalized (c:=vp0101101100) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2911761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2911761639/8000000 : ℚ) by norm_num]
  exact coverp0101101100
private noncomputable def ep0101101101_0 : Blocks := edgeBlocks% "full/vectors/0101101101-E-0000.bin"
private noncomputable def ep0101101101_1 : Blocks := edgeBlocks% "full/vectors/0101101101-E-0001.bin"
private noncomputable def ep0101101101_2 : Blocks := edgeBlocks% "full/vectors/0101101101-E-0002.bin"
noncomputable def ep0101101101 : Blocks := (Blocks.join ep0101101101_0 (Blocks.join ep0101101101_1 ep0101101101_2))
private theorem idp0101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110110.list =
    C ((2:ℤ)^360) * horner X vp0101101101.list + horner X ep0101101101.list := by
  exact edge_identity (B := (2:ℤ)^569) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101101101 : Branch 1 (-2911761639/16000000 : ℚ) vp010110110 := by
  apply branch_checked idp0101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2911761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2919761639/8000000 : ℚ) by norm_num]
  exact coverp0101101101
theorem coverp010110110 : Covers (-2911761639/16000000 : ℚ) vp010110110 := join_branches bp0101101100 bp0101101101
private noncomputable def vp01011011_0 : Blocks := edgeBlocks% "full/vectors/01011011-V-0000.bin"
private noncomputable def vp01011011_1 : Blocks := edgeBlocks% "full/vectors/01011011-V-0001.bin"
private noncomputable def vp01011011_2 : Blocks := edgeBlocks% "full/vectors/01011011-V-0002.bin"
private noncomputable def vp01011011_3 : Blocks := edgeBlocks% "full/vectors/01011011-V-0003.bin"
private noncomputable def vp01011011_4 : Blocks := edgeBlocks% "full/vectors/01011011-V-0004.bin"
noncomputable def vp01011011 : Blocks := (Blocks.join (Blocks.join vp01011011_0 vp01011011_1) (Blocks.join vp01011011_2 (Blocks.join vp01011011_3 vp01011011_4)))
private theorem bp010110110 : Branch 0 (-2911761639/32000000 : ℚ) vp01011011 := by
  apply branch_left_normalized (c:=vp010110110) (k:=0) (m:=313) (by decide +kernel)
  rw [show 2*(-2911761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2911761639/16000000 : ℚ) by norm_num]
  exact coverp010110110
private noncomputable def ep010110111_0 : Blocks := edgeBlocks% "full/vectors/010110111-E-0000.bin"
private noncomputable def ep010110111_1 : Blocks := edgeBlocks% "full/vectors/010110111-E-0001.bin"
private noncomputable def ep010110111_2 : Blocks := edgeBlocks% "full/vectors/010110111-E-0002.bin"
private noncomputable def ep010110111_3 : Blocks := edgeBlocks% "full/vectors/010110111-E-0003.bin"
private noncomputable def ep010110111_4 : Blocks := edgeBlocks% "full/vectors/010110111-E-0004.bin"
noncomputable def ep010110111 : Blocks := (Blocks.join (Blocks.join ep010110111_0 ep010110111_1) (Blocks.join ep010110111_2 (Blocks.join ep010110111_3 ep010110111_4)))
private theorem idp010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011011.list =
    C ((2:ℤ)^694) * horner X vp010110111.list + horner X ep010110111.list := by
  exact edge_identity (B := (2:ℤ)^1011) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110111 : Branch 1 (-2911761639/32000000 : ℚ) vp01011011 := by
  apply branch_checked idp010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2911761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2927761639/16000000 : ℚ) by norm_num]
  exact coverp010110111
theorem coverp01011011 : Covers (-2911761639/32000000 : ℚ) vp01011011 := join_branches bp010110110 bp010110111
private noncomputable def vp010110101111_0 : Blocks := edgeBlocks% "full/vectors/010110101111-V-0000.bin"
noncomputable def vp010110101111 : Blocks := vp010110101111_0
theorem coverp010110101111 : Covers (-2909761639/2000000 : ℚ) vp010110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110101110_0 : Blocks := edgeBlocks% "full/vectors/010110101110-V-0000.bin"
noncomputable def vp010110101110 : Blocks := vp010110101110_0
theorem coverp010110101110 : Covers (-2907761639/2000000 : ℚ) vp010110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010111_0 : Blocks := edgeBlocks% "full/vectors/01011010111-V-0000.bin"
noncomputable def vp01011010111 : Blocks := vp01011010111_0
private theorem bp010110101110 : Branch 0 (-2907761639/4000000 : ℚ) vp01011010111 := by
  apply branch_left_normalized (c:=vp010110101110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2907761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2907761639/2000000 : ℚ) by norm_num]
  exact coverp010110101110
private noncomputable def ep010110101111_0 : Blocks := edgeBlocks% "full/vectors/010110101111-E-0000.bin"
noncomputable def ep010110101111 : Blocks := ep010110101111_0
private theorem idp010110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010111.list =
    C ((2:ℤ)^107) * horner X vp010110101111.list + horner X ep010110101111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110101111 : Branch 1 (-2907761639/4000000 : ℚ) vp01011010111 := by
  apply branch_checked idp010110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2907761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2909761639/2000000 : ℚ) by norm_num]
  exact coverp010110101111
theorem coverp01011010111 : Covers (-2907761639/4000000 : ℚ) vp01011010111 := join_branches bp010110101110 bp010110101111
private noncomputable def vp010110101101_0 : Blocks := edgeBlocks% "full/vectors/010110101101-V-0000.bin"
noncomputable def vp010110101101 : Blocks := vp010110101101_0
theorem coverp010110101101 : Covers (-2905761639/2000000 : ℚ) vp010110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110101100_0 : Blocks := edgeBlocks% "full/vectors/010110101100-V-0000.bin"
noncomputable def vp010110101100 : Blocks := vp010110101100_0
theorem coverp010110101100 : Covers (-2903761639/2000000 : ℚ) vp010110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010110_0 : Blocks := edgeBlocks% "full/vectors/01011010110-V-0000.bin"
noncomputable def vp01011010110 : Blocks := vp01011010110_0
private theorem bp010110101100 : Branch 0 (-2903761639/4000000 : ℚ) vp01011010110 := by
  apply branch_left_normalized (c:=vp010110101100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2903761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2903761639/2000000 : ℚ) by norm_num]
  exact coverp010110101100
private noncomputable def ep010110101101_0 : Blocks := edgeBlocks% "full/vectors/010110101101-E-0000.bin"
noncomputable def ep010110101101 : Blocks := ep010110101101_0
private theorem idp010110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010110.list =
    C ((2:ℤ)^106) * horner X vp010110101101.list + horner X ep010110101101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110101101 : Branch 1 (-2903761639/4000000 : ℚ) vp01011010110 := by
  apply branch_checked idp010110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2903761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2905761639/2000000 : ℚ) by norm_num]
  exact coverp010110101101
theorem coverp01011010110 : Covers (-2903761639/4000000 : ℚ) vp01011010110 := join_branches bp010110101100 bp010110101101
private noncomputable def vp0101101011_0 : Blocks := edgeBlocks% "full/vectors/0101101011-V-0000.bin"
private noncomputable def vp0101101011_1 : Blocks := edgeBlocks% "full/vectors/0101101011-V-0001.bin"
noncomputable def vp0101101011 : Blocks := (Blocks.join vp0101101011_0 vp0101101011_1)
private theorem bp01011010110 : Branch 0 (-2903761639/8000000 : ℚ) vp0101101011 := by
  apply branch_left_normalized (c:=vp01011010110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2903761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2903761639/4000000 : ℚ) by norm_num]
  exact coverp01011010110
private noncomputable def ep01011010111_0 : Blocks := edgeBlocks% "full/vectors/01011010111-E-0000.bin"
private noncomputable def ep01011010111_1 : Blocks := edgeBlocks% "full/vectors/01011010111-E-0001.bin"
noncomputable def ep01011010111 : Blocks := (Blocks.join ep01011010111_0 ep01011010111_1)
private theorem idp01011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101011.list =
    C ((2:ℤ)^191) * horner X vp01011010111.list + horner X ep01011010111.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011010111 : Branch 1 (-2903761639/8000000 : ℚ) vp0101101011 := by
  apply branch_checked idp01011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2903761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2907761639/4000000 : ℚ) by norm_num]
  exact coverp01011010111
theorem coverp0101101011 : Covers (-2903761639/8000000 : ℚ) vp0101101011 := join_branches bp01011010110 bp01011010111
private noncomputable def vp010110101011_0 : Blocks := edgeBlocks% "full/vectors/010110101011-V-0000.bin"
noncomputable def vp010110101011 : Blocks := vp010110101011_0
theorem coverp010110101011 : Covers (-2901761639/2000000 : ℚ) vp010110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110101010_0 : Blocks := edgeBlocks% "full/vectors/010110101010-V-0000.bin"
noncomputable def vp010110101010 : Blocks := vp010110101010_0
theorem coverp010110101010 : Covers (-2899761639/2000000 : ℚ) vp010110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010101_0 : Blocks := edgeBlocks% "full/vectors/01011010101-V-0000.bin"
noncomputable def vp01011010101 : Blocks := vp01011010101_0
private theorem bp010110101010 : Branch 0 (-2899761639/4000000 : ℚ) vp01011010101 := by
  apply branch_left_normalized (c:=vp010110101010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2899761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2899761639/2000000 : ℚ) by norm_num]
  exact coverp010110101010
private noncomputable def ep010110101011_0 : Blocks := edgeBlocks% "full/vectors/010110101011-E-0000.bin"
noncomputable def ep010110101011 : Blocks := ep010110101011_0
private theorem idp010110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010101.list =
    C ((2:ℤ)^106) * horner X vp010110101011.list + horner X ep010110101011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110101011 : Branch 1 (-2899761639/4000000 : ℚ) vp01011010101 := by
  apply branch_checked idp010110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2899761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2901761639/2000000 : ℚ) by norm_num]
  exact coverp010110101011
theorem coverp01011010101 : Covers (-2899761639/4000000 : ℚ) vp01011010101 := join_branches bp010110101010 bp010110101011
private noncomputable def vp010110101001_0 : Blocks := edgeBlocks% "full/vectors/010110101001-V-0000.bin"
noncomputable def vp010110101001 : Blocks := vp010110101001_0
theorem coverp010110101001 : Covers (-2897761639/2000000 : ℚ) vp010110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110101000_0 : Blocks := edgeBlocks% "full/vectors/010110101000-V-0000.bin"
noncomputable def vp010110101000 : Blocks := vp010110101000_0
theorem coverp010110101000 : Covers (-2895761639/2000000 : ℚ) vp010110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010100_0 : Blocks := edgeBlocks% "full/vectors/01011010100-V-0000.bin"
noncomputable def vp01011010100 : Blocks := vp01011010100_0
private theorem bp010110101000 : Branch 0 (-2895761639/4000000 : ℚ) vp01011010100 := by
  apply branch_left_normalized (c:=vp010110101000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2895761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2895761639/2000000 : ℚ) by norm_num]
  exact coverp010110101000
private noncomputable def ep010110101001_0 : Blocks := edgeBlocks% "full/vectors/010110101001-E-0000.bin"
noncomputable def ep010110101001 : Blocks := ep010110101001_0
private theorem idp010110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010100.list =
    C ((2:ℤ)^107) * horner X vp010110101001.list + horner X ep010110101001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110101001 : Branch 1 (-2895761639/4000000 : ℚ) vp01011010100 := by
  apply branch_checked idp010110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2895761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2897761639/2000000 : ℚ) by norm_num]
  exact coverp010110101001
theorem coverp01011010100 : Covers (-2895761639/4000000 : ℚ) vp01011010100 := join_branches bp010110101000 bp010110101001
private noncomputable def vp0101101010_0 : Blocks := edgeBlocks% "full/vectors/0101101010-V-0000.bin"
private noncomputable def vp0101101010_1 : Blocks := edgeBlocks% "full/vectors/0101101010-V-0001.bin"
noncomputable def vp0101101010 : Blocks := (Blocks.join vp0101101010_0 vp0101101010_1)
private theorem bp01011010100 : Branch 0 (-2895761639/8000000 : ℚ) vp0101101010 := by
  apply branch_left_normalized (c:=vp01011010100) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2895761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2895761639/4000000 : ℚ) by norm_num]
  exact coverp01011010100
private noncomputable def ep01011010101_0 : Blocks := edgeBlocks% "full/vectors/01011010101-E-0000.bin"
private noncomputable def ep01011010101_1 : Blocks := edgeBlocks% "full/vectors/01011010101-E-0001.bin"
noncomputable def ep01011010101 : Blocks := (Blocks.join ep01011010101_0 ep01011010101_1)
private theorem idp01011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101010.list =
    C ((2:ℤ)^192) * horner X vp01011010101.list + horner X ep01011010101.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011010101 : Branch 1 (-2895761639/8000000 : ℚ) vp0101101010 := by
  apply branch_checked idp01011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2895761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2899761639/4000000 : ℚ) by norm_num]
  exact coverp01011010101
theorem coverp0101101010 : Covers (-2895761639/8000000 : ℚ) vp0101101010 := join_branches bp01011010100 bp01011010101
private noncomputable def vp010110101_0 : Blocks := edgeBlocks% "full/vectors/010110101-V-0000.bin"
private noncomputable def vp010110101_1 : Blocks := edgeBlocks% "full/vectors/010110101-V-0001.bin"
private noncomputable def vp010110101_2 : Blocks := edgeBlocks% "full/vectors/010110101-V-0002.bin"
noncomputable def vp010110101 : Blocks := (Blocks.join vp010110101_0 (Blocks.join vp010110101_1 vp010110101_2))
private theorem bp0101101010 : Branch 0 (-2895761639/16000000 : ℚ) vp010110101 := by
  apply branch_left_normalized (c:=vp0101101010) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2895761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2895761639/8000000 : ℚ) by norm_num]
  exact coverp0101101010
private noncomputable def ep0101101011_0 : Blocks := edgeBlocks% "full/vectors/0101101011-E-0000.bin"
private noncomputable def ep0101101011_1 : Blocks := edgeBlocks% "full/vectors/0101101011-E-0001.bin"
private noncomputable def ep0101101011_2 : Blocks := edgeBlocks% "full/vectors/0101101011-E-0002.bin"
noncomputable def ep0101101011 : Blocks := (Blocks.join ep0101101011_0 (Blocks.join ep0101101011_1 ep0101101011_2))
private theorem idp0101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110101.list =
    C ((2:ℤ)^360) * horner X vp0101101011.list + horner X ep0101101011.list := by
  exact edge_identity (B := (2:ℤ)^570) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101101011 : Branch 1 (-2895761639/16000000 : ℚ) vp010110101 := by
  apply branch_checked idp0101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2895761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2903761639/8000000 : ℚ) by norm_num]
  exact coverp0101101011
theorem coverp010110101 : Covers (-2895761639/16000000 : ℚ) vp010110101 := join_branches bp0101101010 bp0101101011
private noncomputable def vp010110100111_0 : Blocks := edgeBlocks% "full/vectors/010110100111-V-0000.bin"
noncomputable def vp010110100111 : Blocks := vp010110100111_0
theorem coverp010110100111 : Covers (-2893761639/2000000 : ℚ) vp010110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110100110_0 : Blocks := edgeBlocks% "full/vectors/010110100110-V-0000.bin"
noncomputable def vp010110100110 : Blocks := vp010110100110_0
theorem coverp010110100110 : Covers (-2891761639/2000000 : ℚ) vp010110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010011_0 : Blocks := edgeBlocks% "full/vectors/01011010011-V-0000.bin"
noncomputable def vp01011010011 : Blocks := vp01011010011_0
private theorem bp010110100110 : Branch 0 (-2891761639/4000000 : ℚ) vp01011010011 := by
  apply branch_left_normalized (c:=vp010110100110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2891761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2891761639/2000000 : ℚ) by norm_num]
  exact coverp010110100110
private noncomputable def ep010110100111_0 : Blocks := edgeBlocks% "full/vectors/010110100111-E-0000.bin"
noncomputable def ep010110100111 : Blocks := ep010110100111_0
private theorem idp010110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010011.list =
    C ((2:ℤ)^107) * horner X vp010110100111.list + horner X ep010110100111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110100111 : Branch 1 (-2891761639/4000000 : ℚ) vp01011010011 := by
  apply branch_checked idp010110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2891761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2893761639/2000000 : ℚ) by norm_num]
  exact coverp010110100111
theorem coverp01011010011 : Covers (-2891761639/4000000 : ℚ) vp01011010011 := join_branches bp010110100110 bp010110100111
private noncomputable def vp010110100101_0 : Blocks := edgeBlocks% "full/vectors/010110100101-V-0000.bin"
noncomputable def vp010110100101 : Blocks := vp010110100101_0
theorem coverp010110100101 : Covers (-2889761639/2000000 : ℚ) vp010110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110100100_0 : Blocks := edgeBlocks% "full/vectors/010110100100-V-0000.bin"
noncomputable def vp010110100100 : Blocks := vp010110100100_0
theorem coverp010110100100 : Covers (-2887761639/2000000 : ℚ) vp010110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010010_0 : Blocks := edgeBlocks% "full/vectors/01011010010-V-0000.bin"
noncomputable def vp01011010010 : Blocks := vp01011010010_0
private theorem bp010110100100 : Branch 0 (-2887761639/4000000 : ℚ) vp01011010010 := by
  apply branch_left_normalized (c:=vp010110100100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2887761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2887761639/2000000 : ℚ) by norm_num]
  exact coverp010110100100
private noncomputable def ep010110100101_0 : Blocks := edgeBlocks% "full/vectors/010110100101-E-0000.bin"
noncomputable def ep010110100101 : Blocks := ep010110100101_0
private theorem idp010110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010010.list =
    C ((2:ℤ)^106) * horner X vp010110100101.list + horner X ep010110100101.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110100101 : Branch 1 (-2887761639/4000000 : ℚ) vp01011010010 := by
  apply branch_checked idp010110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2887761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2889761639/2000000 : ℚ) by norm_num]
  exact coverp010110100101
theorem coverp01011010010 : Covers (-2887761639/4000000 : ℚ) vp01011010010 := join_branches bp010110100100 bp010110100101
private noncomputable def vp0101101001_0 : Blocks := edgeBlocks% "full/vectors/0101101001-V-0000.bin"
private noncomputable def vp0101101001_1 : Blocks := edgeBlocks% "full/vectors/0101101001-V-0001.bin"
noncomputable def vp0101101001 : Blocks := (Blocks.join vp0101101001_0 vp0101101001_1)
private theorem bp01011010010 : Branch 0 (-2887761639/8000000 : ℚ) vp0101101001 := by
  apply branch_left_normalized (c:=vp01011010010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2887761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2887761639/4000000 : ℚ) by norm_num]
  exact coverp01011010010
private noncomputable def ep01011010011_0 : Blocks := edgeBlocks% "full/vectors/01011010011-E-0000.bin"
private noncomputable def ep01011010011_1 : Blocks := edgeBlocks% "full/vectors/01011010011-E-0001.bin"
noncomputable def ep01011010011 : Blocks := (Blocks.join ep01011010011_0 ep01011010011_1)
private theorem idp01011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101001.list =
    C ((2:ℤ)^192) * horner X vp01011010011.list + horner X ep01011010011.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011010011 : Branch 1 (-2887761639/8000000 : ℚ) vp0101101001 := by
  apply branch_checked idp01011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2887761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2891761639/4000000 : ℚ) by norm_num]
  exact coverp01011010011
theorem coverp0101101001 : Covers (-2887761639/8000000 : ℚ) vp0101101001 := join_branches bp01011010010 bp01011010011
private noncomputable def vp010110100011_0 : Blocks := edgeBlocks% "full/vectors/010110100011-V-0000.bin"
noncomputable def vp010110100011 : Blocks := vp010110100011_0
theorem coverp010110100011 : Covers (-2885761639/2000000 : ℚ) vp010110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110100010_0 : Blocks := edgeBlocks% "full/vectors/010110100010-V-0000.bin"
noncomputable def vp010110100010 : Blocks := vp010110100010_0
theorem coverp010110100010 : Covers (-2883761639/2000000 : ℚ) vp010110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010001_0 : Blocks := edgeBlocks% "full/vectors/01011010001-V-0000.bin"
noncomputable def vp01011010001 : Blocks := vp01011010001_0
private theorem bp010110100010 : Branch 0 (-2883761639/4000000 : ℚ) vp01011010001 := by
  apply branch_left_normalized (c:=vp010110100010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2883761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2883761639/2000000 : ℚ) by norm_num]
  exact coverp010110100010
private noncomputable def ep010110100011_0 : Blocks := edgeBlocks% "full/vectors/010110100011-E-0000.bin"
noncomputable def ep010110100011 : Blocks := ep010110100011_0
private theorem idp010110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010001.list =
    C ((2:ℤ)^106) * horner X vp010110100011.list + horner X ep010110100011.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110100011 : Branch 1 (-2883761639/4000000 : ℚ) vp01011010001 := by
  apply branch_checked idp010110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2883761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2885761639/2000000 : ℚ) by norm_num]
  exact coverp010110100011
theorem coverp01011010001 : Covers (-2883761639/4000000 : ℚ) vp01011010001 := join_branches bp010110100010 bp010110100011
private noncomputable def vp010110100001_0 : Blocks := edgeBlocks% "full/vectors/010110100001-V-0000.bin"
noncomputable def vp010110100001 : Blocks := vp010110100001_0
theorem coverp010110100001 : Covers (-2881761639/2000000 : ℚ) vp010110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110100000_0 : Blocks := edgeBlocks% "full/vectors/010110100000-V-0000.bin"
noncomputable def vp010110100000 : Blocks := vp010110100000_0
theorem coverp010110100000 : Covers (-2879761639/2000000 : ℚ) vp010110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011010000_0 : Blocks := edgeBlocks% "full/vectors/01011010000-V-0000.bin"
noncomputable def vp01011010000 : Blocks := vp01011010000_0
private theorem bp010110100000 : Branch 0 (-2879761639/4000000 : ℚ) vp01011010000 := by
  apply branch_left_normalized (c:=vp010110100000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2879761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2879761639/2000000 : ℚ) by norm_num]
  exact coverp010110100000
private noncomputable def ep010110100001_0 : Blocks := edgeBlocks% "full/vectors/010110100001-E-0000.bin"
noncomputable def ep010110100001 : Blocks := ep010110100001_0
private theorem idp010110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010000.list =
    C ((2:ℤ)^107) * horner X vp010110100001.list + horner X ep010110100001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110100001 : Branch 1 (-2879761639/4000000 : ℚ) vp01011010000 := by
  apply branch_checked idp010110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2879761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2881761639/2000000 : ℚ) by norm_num]
  exact coverp010110100001
theorem coverp01011010000 : Covers (-2879761639/4000000 : ℚ) vp01011010000 := join_branches bp010110100000 bp010110100001
private noncomputable def vp0101101000_0 : Blocks := edgeBlocks% "full/vectors/0101101000-V-0000.bin"
private noncomputable def vp0101101000_1 : Blocks := edgeBlocks% "full/vectors/0101101000-V-0001.bin"
noncomputable def vp0101101000 : Blocks := (Blocks.join vp0101101000_0 vp0101101000_1)
private theorem bp01011010000 : Branch 0 (-2879761639/8000000 : ℚ) vp0101101000 := by
  apply branch_left_normalized (c:=vp01011010000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2879761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2879761639/4000000 : ℚ) by norm_num]
  exact coverp01011010000
private noncomputable def ep01011010001_0 : Blocks := edgeBlocks% "full/vectors/01011010001-E-0000.bin"
private noncomputable def ep01011010001_1 : Blocks := edgeBlocks% "full/vectors/01011010001-E-0001.bin"
noncomputable def ep01011010001 : Blocks := (Blocks.join ep01011010001_0 ep01011010001_1)
private theorem idp01011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101000.list =
    C ((2:ℤ)^192) * horner X vp01011010001.list + horner X ep01011010001.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011010001 : Branch 1 (-2879761639/8000000 : ℚ) vp0101101000 := by
  apply branch_checked idp01011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2879761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2883761639/4000000 : ℚ) by norm_num]
  exact coverp01011010001
theorem coverp0101101000 : Covers (-2879761639/8000000 : ℚ) vp0101101000 := join_branches bp01011010000 bp01011010001
private noncomputable def vp010110100_0 : Blocks := edgeBlocks% "full/vectors/010110100-V-0000.bin"
private noncomputable def vp010110100_1 : Blocks := edgeBlocks% "full/vectors/010110100-V-0001.bin"
private noncomputable def vp010110100_2 : Blocks := edgeBlocks% "full/vectors/010110100-V-0002.bin"
noncomputable def vp010110100 : Blocks := (Blocks.join vp010110100_0 (Blocks.join vp010110100_1 vp010110100_2))
private theorem bp0101101000 : Branch 0 (-2879761639/16000000 : ℚ) vp010110100 := by
  apply branch_left_normalized (c:=vp0101101000) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2879761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2879761639/8000000 : ℚ) by norm_num]
  exact coverp0101101000
private noncomputable def ep0101101001_0 : Blocks := edgeBlocks% "full/vectors/0101101001-E-0000.bin"
private noncomputable def ep0101101001_1 : Blocks := edgeBlocks% "full/vectors/0101101001-E-0001.bin"
private noncomputable def ep0101101001_2 : Blocks := edgeBlocks% "full/vectors/0101101001-E-0002.bin"
noncomputable def ep0101101001 : Blocks := (Blocks.join ep0101101001_0 (Blocks.join ep0101101001_1 ep0101101001_2))
private theorem idp0101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110100.list =
    C ((2:ℤ)^361) * horner X vp0101101001.list + horner X ep0101101001.list := by
  exact edge_identity (B := (2:ℤ)^571) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101101001 : Branch 1 (-2879761639/16000000 : ℚ) vp010110100 := by
  apply branch_checked idp0101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2879761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2887761639/8000000 : ℚ) by norm_num]
  exact coverp0101101001
theorem coverp010110100 : Covers (-2879761639/16000000 : ℚ) vp010110100 := join_branches bp0101101000 bp0101101001
private noncomputable def vp01011010_0 : Blocks := edgeBlocks% "full/vectors/01011010-V-0000.bin"
private noncomputable def vp01011010_1 : Blocks := edgeBlocks% "full/vectors/01011010-V-0001.bin"
private noncomputable def vp01011010_2 : Blocks := edgeBlocks% "full/vectors/01011010-V-0002.bin"
private noncomputable def vp01011010_3 : Blocks := edgeBlocks% "full/vectors/01011010-V-0003.bin"
private noncomputable def vp01011010_4 : Blocks := edgeBlocks% "full/vectors/01011010-V-0004.bin"
noncomputable def vp01011010 : Blocks := (Blocks.join (Blocks.join vp01011010_0 vp01011010_1) (Blocks.join vp01011010_2 (Blocks.join vp01011010_3 vp01011010_4)))
private theorem bp010110100 : Branch 0 (-2879761639/32000000 : ℚ) vp01011010 := by
  apply branch_left_normalized (c:=vp010110100) (k:=0) (m:=314) (by decide +kernel)
  rw [show 2*(-2879761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2879761639/16000000 : ℚ) by norm_num]
  exact coverp010110100
private noncomputable def ep010110101_0 : Blocks := edgeBlocks% "full/vectors/010110101-E-0000.bin"
private noncomputable def ep010110101_1 : Blocks := edgeBlocks% "full/vectors/010110101-E-0001.bin"
private noncomputable def ep010110101_2 : Blocks := edgeBlocks% "full/vectors/010110101-E-0002.bin"
private noncomputable def ep010110101_3 : Blocks := edgeBlocks% "full/vectors/010110101-E-0003.bin"
private noncomputable def ep010110101_4 : Blocks := edgeBlocks% "full/vectors/010110101-E-0004.bin"
noncomputable def ep010110101 : Blocks := (Blocks.join (Blocks.join ep010110101_0 ep010110101_1) (Blocks.join ep010110101_2 (Blocks.join ep010110101_3 ep010110101_4)))
private theorem idp010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011010.list =
    C ((2:ℤ)^697) * horner X vp010110101.list + horner X ep010110101.list := by
  exact edge_identity (B := (2:ℤ)^1016) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110101 : Branch 1 (-2879761639/32000000 : ℚ) vp01011010 := by
  apply branch_checked idp010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2879761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2895761639/16000000 : ℚ) by norm_num]
  exact coverp010110101
theorem coverp01011010 : Covers (-2879761639/32000000 : ℚ) vp01011010 := join_branches bp010110100 bp010110101
private noncomputable def vp0101101_0 : Blocks := edgeBlocks% "full/vectors/0101101-V-0000.bin"
private noncomputable def vp0101101_1 : Blocks := edgeBlocks% "full/vectors/0101101-V-0001.bin"
private noncomputable def vp0101101_2 : Blocks := edgeBlocks% "full/vectors/0101101-V-0002.bin"
private noncomputable def vp0101101_3 : Blocks := edgeBlocks% "full/vectors/0101101-V-0003.bin"
private noncomputable def vp0101101_4 : Blocks := edgeBlocks% "full/vectors/0101101-V-0004.bin"
private noncomputable def vp0101101_5 : Blocks := edgeBlocks% "full/vectors/0101101-V-0005.bin"
private noncomputable def vp0101101_6 : Blocks := edgeBlocks% "full/vectors/0101101-V-0006.bin"
private noncomputable def vp0101101_7 : Blocks := edgeBlocks% "full/vectors/0101101-V-0007.bin"
private noncomputable def vp0101101_8 : Blocks := edgeBlocks% "full/vectors/0101101-V-0008.bin"
private noncomputable def vp0101101_9 : Blocks := edgeBlocks% "full/vectors/0101101-V-0009.bin"
noncomputable def vp0101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101101_0 vp0101101_1) (Blocks.join vp0101101_2 (Blocks.join vp0101101_3 vp0101101_4))) (Blocks.join (Blocks.join vp0101101_5 vp0101101_6) (Blocks.join vp0101101_7 (Blocks.join vp0101101_8 vp0101101_9))))
private theorem bp01011010 : Branch 0 (-2879761639/64000000 : ℚ) vp0101101 := by
  apply branch_left_normalized (c:=vp01011010) (k:=0) (m:=604) (by decide +kernel)
  rw [show 2*(-2879761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2879761639/32000000 : ℚ) by norm_num]
  exact coverp01011010
private noncomputable def ep01011011_0 : Blocks := edgeBlocks% "full/vectors/01011011-E-0000.bin"
private noncomputable def ep01011011_1 : Blocks := edgeBlocks% "full/vectors/01011011-E-0001.bin"
private noncomputable def ep01011011_2 : Blocks := edgeBlocks% "full/vectors/01011011-E-0002.bin"
private noncomputable def ep01011011_3 : Blocks := edgeBlocks% "full/vectors/01011011-E-0003.bin"
private noncomputable def ep01011011_4 : Blocks := edgeBlocks% "full/vectors/01011011-E-0004.bin"
private noncomputable def ep01011011_5 : Blocks := edgeBlocks% "full/vectors/01011011-E-0005.bin"
private noncomputable def ep01011011_6 : Blocks := edgeBlocks% "full/vectors/01011011-E-0006.bin"
private noncomputable def ep01011011_7 : Blocks := edgeBlocks% "full/vectors/01011011-E-0007.bin"
private noncomputable def ep01011011_8 : Blocks := edgeBlocks% "full/vectors/01011011-E-0008.bin"
private noncomputable def ep01011011_9 : Blocks := edgeBlocks% "full/vectors/01011011-E-0009.bin"
noncomputable def ep01011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01011011_0 ep01011011_1) (Blocks.join ep01011011_2 (Blocks.join ep01011011_3 ep01011011_4))) (Blocks.join (Blocks.join ep01011011_5 ep01011011_6) (Blocks.join ep01011011_7 (Blocks.join ep01011011_8 ep01011011_9))))
private theorem idp01011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101101.list =
    C ((2:ℤ)^1360) * horner X vp01011011.list + horner X ep01011011.list := by
  exact edge_identity (B := (2:ℤ)^1895) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011011 : Branch 1 (-2879761639/64000000 : ℚ) vp0101101 := by
  apply branch_checked idp01011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2879761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2911761639/32000000 : ℚ) by norm_num]
  exact coverp01011011
theorem coverp0101101 : Covers (-2879761639/64000000 : ℚ) vp0101101 := join_branches bp01011010 bp01011011
private noncomputable def vp010110011111_0 : Blocks := edgeBlocks% "full/vectors/010110011111-V-0000.bin"
noncomputable def vp010110011111 : Blocks := vp010110011111_0
theorem coverp010110011111 : Covers (-2877761639/2000000 : ℚ) vp010110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110011110_0 : Blocks := edgeBlocks% "full/vectors/010110011110-V-0000.bin"
noncomputable def vp010110011110 : Blocks := vp010110011110_0
theorem coverp010110011110 : Covers (-2875761639/2000000 : ℚ) vp010110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001111_0 : Blocks := edgeBlocks% "full/vectors/01011001111-V-0000.bin"
noncomputable def vp01011001111 : Blocks := vp01011001111_0
private theorem bp010110011110 : Branch 0 (-2875761639/4000000 : ℚ) vp01011001111 := by
  apply branch_left_normalized (c:=vp010110011110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2875761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2875761639/2000000 : ℚ) by norm_num]
  exact coverp010110011110
private noncomputable def ep010110011111_0 : Blocks := edgeBlocks% "full/vectors/010110011111-E-0000.bin"
noncomputable def ep010110011111 : Blocks := ep010110011111_0
private theorem idp010110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001111.list =
    C ((2:ℤ)^106) * horner X vp010110011111.list + horner X ep010110011111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110011111 : Branch 1 (-2875761639/4000000 : ℚ) vp01011001111 := by
  apply branch_checked idp010110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2875761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2877761639/2000000 : ℚ) by norm_num]
  exact coverp010110011111
theorem coverp01011001111 : Covers (-2875761639/4000000 : ℚ) vp01011001111 := join_branches bp010110011110 bp010110011111
private noncomputable def vp010110011101_0 : Blocks := edgeBlocks% "full/vectors/010110011101-V-0000.bin"
noncomputable def vp010110011101 : Blocks := vp010110011101_0
theorem coverp010110011101 : Covers (-2873761639/2000000 : ℚ) vp010110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110011100_0 : Blocks := edgeBlocks% "full/vectors/010110011100-V-0000.bin"
noncomputable def vp010110011100 : Blocks := vp010110011100_0
theorem coverp010110011100 : Covers (-2871761639/2000000 : ℚ) vp010110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001110_0 : Blocks := edgeBlocks% "full/vectors/01011001110-V-0000.bin"
noncomputable def vp01011001110 : Blocks := vp01011001110_0
private theorem bp010110011100 : Branch 0 (-2871761639/4000000 : ℚ) vp01011001110 := by
  apply branch_left_normalized (c:=vp010110011100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2871761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2871761639/2000000 : ℚ) by norm_num]
  exact coverp010110011100
private noncomputable def ep010110011101_0 : Blocks := edgeBlocks% "full/vectors/010110011101-E-0000.bin"
noncomputable def ep010110011101 : Blocks := ep010110011101_0
private theorem idp010110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001110.list =
    C ((2:ℤ)^106) * horner X vp010110011101.list + horner X ep010110011101.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110011101 : Branch 1 (-2871761639/4000000 : ℚ) vp01011001110 := by
  apply branch_checked idp010110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2871761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2873761639/2000000 : ℚ) by norm_num]
  exact coverp010110011101
theorem coverp01011001110 : Covers (-2871761639/4000000 : ℚ) vp01011001110 := join_branches bp010110011100 bp010110011101
private noncomputable def vp0101100111_0 : Blocks := edgeBlocks% "full/vectors/0101100111-V-0000.bin"
private noncomputable def vp0101100111_1 : Blocks := edgeBlocks% "full/vectors/0101100111-V-0001.bin"
noncomputable def vp0101100111 : Blocks := (Blocks.join vp0101100111_0 vp0101100111_1)
private theorem bp01011001110 : Branch 0 (-2871761639/8000000 : ℚ) vp0101100111 := by
  apply branch_left_normalized (c:=vp01011001110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2871761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2871761639/4000000 : ℚ) by norm_num]
  exact coverp01011001110
private noncomputable def ep01011001111_0 : Blocks := edgeBlocks% "full/vectors/01011001111-E-0000.bin"
private noncomputable def ep01011001111_1 : Blocks := edgeBlocks% "full/vectors/01011001111-E-0001.bin"
noncomputable def ep01011001111 : Blocks := (Blocks.join ep01011001111_0 ep01011001111_1)
private theorem idp01011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100111.list =
    C ((2:ℤ)^192) * horner X vp01011001111.list + horner X ep01011001111.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011001111 : Branch 1 (-2871761639/8000000 : ℚ) vp0101100111 := by
  apply branch_checked idp01011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2871761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2875761639/4000000 : ℚ) by norm_num]
  exact coverp01011001111
theorem coverp0101100111 : Covers (-2871761639/8000000 : ℚ) vp0101100111 := join_branches bp01011001110 bp01011001111
private noncomputable def vp010110011011_0 : Blocks := edgeBlocks% "full/vectors/010110011011-V-0000.bin"
noncomputable def vp010110011011 : Blocks := vp010110011011_0
theorem coverp010110011011 : Covers (-2869761639/2000000 : ℚ) vp010110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110011010_0 : Blocks := edgeBlocks% "full/vectors/010110011010-V-0000.bin"
noncomputable def vp010110011010 : Blocks := vp010110011010_0
theorem coverp010110011010 : Covers (-2867761639/2000000 : ℚ) vp010110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001101_0 : Blocks := edgeBlocks% "full/vectors/01011001101-V-0000.bin"
noncomputable def vp01011001101 : Blocks := vp01011001101_0
private theorem bp010110011010 : Branch 0 (-2867761639/4000000 : ℚ) vp01011001101 := by
  apply branch_left_normalized (c:=vp010110011010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2867761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2867761639/2000000 : ℚ) by norm_num]
  exact coverp010110011010
private noncomputable def ep010110011011_0 : Blocks := edgeBlocks% "full/vectors/010110011011-E-0000.bin"
noncomputable def ep010110011011 : Blocks := ep010110011011_0
private theorem idp010110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001101.list =
    C ((2:ℤ)^106) * horner X vp010110011011.list + horner X ep010110011011.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110011011 : Branch 1 (-2867761639/4000000 : ℚ) vp01011001101 := by
  apply branch_checked idp010110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2867761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2869761639/2000000 : ℚ) by norm_num]
  exact coverp010110011011
theorem coverp01011001101 : Covers (-2867761639/4000000 : ℚ) vp01011001101 := join_branches bp010110011010 bp010110011011
private noncomputable def vp010110011001_0 : Blocks := edgeBlocks% "full/vectors/010110011001-V-0000.bin"
noncomputable def vp010110011001 : Blocks := vp010110011001_0
theorem coverp010110011001 : Covers (-2865761639/2000000 : ℚ) vp010110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110011000_0 : Blocks := edgeBlocks% "full/vectors/010110011000-V-0000.bin"
noncomputable def vp010110011000 : Blocks := vp010110011000_0
theorem coverp010110011000 : Covers (-2863761639/2000000 : ℚ) vp010110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001100_0 : Blocks := edgeBlocks% "full/vectors/01011001100-V-0000.bin"
noncomputable def vp01011001100 : Blocks := vp01011001100_0
private theorem bp010110011000 : Branch 0 (-2863761639/4000000 : ℚ) vp01011001100 := by
  apply branch_left_normalized (c:=vp010110011000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2863761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2863761639/2000000 : ℚ) by norm_num]
  exact coverp010110011000
private noncomputable def ep010110011001_0 : Blocks := edgeBlocks% "full/vectors/010110011001-E-0000.bin"
noncomputable def ep010110011001 : Blocks := ep010110011001_0
private theorem idp010110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001100.list =
    C ((2:ℤ)^106) * horner X vp010110011001.list + horner X ep010110011001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110011001 : Branch 1 (-2863761639/4000000 : ℚ) vp01011001100 := by
  apply branch_checked idp010110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2863761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2865761639/2000000 : ℚ) by norm_num]
  exact coverp010110011001
theorem coverp01011001100 : Covers (-2863761639/4000000 : ℚ) vp01011001100 := join_branches bp010110011000 bp010110011001
private noncomputable def vp0101100110_0 : Blocks := edgeBlocks% "full/vectors/0101100110-V-0000.bin"
private noncomputable def vp0101100110_1 : Blocks := edgeBlocks% "full/vectors/0101100110-V-0001.bin"
noncomputable def vp0101100110 : Blocks := (Blocks.join vp0101100110_0 vp0101100110_1)
private theorem bp01011001100 : Branch 0 (-2863761639/8000000 : ℚ) vp0101100110 := by
  apply branch_left_normalized (c:=vp01011001100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2863761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2863761639/4000000 : ℚ) by norm_num]
  exact coverp01011001100
private noncomputable def ep01011001101_0 : Blocks := edgeBlocks% "full/vectors/01011001101-E-0000.bin"
private noncomputable def ep01011001101_1 : Blocks := edgeBlocks% "full/vectors/01011001101-E-0001.bin"
noncomputable def ep01011001101 : Blocks := (Blocks.join ep01011001101_0 ep01011001101_1)
private theorem idp01011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100110.list =
    C ((2:ℤ)^192) * horner X vp01011001101.list + horner X ep01011001101.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011001101 : Branch 1 (-2863761639/8000000 : ℚ) vp0101100110 := by
  apply branch_checked idp01011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2863761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2867761639/4000000 : ℚ) by norm_num]
  exact coverp01011001101
theorem coverp0101100110 : Covers (-2863761639/8000000 : ℚ) vp0101100110 := join_branches bp01011001100 bp01011001101
private noncomputable def vp010110011_0 : Blocks := edgeBlocks% "full/vectors/010110011-V-0000.bin"
private noncomputable def vp010110011_1 : Blocks := edgeBlocks% "full/vectors/010110011-V-0001.bin"
private noncomputable def vp010110011_2 : Blocks := edgeBlocks% "full/vectors/010110011-V-0002.bin"
noncomputable def vp010110011 : Blocks := (Blocks.join vp010110011_0 (Blocks.join vp010110011_1 vp010110011_2))
private theorem bp0101100110 : Branch 0 (-2863761639/16000000 : ℚ) vp010110011 := by
  apply branch_left_normalized (c:=vp0101100110) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2863761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2863761639/8000000 : ℚ) by norm_num]
  exact coverp0101100110
private noncomputable def ep0101100111_0 : Blocks := edgeBlocks% "full/vectors/0101100111-E-0000.bin"
private noncomputable def ep0101100111_1 : Blocks := edgeBlocks% "full/vectors/0101100111-E-0001.bin"
private noncomputable def ep0101100111_2 : Blocks := edgeBlocks% "full/vectors/0101100111-E-0002.bin"
noncomputable def ep0101100111 : Blocks := (Blocks.join ep0101100111_0 (Blocks.join ep0101100111_1 ep0101100111_2))
private theorem idp0101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110011.list =
    C ((2:ℤ)^362) * horner X vp0101100111.list + horner X ep0101100111.list := by
  exact edge_identity (B := (2:ℤ)^572) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101100111 : Branch 1 (-2863761639/16000000 : ℚ) vp010110011 := by
  apply branch_checked idp0101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2863761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2871761639/8000000 : ℚ) by norm_num]
  exact coverp0101100111
theorem coverp010110011 : Covers (-2863761639/16000000 : ℚ) vp010110011 := join_branches bp0101100110 bp0101100111
private noncomputable def vp010110010111_0 : Blocks := edgeBlocks% "full/vectors/010110010111-V-0000.bin"
noncomputable def vp010110010111 : Blocks := vp010110010111_0
theorem coverp010110010111 : Covers (-2861761639/2000000 : ℚ) vp010110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110010110_0 : Blocks := edgeBlocks% "full/vectors/010110010110-V-0000.bin"
noncomputable def vp010110010110 : Blocks := vp010110010110_0
theorem coverp010110010110 : Covers (-2859761639/2000000 : ℚ) vp010110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001011_0 : Blocks := edgeBlocks% "full/vectors/01011001011-V-0000.bin"
noncomputable def vp01011001011 : Blocks := vp01011001011_0
private theorem bp010110010110 : Branch 0 (-2859761639/4000000 : ℚ) vp01011001011 := by
  apply branch_left_normalized (c:=vp010110010110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2859761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2859761639/2000000 : ℚ) by norm_num]
  exact coverp010110010110
private noncomputable def ep010110010111_0 : Blocks := edgeBlocks% "full/vectors/010110010111-E-0000.bin"
noncomputable def ep010110010111 : Blocks := ep010110010111_0
private theorem idp010110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001011.list =
    C ((2:ℤ)^108) * horner X vp010110010111.list + horner X ep010110010111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110010111 : Branch 1 (-2859761639/4000000 : ℚ) vp01011001011 := by
  apply branch_checked idp010110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2859761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2861761639/2000000 : ℚ) by norm_num]
  exact coverp010110010111
theorem coverp01011001011 : Covers (-2859761639/4000000 : ℚ) vp01011001011 := join_branches bp010110010110 bp010110010111
private noncomputable def vp010110010101_0 : Blocks := edgeBlocks% "full/vectors/010110010101-V-0000.bin"
noncomputable def vp010110010101 : Blocks := vp010110010101_0
theorem coverp010110010101 : Covers (-2857761639/2000000 : ℚ) vp010110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110010100_0 : Blocks := edgeBlocks% "full/vectors/010110010100-V-0000.bin"
noncomputable def vp010110010100 : Blocks := vp010110010100_0
theorem coverp010110010100 : Covers (-2855761639/2000000 : ℚ) vp010110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001010_0 : Blocks := edgeBlocks% "full/vectors/01011001010-V-0000.bin"
noncomputable def vp01011001010 : Blocks := vp01011001010_0
private theorem bp010110010100 : Branch 0 (-2855761639/4000000 : ℚ) vp01011001010 := by
  apply branch_left_normalized (c:=vp010110010100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2855761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2855761639/2000000 : ℚ) by norm_num]
  exact coverp010110010100
private noncomputable def ep010110010101_0 : Blocks := edgeBlocks% "full/vectors/010110010101-E-0000.bin"
noncomputable def ep010110010101 : Blocks := ep010110010101_0
private theorem idp010110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001010.list =
    C ((2:ℤ)^106) * horner X vp010110010101.list + horner X ep010110010101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110010101 : Branch 1 (-2855761639/4000000 : ℚ) vp01011001010 := by
  apply branch_checked idp010110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2855761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2857761639/2000000 : ℚ) by norm_num]
  exact coverp010110010101
theorem coverp01011001010 : Covers (-2855761639/4000000 : ℚ) vp01011001010 := join_branches bp010110010100 bp010110010101
private noncomputable def vp0101100101_0 : Blocks := edgeBlocks% "full/vectors/0101100101-V-0000.bin"
private noncomputable def vp0101100101_1 : Blocks := edgeBlocks% "full/vectors/0101100101-V-0001.bin"
noncomputable def vp0101100101 : Blocks := (Blocks.join vp0101100101_0 vp0101100101_1)
private theorem bp01011001010 : Branch 0 (-2855761639/8000000 : ℚ) vp0101100101 := by
  apply branch_left_normalized (c:=vp01011001010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2855761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2855761639/4000000 : ℚ) by norm_num]
  exact coverp01011001010
private noncomputable def ep01011001011_0 : Blocks := edgeBlocks% "full/vectors/01011001011-E-0000.bin"
private noncomputable def ep01011001011_1 : Blocks := edgeBlocks% "full/vectors/01011001011-E-0001.bin"
noncomputable def ep01011001011 : Blocks := (Blocks.join ep01011001011_0 ep01011001011_1)
private theorem idp01011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100101.list =
    C ((2:ℤ)^192) * horner X vp01011001011.list + horner X ep01011001011.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011001011 : Branch 1 (-2855761639/8000000 : ℚ) vp0101100101 := by
  apply branch_checked idp01011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2855761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2859761639/4000000 : ℚ) by norm_num]
  exact coverp01011001011
theorem coverp0101100101 : Covers (-2855761639/8000000 : ℚ) vp0101100101 := join_branches bp01011001010 bp01011001011
private noncomputable def vp010110010011_0 : Blocks := edgeBlocks% "full/vectors/010110010011-V-0000.bin"
noncomputable def vp010110010011 : Blocks := vp010110010011_0
theorem coverp010110010011 : Covers (-2853761639/2000000 : ℚ) vp010110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010110010010_0 : Blocks := edgeBlocks% "full/vectors/010110010010-V-0000.bin"
noncomputable def vp010110010010 : Blocks := vp010110010010_0
theorem coverp010110010010 : Covers (-2851761639/2000000 : ℚ) vp010110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001001_0 : Blocks := edgeBlocks% "full/vectors/01011001001-V-0000.bin"
noncomputable def vp01011001001 : Blocks := vp01011001001_0
private theorem bp010110010010 : Branch 0 (-2851761639/4000000 : ℚ) vp01011001001 := by
  apply branch_left_normalized (c:=vp010110010010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2851761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2851761639/2000000 : ℚ) by norm_num]
  exact coverp010110010010
private noncomputable def ep010110010011_0 : Blocks := edgeBlocks% "full/vectors/010110010011-E-0000.bin"
noncomputable def ep010110010011 : Blocks := ep010110010011_0
private theorem idp010110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001001.list =
    C ((2:ℤ)^105) * horner X vp010110010011.list + horner X ep010110010011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110010011 : Branch 1 (-2851761639/4000000 : ℚ) vp01011001001 := by
  apply branch_checked idp010110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2851761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2853761639/2000000 : ℚ) by norm_num]
  exact coverp010110010011
theorem coverp01011001001 : Covers (-2851761639/4000000 : ℚ) vp01011001001 := join_branches bp010110010010 bp010110010011
private noncomputable def vp010110010001_0 : Blocks := edgeBlocks% "full/vectors/010110010001-V-0000.bin"
noncomputable def vp010110010001 : Blocks := vp010110010001_0
theorem coverp010110010001 : Covers (-2849761639/2000000 : ℚ) vp010110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010110010000_0 : Blocks := edgeBlocks% "full/vectors/010110010000-V-0000.bin"
noncomputable def vp010110010000 : Blocks := vp010110010000_0
theorem coverp010110010000 : Covers (-2847761639/2000000 : ℚ) vp010110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011001000_0 : Blocks := edgeBlocks% "full/vectors/01011001000-V-0000.bin"
noncomputable def vp01011001000 : Blocks := vp01011001000_0
private theorem bp010110010000 : Branch 0 (-2847761639/4000000 : ℚ) vp01011001000 := by
  apply branch_left_normalized (c:=vp010110010000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2847761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2847761639/2000000 : ℚ) by norm_num]
  exact coverp010110010000
private noncomputable def ep010110010001_0 : Blocks := edgeBlocks% "full/vectors/010110010001-E-0000.bin"
noncomputable def ep010110010001 : Blocks := ep010110010001_0
private theorem idp010110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001000.list =
    C ((2:ℤ)^107) * horner X vp010110010001.list + horner X ep010110010001.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110010001 : Branch 1 (-2847761639/4000000 : ℚ) vp01011001000 := by
  apply branch_checked idp010110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2847761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2849761639/2000000 : ℚ) by norm_num]
  exact coverp010110010001
theorem coverp01011001000 : Covers (-2847761639/4000000 : ℚ) vp01011001000 := join_branches bp010110010000 bp010110010001
private noncomputable def vp0101100100_0 : Blocks := edgeBlocks% "full/vectors/0101100100-V-0000.bin"
private noncomputable def vp0101100100_1 : Blocks := edgeBlocks% "full/vectors/0101100100-V-0001.bin"
noncomputable def vp0101100100 : Blocks := (Blocks.join vp0101100100_0 vp0101100100_1)
private theorem bp01011001000 : Branch 0 (-2847761639/8000000 : ℚ) vp0101100100 := by
  apply branch_left_normalized (c:=vp01011001000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2847761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2847761639/4000000 : ℚ) by norm_num]
  exact coverp01011001000
private noncomputable def ep01011001001_0 : Blocks := edgeBlocks% "full/vectors/01011001001-E-0000.bin"
private noncomputable def ep01011001001_1 : Blocks := edgeBlocks% "full/vectors/01011001001-E-0001.bin"
noncomputable def ep01011001001 : Blocks := (Blocks.join ep01011001001_0 ep01011001001_1)
private theorem idp01011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100100.list =
    C ((2:ℤ)^192) * horner X vp01011001001.list + horner X ep01011001001.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011001001 : Branch 1 (-2847761639/8000000 : ℚ) vp0101100100 := by
  apply branch_checked idp01011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2847761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2851761639/4000000 : ℚ) by norm_num]
  exact coverp01011001001
theorem coverp0101100100 : Covers (-2847761639/8000000 : ℚ) vp0101100100 := join_branches bp01011001000 bp01011001001
private noncomputable def vp010110010_0 : Blocks := edgeBlocks% "full/vectors/010110010-V-0000.bin"
private noncomputable def vp010110010_1 : Blocks := edgeBlocks% "full/vectors/010110010-V-0001.bin"
private noncomputable def vp010110010_2 : Blocks := edgeBlocks% "full/vectors/010110010-V-0002.bin"
noncomputable def vp010110010 : Blocks := (Blocks.join vp010110010_0 (Blocks.join vp010110010_1 vp010110010_2))
private theorem bp0101100100 : Branch 0 (-2847761639/16000000 : ℚ) vp010110010 := by
  apply branch_left_normalized (c:=vp0101100100) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2847761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2847761639/8000000 : ℚ) by norm_num]
  exact coverp0101100100
private noncomputable def ep0101100101_0 : Blocks := edgeBlocks% "full/vectors/0101100101-E-0000.bin"
private noncomputable def ep0101100101_1 : Blocks := edgeBlocks% "full/vectors/0101100101-E-0001.bin"
private noncomputable def ep0101100101_2 : Blocks := edgeBlocks% "full/vectors/0101100101-E-0002.bin"
noncomputable def ep0101100101 : Blocks := (Blocks.join ep0101100101_0 (Blocks.join ep0101100101_1 ep0101100101_2))
private theorem idp0101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110010.list =
    C ((2:ℤ)^361) * horner X vp0101100101.list + horner X ep0101100101.list := by
  exact edge_identity (B := (2:ℤ)^572) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101100101 : Branch 1 (-2847761639/16000000 : ℚ) vp010110010 := by
  apply branch_checked idp0101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2847761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2855761639/8000000 : ℚ) by norm_num]
  exact coverp0101100101
theorem coverp010110010 : Covers (-2847761639/16000000 : ℚ) vp010110010 := join_branches bp0101100100 bp0101100101
private noncomputable def vp01011001_0 : Blocks := edgeBlocks% "full/vectors/01011001-V-0000.bin"
private noncomputable def vp01011001_1 : Blocks := edgeBlocks% "full/vectors/01011001-V-0001.bin"
private noncomputable def vp01011001_2 : Blocks := edgeBlocks% "full/vectors/01011001-V-0002.bin"
private noncomputable def vp01011001_3 : Blocks := edgeBlocks% "full/vectors/01011001-V-0003.bin"
private noncomputable def vp01011001_4 : Blocks := edgeBlocks% "full/vectors/01011001-V-0004.bin"
noncomputable def vp01011001 : Blocks := (Blocks.join (Blocks.join vp01011001_0 vp01011001_1) (Blocks.join vp01011001_2 (Blocks.join vp01011001_3 vp01011001_4)))
private theorem bp010110010 : Branch 0 (-2847761639/32000000 : ℚ) vp01011001 := by
  apply branch_left_normalized (c:=vp010110010) (k:=0) (m:=315) (by decide +kernel)
  rw [show 2*(-2847761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2847761639/16000000 : ℚ) by norm_num]
  exact coverp010110010
private noncomputable def ep010110011_0 : Blocks := edgeBlocks% "full/vectors/010110011-E-0000.bin"
private noncomputable def ep010110011_1 : Blocks := edgeBlocks% "full/vectors/010110011-E-0001.bin"
private noncomputable def ep010110011_2 : Blocks := edgeBlocks% "full/vectors/010110011-E-0002.bin"
private noncomputable def ep010110011_3 : Blocks := edgeBlocks% "full/vectors/010110011-E-0003.bin"
private noncomputable def ep010110011_4 : Blocks := edgeBlocks% "full/vectors/010110011-E-0004.bin"
noncomputable def ep010110011 : Blocks := (Blocks.join (Blocks.join ep010110011_0 ep010110011_1) (Blocks.join ep010110011_2 (Blocks.join ep010110011_3 ep010110011_4)))
private theorem idp010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011001.list =
    C ((2:ℤ)^697) * horner X vp010110011.list + horner X ep010110011.list := by
  exact edge_identity (B := (2:ℤ)^1017) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110011 : Branch 1 (-2847761639/32000000 : ℚ) vp01011001 := by
  apply branch_checked idp010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2847761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2863761639/16000000 : ℚ) by norm_num]
  exact coverp010110011
theorem coverp01011001 : Covers (-2847761639/32000000 : ℚ) vp01011001 := join_branches bp010110010 bp010110011
private noncomputable def vp010110001111_0 : Blocks := edgeBlocks% "full/vectors/010110001111-V-0000.bin"
noncomputable def vp010110001111 : Blocks := vp010110001111_0
theorem coverp010110001111 : Covers (-2845761639/2000000 : ℚ) vp010110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010110001110_0 : Blocks := edgeBlocks% "full/vectors/010110001110-V-0000.bin"
noncomputable def vp010110001110 : Blocks := vp010110001110_0
theorem coverp010110001110 : Covers (-2843761639/2000000 : ℚ) vp010110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011000111_0 : Blocks := edgeBlocks% "full/vectors/01011000111-V-0000.bin"
noncomputable def vp01011000111 : Blocks := vp01011000111_0
private theorem bp010110001110 : Branch 0 (-2843761639/4000000 : ℚ) vp01011000111 := by
  apply branch_left_normalized (c:=vp010110001110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2843761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2843761639/2000000 : ℚ) by norm_num]
  exact coverp010110001110
private noncomputable def ep010110001111_0 : Blocks := edgeBlocks% "full/vectors/010110001111-E-0000.bin"
noncomputable def ep010110001111 : Blocks := ep010110001111_0
private theorem idp010110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011000111.list =
    C ((2:ℤ)^108) * horner X vp010110001111.list + horner X ep010110001111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110001111 : Branch 1 (-2843761639/4000000 : ℚ) vp01011000111 := by
  apply branch_checked idp010110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2843761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2845761639/2000000 : ℚ) by norm_num]
  exact coverp010110001111
theorem coverp01011000111 : Covers (-2843761639/4000000 : ℚ) vp01011000111 := join_branches bp010110001110 bp010110001111
private noncomputable def vp010110001101_0 : Blocks := edgeBlocks% "full/vectors/010110001101-V-0000.bin"
noncomputable def vp010110001101 : Blocks := vp010110001101_0
theorem coverp010110001101 : Covers (-2841761639/2000000 : ℚ) vp010110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010110001100_0 : Blocks := edgeBlocks% "full/vectors/010110001100-V-0000.bin"
noncomputable def vp010110001100 : Blocks := vp010110001100_0
theorem coverp010110001100 : Covers (-2839761639/2000000 : ℚ) vp010110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011000110_0 : Blocks := edgeBlocks% "full/vectors/01011000110-V-0000.bin"
noncomputable def vp01011000110 : Blocks := vp01011000110_0
private theorem bp010110001100 : Branch 0 (-2839761639/4000000 : ℚ) vp01011000110 := by
  apply branch_left_normalized (c:=vp010110001100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-2839761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2839761639/2000000 : ℚ) by norm_num]
  exact coverp010110001100
private noncomputable def ep010110001101_0 : Blocks := edgeBlocks% "full/vectors/010110001101-E-0000.bin"
noncomputable def ep010110001101 : Blocks := ep010110001101_0
private theorem idp010110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011000110.list =
    C ((2:ℤ)^103) * horner X vp010110001101.list + horner X ep010110001101.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110001101 : Branch 1 (-2839761639/4000000 : ℚ) vp01011000110 := by
  apply branch_checked idp010110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2839761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2841761639/2000000 : ℚ) by norm_num]
  exact coverp010110001101
theorem coverp01011000110 : Covers (-2839761639/4000000 : ℚ) vp01011000110 := join_branches bp010110001100 bp010110001101
private noncomputable def vp0101100011_0 : Blocks := edgeBlocks% "full/vectors/0101100011-V-0000.bin"
private noncomputable def vp0101100011_1 : Blocks := edgeBlocks% "full/vectors/0101100011-V-0001.bin"
noncomputable def vp0101100011 : Blocks := (Blocks.join vp0101100011_0 vp0101100011_1)
private theorem bp01011000110 : Branch 0 (-2839761639/8000000 : ℚ) vp0101100011 := by
  apply branch_left_normalized (c:=vp01011000110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-2839761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2839761639/4000000 : ℚ) by norm_num]
  exact coverp01011000110
private noncomputable def ep01011000111_0 : Blocks := edgeBlocks% "full/vectors/01011000111-E-0000.bin"
private noncomputable def ep01011000111_1 : Blocks := edgeBlocks% "full/vectors/01011000111-E-0001.bin"
noncomputable def ep01011000111 : Blocks := (Blocks.join ep01011000111_0 ep01011000111_1)
private theorem idp01011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100011.list =
    C ((2:ℤ)^187) * horner X vp01011000111.list + horner X ep01011000111.list := by
  exact edge_identity (B := (2:ℤ)^343) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011000111 : Branch 1 (-2839761639/8000000 : ℚ) vp0101100011 := by
  apply branch_checked idp01011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2839761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2843761639/4000000 : ℚ) by norm_num]
  exact coverp01011000111
theorem coverp0101100011 : Covers (-2839761639/8000000 : ℚ) vp0101100011 := join_branches bp01011000110 bp01011000111
private noncomputable def vp01011000101_0 : Blocks := edgeBlocks% "full/vectors/01011000101-V-0000.bin"
noncomputable def vp01011000101 : Blocks := vp01011000101_0
theorem coverp01011000101 : Covers (-2835761639/4000000 : ℚ) vp01011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp01011000100_0 : Blocks := edgeBlocks% "full/vectors/01011000100-V-0000.bin"
noncomputable def vp01011000100 : Blocks := vp01011000100_0
theorem coverp01011000100 : Covers (-2831761639/4000000 : ℚ) vp01011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0101100010_0 : Blocks := edgeBlocks% "full/vectors/0101100010-V-0000.bin"
private noncomputable def vp0101100010_1 : Blocks := edgeBlocks% "full/vectors/0101100010-V-0001.bin"
noncomputable def vp0101100010 : Blocks := (Blocks.join vp0101100010_0 vp0101100010_1)
private theorem bp01011000100 : Branch 0 (-2831761639/8000000 : ℚ) vp0101100010 := by
  apply branch_left_normalized (c:=vp01011000100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-2831761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2831761639/4000000 : ℚ) by norm_num]
  exact coverp01011000100
private noncomputable def ep01011000101_0 : Blocks := edgeBlocks% "full/vectors/01011000101-E-0000.bin"
private noncomputable def ep01011000101_1 : Blocks := edgeBlocks% "full/vectors/01011000101-E-0001.bin"
noncomputable def ep01011000101 : Blocks := (Blocks.join ep01011000101_0 ep01011000101_1)
private theorem idp01011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100010.list =
    C ((2:ℤ)^188) * horner X vp01011000101.list + horner X ep01011000101.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011000101 : Branch 1 (-2831761639/8000000 : ℚ) vp0101100010 := by
  apply branch_checked idp01011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2831761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2835761639/4000000 : ℚ) by norm_num]
  exact coverp01011000101
theorem coverp0101100010 : Covers (-2831761639/8000000 : ℚ) vp0101100010 := join_branches bp01011000100 bp01011000101
private noncomputable def vp010110001_0 : Blocks := edgeBlocks% "full/vectors/010110001-V-0000.bin"
private noncomputable def vp010110001_1 : Blocks := edgeBlocks% "full/vectors/010110001-V-0001.bin"
private noncomputable def vp010110001_2 : Blocks := edgeBlocks% "full/vectors/010110001-V-0002.bin"
noncomputable def vp010110001 : Blocks := (Blocks.join vp010110001_0 (Blocks.join vp010110001_1 vp010110001_2))
private theorem bp0101100010 : Branch 0 (-2831761639/16000000 : ℚ) vp010110001 := by
  apply branch_left_normalized (c:=vp0101100010) (k:=0) (m:=165) (by decide +kernel)
  rw [show 2*(-2831761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2831761639/8000000 : ℚ) by norm_num]
  exact coverp0101100010
private noncomputable def ep0101100011_0 : Blocks := edgeBlocks% "full/vectors/0101100011-E-0000.bin"
private noncomputable def ep0101100011_1 : Blocks := edgeBlocks% "full/vectors/0101100011-E-0001.bin"
private noncomputable def ep0101100011_2 : Blocks := edgeBlocks% "full/vectors/0101100011-E-0002.bin"
noncomputable def ep0101100011 : Blocks := (Blocks.join ep0101100011_0 (Blocks.join ep0101100011_1 ep0101100011_2))
private theorem idp0101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110001.list =
    C ((2:ℤ)^354) * horner X vp0101100011.list + horner X ep0101100011.list := by
  exact edge_identity (B := (2:ℤ)^562) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101100011 : Branch 1 (-2831761639/16000000 : ℚ) vp010110001 := by
  apply branch_checked idp0101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2831761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2839761639/8000000 : ℚ) by norm_num]
  exact coverp0101100011
theorem coverp010110001 : Covers (-2831761639/16000000 : ℚ) vp010110001 := join_branches bp0101100010 bp0101100011
private noncomputable def vp01011000011_0 : Blocks := edgeBlocks% "full/vectors/01011000011-V-0000.bin"
noncomputable def vp01011000011 : Blocks := vp01011000011_0
theorem coverp01011000011 : Covers (-2827761639/4000000 : ℚ) vp01011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp01011000010_0 : Blocks := edgeBlocks% "full/vectors/01011000010-V-0000.bin"
noncomputable def vp01011000010 : Blocks := vp01011000010_0
theorem coverp01011000010 : Covers (-2823761639/4000000 : ℚ) vp01011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0101100001_0 : Blocks := edgeBlocks% "full/vectors/0101100001-V-0000.bin"
private noncomputable def vp0101100001_1 : Blocks := edgeBlocks% "full/vectors/0101100001-V-0001.bin"
noncomputable def vp0101100001 : Blocks := (Blocks.join vp0101100001_0 vp0101100001_1)
private theorem bp01011000010 : Branch 0 (-2823761639/8000000 : ℚ) vp0101100001 := by
  apply branch_left_normalized (c:=vp01011000010) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-2823761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2823761639/4000000 : ℚ) by norm_num]
  exact coverp01011000010
private noncomputable def ep01011000011_0 : Blocks := edgeBlocks% "full/vectors/01011000011-E-0000.bin"
private noncomputable def ep01011000011_1 : Blocks := edgeBlocks% "full/vectors/01011000011-E-0001.bin"
noncomputable def ep01011000011 : Blocks := (Blocks.join ep01011000011_0 ep01011000011_1)
private theorem idp01011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100001.list =
    C ((2:ℤ)^188) * horner X vp01011000011.list + horner X ep01011000011.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011000011 : Branch 1 (-2823761639/8000000 : ℚ) vp0101100001 := by
  apply branch_checked idp01011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2823761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2827761639/4000000 : ℚ) by norm_num]
  exact coverp01011000011
theorem coverp0101100001 : Covers (-2823761639/8000000 : ℚ) vp0101100001 := join_branches bp01011000010 bp01011000011
private noncomputable def vp01011000001_0 : Blocks := edgeBlocks% "full/vectors/01011000001-V-0000.bin"
noncomputable def vp01011000001 : Blocks := vp01011000001_0
theorem coverp01011000001 : Covers (-2819761639/4000000 : ℚ) vp01011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp01011000000_0 : Blocks := edgeBlocks% "full/vectors/01011000000-V-0000.bin"
noncomputable def vp01011000000 : Blocks := vp01011000000_0
theorem coverp01011000000 : Covers (-2815761639/4000000 : ℚ) vp01011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0101100000_0 : Blocks := edgeBlocks% "full/vectors/0101100000-V-0000.bin"
private noncomputable def vp0101100000_1 : Blocks := edgeBlocks% "full/vectors/0101100000-V-0001.bin"
noncomputable def vp0101100000 : Blocks := (Blocks.join vp0101100000_0 vp0101100000_1)
private theorem bp01011000000 : Branch 0 (-2815761639/8000000 : ℚ) vp0101100000 := by
  apply branch_left_normalized (c:=vp01011000000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-2815761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/4000000 : ℚ) by norm_num]
  exact coverp01011000000
private noncomputable def ep01011000001_0 : Blocks := edgeBlocks% "full/vectors/01011000001-E-0000.bin"
private noncomputable def ep01011000001_1 : Blocks := edgeBlocks% "full/vectors/01011000001-E-0001.bin"
noncomputable def ep01011000001 : Blocks := (Blocks.join ep01011000001_0 ep01011000001_1)
private theorem idp01011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100000.list =
    C ((2:ℤ)^188) * horner X vp01011000001.list + horner X ep01011000001.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011000001 : Branch 1 (-2815761639/8000000 : ℚ) vp0101100000 := by
  apply branch_checked idp01011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2819761639/4000000 : ℚ) by norm_num]
  exact coverp01011000001
theorem coverp0101100000 : Covers (-2815761639/8000000 : ℚ) vp0101100000 := join_branches bp01011000000 bp01011000001
private noncomputable def vp010110000_0 : Blocks := edgeBlocks% "full/vectors/010110000-V-0000.bin"
private noncomputable def vp010110000_1 : Blocks := edgeBlocks% "full/vectors/010110000-V-0001.bin"
private noncomputable def vp010110000_2 : Blocks := edgeBlocks% "full/vectors/010110000-V-0002.bin"
noncomputable def vp010110000 : Blocks := (Blocks.join vp010110000_0 (Blocks.join vp010110000_1 vp010110000_2))
private theorem bp0101100000 : Branch 0 (-2815761639/16000000 : ℚ) vp010110000 := by
  apply branch_left_normalized (c:=vp0101100000) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-2815761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/8000000 : ℚ) by norm_num]
  exact coverp0101100000
private noncomputable def ep0101100001_0 : Blocks := edgeBlocks% "full/vectors/0101100001-E-0000.bin"
private noncomputable def ep0101100001_1 : Blocks := edgeBlocks% "full/vectors/0101100001-E-0001.bin"
private noncomputable def ep0101100001_2 : Blocks := edgeBlocks% "full/vectors/0101100001-E-0002.bin"
noncomputable def ep0101100001 : Blocks := (Blocks.join ep0101100001_0 (Blocks.join ep0101100001_1 ep0101100001_2))
private theorem idp0101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110000.list =
    C ((2:ℤ)^358) * horner X vp0101100001.list + horner X ep0101100001.list := by
  exact edge_identity (B := (2:ℤ)^561) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101100001 : Branch 1 (-2815761639/16000000 : ℚ) vp010110000 := by
  apply branch_checked idp0101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2823761639/8000000 : ℚ) by norm_num]
  exact coverp0101100001
theorem coverp010110000 : Covers (-2815761639/16000000 : ℚ) vp010110000 := join_branches bp0101100000 bp0101100001
private noncomputable def vp01011000_0 : Blocks := edgeBlocks% "full/vectors/01011000-V-0000.bin"
private noncomputable def vp01011000_1 : Blocks := edgeBlocks% "full/vectors/01011000-V-0001.bin"
private noncomputable def vp01011000_2 : Blocks := edgeBlocks% "full/vectors/01011000-V-0002.bin"
private noncomputable def vp01011000_3 : Blocks := edgeBlocks% "full/vectors/01011000-V-0003.bin"
private noncomputable def vp01011000_4 : Blocks := edgeBlocks% "full/vectors/01011000-V-0004.bin"
noncomputable def vp01011000 : Blocks := (Blocks.join (Blocks.join vp01011000_0 vp01011000_1) (Blocks.join vp01011000_2 (Blocks.join vp01011000_3 vp01011000_4)))
private theorem bp010110000 : Branch 0 (-2815761639/32000000 : ℚ) vp01011000 := by
  apply branch_left_normalized (c:=vp010110000) (k:=0) (m:=311) (by decide +kernel)
  rw [show 2*(-2815761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/16000000 : ℚ) by norm_num]
  exact coverp010110000
private noncomputable def ep010110001_0 : Blocks := edgeBlocks% "full/vectors/010110001-E-0000.bin"
private noncomputable def ep010110001_1 : Blocks := edgeBlocks% "full/vectors/010110001-E-0001.bin"
private noncomputable def ep010110001_2 : Blocks := edgeBlocks% "full/vectors/010110001-E-0002.bin"
private noncomputable def ep010110001_3 : Blocks := edgeBlocks% "full/vectors/010110001-E-0003.bin"
private noncomputable def ep010110001_4 : Blocks := edgeBlocks% "full/vectors/010110001-E-0004.bin"
noncomputable def ep010110001 : Blocks := (Blocks.join (Blocks.join ep010110001_0 ep010110001_1) (Blocks.join ep010110001_2 (Blocks.join ep010110001_3 ep010110001_4)))
private theorem idp010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011000.list =
    C ((2:ℤ)^696) * horner X vp010110001.list + horner X ep010110001.list := by
  exact edge_identity (B := (2:ℤ)^1010) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010110001 : Branch 1 (-2815761639/32000000 : ℚ) vp01011000 := by
  apply branch_checked idp010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2831761639/16000000 : ℚ) by norm_num]
  exact coverp010110001
theorem coverp01011000 : Covers (-2815761639/32000000 : ℚ) vp01011000 := join_branches bp010110000 bp010110001
private noncomputable def vp0101100_0 : Blocks := edgeBlocks% "full/vectors/0101100-V-0000.bin"
private noncomputable def vp0101100_1 : Blocks := edgeBlocks% "full/vectors/0101100-V-0001.bin"
private noncomputable def vp0101100_2 : Blocks := edgeBlocks% "full/vectors/0101100-V-0002.bin"
private noncomputable def vp0101100_3 : Blocks := edgeBlocks% "full/vectors/0101100-V-0003.bin"
private noncomputable def vp0101100_4 : Blocks := edgeBlocks% "full/vectors/0101100-V-0004.bin"
private noncomputable def vp0101100_5 : Blocks := edgeBlocks% "full/vectors/0101100-V-0005.bin"
private noncomputable def vp0101100_6 : Blocks := edgeBlocks% "full/vectors/0101100-V-0006.bin"
private noncomputable def vp0101100_7 : Blocks := edgeBlocks% "full/vectors/0101100-V-0007.bin"
private noncomputable def vp0101100_8 : Blocks := edgeBlocks% "full/vectors/0101100-V-0008.bin"
private noncomputable def vp0101100_9 : Blocks := edgeBlocks% "full/vectors/0101100-V-0009.bin"
noncomputable def vp0101100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101100_0 vp0101100_1) (Blocks.join vp0101100_2 (Blocks.join vp0101100_3 vp0101100_4))) (Blocks.join (Blocks.join vp0101100_5 vp0101100_6) (Blocks.join vp0101100_7 (Blocks.join vp0101100_8 vp0101100_9))))
private theorem bp01011000 : Branch 0 (-2815761639/64000000 : ℚ) vp0101100 := by
  apply branch_left_normalized (c:=vp01011000) (k:=0) (m:=604) (by decide +kernel)
  rw [show 2*(-2815761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/32000000 : ℚ) by norm_num]
  exact coverp01011000
private noncomputable def ep01011001_0 : Blocks := edgeBlocks% "full/vectors/01011001-E-0000.bin"
private noncomputable def ep01011001_1 : Blocks := edgeBlocks% "full/vectors/01011001-E-0001.bin"
private noncomputable def ep01011001_2 : Blocks := edgeBlocks% "full/vectors/01011001-E-0002.bin"
private noncomputable def ep01011001_3 : Blocks := edgeBlocks% "full/vectors/01011001-E-0003.bin"
private noncomputable def ep01011001_4 : Blocks := edgeBlocks% "full/vectors/01011001-E-0004.bin"
private noncomputable def ep01011001_5 : Blocks := edgeBlocks% "full/vectors/01011001-E-0005.bin"
private noncomputable def ep01011001_6 : Blocks := edgeBlocks% "full/vectors/01011001-E-0006.bin"
private noncomputable def ep01011001_7 : Blocks := edgeBlocks% "full/vectors/01011001-E-0007.bin"
private noncomputable def ep01011001_8 : Blocks := edgeBlocks% "full/vectors/01011001-E-0008.bin"
private noncomputable def ep01011001_9 : Blocks := edgeBlocks% "full/vectors/01011001-E-0009.bin"
noncomputable def ep01011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01011001_0 ep01011001_1) (Blocks.join ep01011001_2 (Blocks.join ep01011001_3 ep01011001_4))) (Blocks.join (Blocks.join ep01011001_5 ep01011001_6) (Blocks.join ep01011001_7 (Blocks.join ep01011001_8 ep01011001_9))))
private theorem idp01011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101100.list =
    C ((2:ℤ)^1359) * horner X vp01011001.list + horner X ep01011001.list := by
  exact edge_identity (B := (2:ℤ)^1899) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011001 : Branch 1 (-2815761639/64000000 : ℚ) vp0101100 := by
  apply branch_checked idp01011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2847761639/32000000 : ℚ) by norm_num]
  exact coverp01011001
theorem coverp0101100 : Covers (-2815761639/64000000 : ℚ) vp0101100 := join_branches bp01011000 bp01011001
private noncomputable def vp010110_0 : Blocks := edgeBlocks% "full/vectors/010110-V-0000.bin"
private noncomputable def vp010110_1 : Blocks := edgeBlocks% "full/vectors/010110-V-0001.bin"
private noncomputable def vp010110_2 : Blocks := edgeBlocks% "full/vectors/010110-V-0002.bin"
private noncomputable def vp010110_3 : Blocks := edgeBlocks% "full/vectors/010110-V-0003.bin"
private noncomputable def vp010110_4 : Blocks := edgeBlocks% "full/vectors/010110-V-0004.bin"
private noncomputable def vp010110_5 : Blocks := edgeBlocks% "full/vectors/010110-V-0005.bin"
private noncomputable def vp010110_6 : Blocks := edgeBlocks% "full/vectors/010110-V-0006.bin"
private noncomputable def vp010110_7 : Blocks := edgeBlocks% "full/vectors/010110-V-0007.bin"
private noncomputable def vp010110_8 : Blocks := edgeBlocks% "full/vectors/010110-V-0008.bin"
private noncomputable def vp010110_9 : Blocks := edgeBlocks% "full/vectors/010110-V-0009.bin"
private noncomputable def vp010110_10 : Blocks := edgeBlocks% "full/vectors/010110-V-0010.bin"
private noncomputable def vp010110_11 : Blocks := edgeBlocks% "full/vectors/010110-V-0011.bin"
private noncomputable def vp010110_12 : Blocks := edgeBlocks% "full/vectors/010110-V-0012.bin"
private noncomputable def vp010110_13 : Blocks := edgeBlocks% "full/vectors/010110-V-0013.bin"
private noncomputable def vp010110_14 : Blocks := edgeBlocks% "full/vectors/010110-V-0014.bin"
private noncomputable def vp010110_15 : Blocks := edgeBlocks% "full/vectors/010110-V-0015.bin"
private noncomputable def vp010110_16 : Blocks := edgeBlocks% "full/vectors/010110-V-0016.bin"
private noncomputable def vp010110_17 : Blocks := edgeBlocks% "full/vectors/010110-V-0017.bin"
noncomputable def vp010110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010110_0 vp010110_1) (Blocks.join vp010110_2 vp010110_3)) (Blocks.join (Blocks.join vp010110_4 vp010110_5) (Blocks.join vp010110_6 (Blocks.join vp010110_7 vp010110_8)))) (Blocks.join (Blocks.join (Blocks.join vp010110_9 vp010110_10) (Blocks.join vp010110_11 vp010110_12)) (Blocks.join (Blocks.join vp010110_13 vp010110_14) (Blocks.join vp010110_15 (Blocks.join vp010110_16 vp010110_17)))))
private theorem bp0101100 : Branch 0 (-2815761639/128000000 : ℚ) vp010110 := by
  apply branch_left_normalized (c:=vp0101100) (k:=0) (m:=1181) (by decide +kernel)
  rw [show 2*(-2815761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/64000000 : ℚ) by norm_num]
  exact coverp0101100
private noncomputable def ep0101101_0 : Blocks := edgeBlocks% "full/vectors/0101101-E-0000.bin"
private noncomputable def ep0101101_1 : Blocks := edgeBlocks% "full/vectors/0101101-E-0001.bin"
private noncomputable def ep0101101_2 : Blocks := edgeBlocks% "full/vectors/0101101-E-0002.bin"
private noncomputable def ep0101101_3 : Blocks := edgeBlocks% "full/vectors/0101101-E-0003.bin"
private noncomputable def ep0101101_4 : Blocks := edgeBlocks% "full/vectors/0101101-E-0004.bin"
private noncomputable def ep0101101_5 : Blocks := edgeBlocks% "full/vectors/0101101-E-0005.bin"
private noncomputable def ep0101101_6 : Blocks := edgeBlocks% "full/vectors/0101101-E-0006.bin"
private noncomputable def ep0101101_7 : Blocks := edgeBlocks% "full/vectors/0101101-E-0007.bin"
private noncomputable def ep0101101_8 : Blocks := edgeBlocks% "full/vectors/0101101-E-0008.bin"
private noncomputable def ep0101101_9 : Blocks := edgeBlocks% "full/vectors/0101101-E-0009.bin"
private noncomputable def ep0101101_10 : Blocks := edgeBlocks% "full/vectors/0101101-E-0010.bin"
private noncomputable def ep0101101_11 : Blocks := edgeBlocks% "full/vectors/0101101-E-0011.bin"
private noncomputable def ep0101101_12 : Blocks := edgeBlocks% "full/vectors/0101101-E-0012.bin"
private noncomputable def ep0101101_13 : Blocks := edgeBlocks% "full/vectors/0101101-E-0013.bin"
private noncomputable def ep0101101_14 : Blocks := edgeBlocks% "full/vectors/0101101-E-0014.bin"
private noncomputable def ep0101101_15 : Blocks := edgeBlocks% "full/vectors/0101101-E-0015.bin"
private noncomputable def ep0101101_16 : Blocks := edgeBlocks% "full/vectors/0101101-E-0016.bin"
private noncomputable def ep0101101_17 : Blocks := edgeBlocks% "full/vectors/0101101-E-0017.bin"
noncomputable def ep0101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0101101_0 ep0101101_1) (Blocks.join ep0101101_2 ep0101101_3)) (Blocks.join (Blocks.join ep0101101_4 ep0101101_5) (Blocks.join ep0101101_6 (Blocks.join ep0101101_7 ep0101101_8)))) (Blocks.join (Blocks.join (Blocks.join ep0101101_9 ep0101101_10) (Blocks.join ep0101101_11 ep0101101_12)) (Blocks.join (Blocks.join ep0101101_13 ep0101101_14) (Blocks.join ep0101101_15 (Blocks.join ep0101101_16 ep0101101_17)))))
private theorem idp0101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010110.list =
    C ((2:ℤ)^2664) * horner X vp0101101.list + horner X ep0101101.list := by
  exact edge_identity (B := (2:ℤ)^3639) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101101 : Branch 1 (-2815761639/128000000 : ℚ) vp010110 := by
  apply branch_checked idp0101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2879761639/64000000 : ℚ) by norm_num]
  exact coverp0101101
theorem coverp010110 : Covers (-2815761639/128000000 : ℚ) vp010110 := join_branches bp0101100 bp0101101
private noncomputable def vp01011_0 : Blocks := edgeBlocks% "full/vectors/01011-V-0000.bin"
private noncomputable def vp01011_1 : Blocks := edgeBlocks% "full/vectors/01011-V-0001.bin"
private noncomputable def vp01011_2 : Blocks := edgeBlocks% "full/vectors/01011-V-0002.bin"
private noncomputable def vp01011_3 : Blocks := edgeBlocks% "full/vectors/01011-V-0003.bin"
private noncomputable def vp01011_4 : Blocks := edgeBlocks% "full/vectors/01011-V-0004.bin"
private noncomputable def vp01011_5 : Blocks := edgeBlocks% "full/vectors/01011-V-0005.bin"
private noncomputable def vp01011_6 : Blocks := edgeBlocks% "full/vectors/01011-V-0006.bin"
private noncomputable def vp01011_7 : Blocks := edgeBlocks% "full/vectors/01011-V-0007.bin"
private noncomputable def vp01011_8 : Blocks := edgeBlocks% "full/vectors/01011-V-0008.bin"
private noncomputable def vp01011_9 : Blocks := edgeBlocks% "full/vectors/01011-V-0009.bin"
private noncomputable def vp01011_10 : Blocks := edgeBlocks% "full/vectors/01011-V-0010.bin"
private noncomputable def vp01011_11 : Blocks := edgeBlocks% "full/vectors/01011-V-0011.bin"
private noncomputable def vp01011_12 : Blocks := edgeBlocks% "full/vectors/01011-V-0012.bin"
private noncomputable def vp01011_13 : Blocks := edgeBlocks% "full/vectors/01011-V-0013.bin"
private noncomputable def vp01011_14 : Blocks := edgeBlocks% "full/vectors/01011-V-0014.bin"
private noncomputable def vp01011_15 : Blocks := edgeBlocks% "full/vectors/01011-V-0015.bin"
private noncomputable def vp01011_16 : Blocks := edgeBlocks% "full/vectors/01011-V-0016.bin"
private noncomputable def vp01011_17 : Blocks := edgeBlocks% "full/vectors/01011-V-0017.bin"
private noncomputable def vp01011_18 : Blocks := edgeBlocks% "full/vectors/01011-V-0018.bin"
private noncomputable def vp01011_19 : Blocks := edgeBlocks% "full/vectors/01011-V-0019.bin"
private noncomputable def vp01011_20 : Blocks := edgeBlocks% "full/vectors/01011-V-0020.bin"
private noncomputable def vp01011_21 : Blocks := edgeBlocks% "full/vectors/01011-V-0021.bin"
private noncomputable def vp01011_22 : Blocks := edgeBlocks% "full/vectors/01011-V-0022.bin"
private noncomputable def vp01011_23 : Blocks := edgeBlocks% "full/vectors/01011-V-0023.bin"
private noncomputable def vp01011_24 : Blocks := edgeBlocks% "full/vectors/01011-V-0024.bin"
private noncomputable def vp01011_25 : Blocks := edgeBlocks% "full/vectors/01011-V-0025.bin"
private noncomputable def vp01011_26 : Blocks := edgeBlocks% "full/vectors/01011-V-0026.bin"
private noncomputable def vp01011_27 : Blocks := edgeBlocks% "full/vectors/01011-V-0027.bin"
private noncomputable def vp01011_28 : Blocks := edgeBlocks% "full/vectors/01011-V-0028.bin"
private noncomputable def vp01011_29 : Blocks := edgeBlocks% "full/vectors/01011-V-0029.bin"
private noncomputable def vp01011_30 : Blocks := edgeBlocks% "full/vectors/01011-V-0030.bin"
private noncomputable def vp01011_31 : Blocks := edgeBlocks% "full/vectors/01011-V-0031.bin"
private noncomputable def vp01011_32 : Blocks := edgeBlocks% "full/vectors/01011-V-0032.bin"
private noncomputable def vp01011_33 : Blocks := edgeBlocks% "full/vectors/01011-V-0033.bin"
private noncomputable def vp01011_34 : Blocks := edgeBlocks% "full/vectors/01011-V-0034.bin"
noncomputable def vp01011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01011_0 vp01011_1) (Blocks.join vp01011_2 vp01011_3)) (Blocks.join (Blocks.join vp01011_4 vp01011_5) (Blocks.join vp01011_6 vp01011_7))) (Blocks.join (Blocks.join (Blocks.join vp01011_8 vp01011_9) (Blocks.join vp01011_10 vp01011_11)) (Blocks.join (Blocks.join vp01011_12 vp01011_13) (Blocks.join vp01011_14 (Blocks.join vp01011_15 vp01011_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01011_17 vp01011_18) (Blocks.join vp01011_19 vp01011_20)) (Blocks.join (Blocks.join vp01011_21 vp01011_22) (Blocks.join vp01011_23 (Blocks.join vp01011_24 vp01011_25)))) (Blocks.join (Blocks.join (Blocks.join vp01011_26 vp01011_27) (Blocks.join vp01011_28 vp01011_29)) (Blocks.join (Blocks.join vp01011_30 vp01011_31) (Blocks.join vp01011_32 (Blocks.join vp01011_33 vp01011_34))))))
private theorem bp010110 : Branch 0 (-2815761639/256000000 : ℚ) vp01011 := by
  apply branch_left_normalized (c:=vp010110) (k:=0) (m:=2303) (by decide +kernel)
  rw [show 2*(-2815761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-2815761639/128000000 : ℚ) by norm_num]
  exact coverp010110
private noncomputable def ep010111_0 : Blocks := edgeBlocks% "full/vectors/010111-E-0000.bin"
private noncomputable def ep010111_1 : Blocks := edgeBlocks% "full/vectors/010111-E-0001.bin"
private noncomputable def ep010111_2 : Blocks := edgeBlocks% "full/vectors/010111-E-0002.bin"
private noncomputable def ep010111_3 : Blocks := edgeBlocks% "full/vectors/010111-E-0003.bin"
private noncomputable def ep010111_4 : Blocks := edgeBlocks% "full/vectors/010111-E-0004.bin"
private noncomputable def ep010111_5 : Blocks := edgeBlocks% "full/vectors/010111-E-0005.bin"
private noncomputable def ep010111_6 : Blocks := edgeBlocks% "full/vectors/010111-E-0006.bin"
private noncomputable def ep010111_7 : Blocks := edgeBlocks% "full/vectors/010111-E-0007.bin"
private noncomputable def ep010111_8 : Blocks := edgeBlocks% "full/vectors/010111-E-0008.bin"
private noncomputable def ep010111_9 : Blocks := edgeBlocks% "full/vectors/010111-E-0009.bin"
private noncomputable def ep010111_10 : Blocks := edgeBlocks% "full/vectors/010111-E-0010.bin"
private noncomputable def ep010111_11 : Blocks := edgeBlocks% "full/vectors/010111-E-0011.bin"
private noncomputable def ep010111_12 : Blocks := edgeBlocks% "full/vectors/010111-E-0012.bin"
private noncomputable def ep010111_13 : Blocks := edgeBlocks% "full/vectors/010111-E-0013.bin"
private noncomputable def ep010111_14 : Blocks := edgeBlocks% "full/vectors/010111-E-0014.bin"
private noncomputable def ep010111_15 : Blocks := edgeBlocks% "full/vectors/010111-E-0015.bin"
private noncomputable def ep010111_16 : Blocks := edgeBlocks% "full/vectors/010111-E-0016.bin"
private noncomputable def ep010111_17 : Blocks := edgeBlocks% "full/vectors/010111-E-0017.bin"
private noncomputable def ep010111_18 : Blocks := edgeBlocks% "full/vectors/010111-E-0018.bin"
private noncomputable def ep010111_19 : Blocks := edgeBlocks% "full/vectors/010111-E-0019.bin"
private noncomputable def ep010111_20 : Blocks := edgeBlocks% "full/vectors/010111-E-0020.bin"
private noncomputable def ep010111_21 : Blocks := edgeBlocks% "full/vectors/010111-E-0021.bin"
private noncomputable def ep010111_22 : Blocks := edgeBlocks% "full/vectors/010111-E-0022.bin"
private noncomputable def ep010111_23 : Blocks := edgeBlocks% "full/vectors/010111-E-0023.bin"
private noncomputable def ep010111_24 : Blocks := edgeBlocks% "full/vectors/010111-E-0024.bin"
private noncomputable def ep010111_25 : Blocks := edgeBlocks% "full/vectors/010111-E-0025.bin"
private noncomputable def ep010111_26 : Blocks := edgeBlocks% "full/vectors/010111-E-0026.bin"
private noncomputable def ep010111_27 : Blocks := edgeBlocks% "full/vectors/010111-E-0027.bin"
private noncomputable def ep010111_28 : Blocks := edgeBlocks% "full/vectors/010111-E-0028.bin"
private noncomputable def ep010111_29 : Blocks := edgeBlocks% "full/vectors/010111-E-0029.bin"
private noncomputable def ep010111_30 : Blocks := edgeBlocks% "full/vectors/010111-E-0030.bin"
private noncomputable def ep010111_31 : Blocks := edgeBlocks% "full/vectors/010111-E-0031.bin"
private noncomputable def ep010111_32 : Blocks := edgeBlocks% "full/vectors/010111-E-0032.bin"
private noncomputable def ep010111_33 : Blocks := edgeBlocks% "full/vectors/010111-E-0033.bin"
private noncomputable def ep010111_34 : Blocks := edgeBlocks% "full/vectors/010111-E-0034.bin"
noncomputable def ep010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010111_0 ep010111_1) (Blocks.join ep010111_2 ep010111_3)) (Blocks.join (Blocks.join ep010111_4 ep010111_5) (Blocks.join ep010111_6 ep010111_7))) (Blocks.join (Blocks.join (Blocks.join ep010111_8 ep010111_9) (Blocks.join ep010111_10 ep010111_11)) (Blocks.join (Blocks.join ep010111_12 ep010111_13) (Blocks.join ep010111_14 (Blocks.join ep010111_15 ep010111_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010111_17 ep010111_18) (Blocks.join ep010111_19 ep010111_20)) (Blocks.join (Blocks.join ep010111_21 ep010111_22) (Blocks.join ep010111_23 (Blocks.join ep010111_24 ep010111_25)))) (Blocks.join (Blocks.join (Blocks.join ep010111_26 ep010111_27) (Blocks.join ep010111_28 ep010111_29)) (Blocks.join (Blocks.join ep010111_30 ep010111_31) (Blocks.join ep010111_32 (Blocks.join ep010111_33 ep010111_34))))))
private def ptsp010111 : List ℤ := [((2:ℤ)^2713+0),((2:ℤ)^2713+1),((2:ℤ)^2713+2)]
private theorem boundp010111 : 2^vp01011.size*absSum vp01011.list + ((2:ℤ)^5152*absSum vp010111.list+absSum ep010111.list) < (2:ℤ)^6968 := by decide +kernel
private theorem pointp010111_0 : fastHom 1 ((2:ℤ)^2713+0) vp01011 = ((2:ℤ)^5152)*vp010111.subst ((2:ℤ)^2713+0)+ep010111.subst ((2:ℤ)^2713+0) := by decide +kernel
private theorem pointp010111_1 : fastHom 1 ((2:ℤ)^2713+1) vp01011 = ((2:ℤ)^5152)*vp010111.subst ((2:ℤ)^2713+1)+ep010111.subst ((2:ℤ)^2713+1) := by decide +kernel
private theorem pointp010111_2 : fastHom 1 ((2:ℤ)^2713+2) vp01011 = ((2:ℤ)^5152)*vp010111.subst ((2:ℤ)^2713+2)+ep010111.subst ((2:ℤ)^2713+2) := by decide +kernel
private theorem checkp010111 (x:ℤ) (hx:x ∈ ptsp010111) : fastHom 1 x vp01011 = ((2:ℤ)^5152)*vp010111.subst x+ep010111.subst x := by
  simp only [ptsp010111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp010111_0
  · exact pointp010111_1
  · exact pointp010111_2
private theorem idp010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011.list =
    C ((2:ℤ)^5152) * horner X vp010111.list + horner X ep010111.list := by
  apply edge_identity (B := (2:ℤ)^6968) (by decide) (by positivity) (by positivity) boundp010111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp010111 (by decide +kernel)
  · have h : ptsp010111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp010111.trans_le (by decide +kernel)
  · exact checkp010111
private theorem bp010111 : Branch 1 (-2815761639/256000000 : ℚ) vp01011 := by
  apply branch_checked idp010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2815761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-2943761639/128000000 : ℚ) by norm_num]
  exact coverp010111
theorem coverp01011 : Covers (-2815761639/256000000 : ℚ) vp01011 := join_branches bp010110 bp010111
end NextProof.EdgeFull

