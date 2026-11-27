import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00081

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001110111111_0 : Blocks := edgeBlocks% "full/vectors/0001110111111-V-0000.bin"
noncomputable def vp0001110111111 : Blocks := vp0001110111111_0
theorem coverp0001110111111 : Covers (-958761639/1000000 : ℚ) vp0001110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110111110_0 : Blocks := edgeBlocks% "full/vectors/0001110111110-V-0000.bin"
noncomputable def vp0001110111110 : Blocks := vp0001110111110_0
theorem coverp0001110111110 : Covers (-957761639/1000000 : ℚ) vp0001110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011111_0 : Blocks := edgeBlocks% "full/vectors/000111011111-V-0000.bin"
noncomputable def vp000111011111 : Blocks := vp000111011111_0
private theorem bp0001110111110 : Branch 0 (-957761639/2000000 : ℚ) vp000111011111 := by
  apply branch_left_normalized (c:=vp0001110111110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-957761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-957761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111110
private noncomputable def ep0001110111111_0 : Blocks := edgeBlocks% "full/vectors/0001110111111-E-0000.bin"
noncomputable def ep0001110111111 : Blocks := ep0001110111111_0
private theorem idp0001110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011111.list =
    C ((2:ℤ)^92) * horner X vp0001110111111.list + horner X ep0001110111111.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110111111 : Branch 1 (-957761639/2000000 : ℚ) vp000111011111 := by
  apply branch_checked idp0001110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-957761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-958761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111111
theorem coverp000111011111 : Covers (-957761639/2000000 : ℚ) vp000111011111 := join_branches bp0001110111110 bp0001110111111
private noncomputable def vp0001110111101_0 : Blocks := edgeBlocks% "full/vectors/0001110111101-V-0000.bin"
noncomputable def vp0001110111101 : Blocks := vp0001110111101_0
theorem coverp0001110111101 : Covers (-956761639/1000000 : ℚ) vp0001110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011101111001_0 : Blocks := edgeBlocks% "full/vectors/00011101111001-V-0000.bin"
noncomputable def vp00011101111001 : Blocks := vp00011101111001_0
theorem coverp00011101111001 : Covers (-956261639/500000 : ℚ) vp00011101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011101111000_0 : Blocks := edgeBlocks% "full/vectors/00011101111000-V-0000.bin"
noncomputable def vp00011101111000 : Blocks := vp00011101111000_0
theorem coverp00011101111000 : Covers (-955761639/500000 : ℚ) vp00011101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110111100_0 : Blocks := edgeBlocks% "full/vectors/0001110111100-V-0000.bin"
noncomputable def vp0001110111100 : Blocks := vp0001110111100_0
private theorem bp00011101111000 : Branch 0 (-955761639/1000000 : ℚ) vp0001110111100 := by
  apply branch_left_normalized (c:=vp00011101111000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-955761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-955761639/500000 : ℚ) by norm_num]
  exact coverp00011101111000
private noncomputable def ep00011101111001_0 : Blocks := edgeBlocks% "full/vectors/00011101111001-E-0000.bin"
noncomputable def ep00011101111001 : Blocks := ep00011101111001_0
private theorem idp00011101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110111100.list =
    C ((2:ℤ)^53) * horner X vp00011101111001.list + horner X ep00011101111001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101111001 : Branch 1 (-955761639/1000000 : ℚ) vp0001110111100 := by
  apply branch_checked idp00011101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-955761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-956261639/500000 : ℚ) by norm_num]
  exact coverp00011101111001
theorem coverp0001110111100 : Covers (-955761639/1000000 : ℚ) vp0001110111100 := join_branches bp00011101111000 bp00011101111001
private noncomputable def vp000111011110_0 : Blocks := edgeBlocks% "full/vectors/000111011110-V-0000.bin"
noncomputable def vp000111011110 : Blocks := vp000111011110_0
private theorem bp0001110111100 : Branch 0 (-955761639/2000000 : ℚ) vp000111011110 := by
  apply branch_left_normalized (c:=vp0001110111100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-955761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-955761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111100
private noncomputable def ep0001110111101_0 : Blocks := edgeBlocks% "full/vectors/0001110111101-E-0000.bin"
noncomputable def ep0001110111101 : Blocks := ep0001110111101_0
private theorem idp0001110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011110.list =
    C ((2:ℤ)^89) * horner X vp0001110111101.list + horner X ep0001110111101.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110111101 : Branch 1 (-955761639/2000000 : ℚ) vp000111011110 := by
  apply branch_checked idp0001110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-955761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-956761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111101
theorem coverp000111011110 : Covers (-955761639/2000000 : ℚ) vp000111011110 := join_branches bp0001110111100 bp0001110111101
private noncomputable def vp00011101111_0 : Blocks := edgeBlocks% "full/vectors/00011101111-V-0000.bin"
private noncomputable def vp00011101111_1 : Blocks := edgeBlocks% "full/vectors/00011101111-V-0001.bin"
noncomputable def vp00011101111 : Blocks := (Blocks.join vp00011101111_0 vp00011101111_1)
private theorem bp000111011110 : Branch 0 (-955761639/4000000 : ℚ) vp00011101111 := by
  apply branch_left_normalized (c:=vp000111011110) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-955761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-955761639/2000000 : ℚ) by norm_num]
  exact coverp000111011110
private noncomputable def ep000111011111_0 : Blocks := edgeBlocks% "full/vectors/000111011111-E-0000.bin"
private noncomputable def ep000111011111_1 : Blocks := edgeBlocks% "full/vectors/000111011111-E-0001.bin"
noncomputable def ep000111011111 : Blocks := (Blocks.join ep000111011111_0 ep000111011111_1)
private theorem idp000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101111.list =
    C ((2:ℤ)^160) * horner X vp000111011111.list + horner X ep000111011111.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111011111 : Branch 1 (-955761639/4000000 : ℚ) vp00011101111 := by
  apply branch_checked idp000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-955761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-957761639/2000000 : ℚ) by norm_num]
  exact coverp000111011111
theorem coverp00011101111 : Covers (-955761639/4000000 : ℚ) vp00011101111 := join_branches bp000111011110 bp000111011111
private noncomputable def vp0001110111011_0 : Blocks := edgeBlocks% "full/vectors/0001110111011-V-0000.bin"
noncomputable def vp0001110111011 : Blocks := vp0001110111011_0
theorem coverp0001110111011 : Covers (-954761639/1000000 : ℚ) vp0001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110111010_0 : Blocks := edgeBlocks% "full/vectors/0001110111010-V-0000.bin"
noncomputable def vp0001110111010 : Blocks := vp0001110111010_0
theorem coverp0001110111010 : Covers (-953761639/1000000 : ℚ) vp0001110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011101_0 : Blocks := edgeBlocks% "full/vectors/000111011101-V-0000.bin"
noncomputable def vp000111011101 : Blocks := vp000111011101_0
private theorem bp0001110111010 : Branch 0 (-953761639/2000000 : ℚ) vp000111011101 := by
  apply branch_left_normalized (c:=vp0001110111010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-953761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-953761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111010
private noncomputable def ep0001110111011_0 : Blocks := edgeBlocks% "full/vectors/0001110111011-E-0000.bin"
noncomputable def ep0001110111011 : Blocks := ep0001110111011_0
private theorem idp0001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011101.list =
    C ((2:ℤ)^88) * horner X vp0001110111011.list + horner X ep0001110111011.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110111011 : Branch 1 (-953761639/2000000 : ℚ) vp000111011101 := by
  apply branch_checked idp0001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-953761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-954761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111011
theorem coverp000111011101 : Covers (-953761639/2000000 : ℚ) vp000111011101 := join_branches bp0001110111010 bp0001110111011
private noncomputable def vp0001110111001_0 : Blocks := edgeBlocks% "full/vectors/0001110111001-V-0000.bin"
noncomputable def vp0001110111001 : Blocks := vp0001110111001_0
theorem coverp0001110111001 : Covers (-952761639/1000000 : ℚ) vp0001110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110111000_0 : Blocks := edgeBlocks% "full/vectors/0001110111000-V-0000.bin"
noncomputable def vp0001110111000 : Blocks := vp0001110111000_0
theorem coverp0001110111000 : Covers (-951761639/1000000 : ℚ) vp0001110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011100_0 : Blocks := edgeBlocks% "full/vectors/000111011100-V-0000.bin"
noncomputable def vp000111011100 : Blocks := vp000111011100_0
private theorem bp0001110111000 : Branch 0 (-951761639/2000000 : ℚ) vp000111011100 := by
  apply branch_left_normalized (c:=vp0001110111000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-951761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-951761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111000
private noncomputable def ep0001110111001_0 : Blocks := edgeBlocks% "full/vectors/0001110111001-E-0000.bin"
noncomputable def ep0001110111001 : Blocks := ep0001110111001_0
private theorem idp0001110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011100.list =
    C ((2:ℤ)^88) * horner X vp0001110111001.list + horner X ep0001110111001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110111001 : Branch 1 (-951761639/2000000 : ℚ) vp000111011100 := by
  apply branch_checked idp0001110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-951761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-952761639/1000000 : ℚ) by norm_num]
  exact coverp0001110111001
theorem coverp000111011100 : Covers (-951761639/2000000 : ℚ) vp000111011100 := join_branches bp0001110111000 bp0001110111001
private noncomputable def vp00011101110_0 : Blocks := edgeBlocks% "full/vectors/00011101110-V-0000.bin"
private noncomputable def vp00011101110_1 : Blocks := edgeBlocks% "full/vectors/00011101110-V-0001.bin"
noncomputable def vp00011101110 : Blocks := (Blocks.join vp00011101110_0 vp00011101110_1)
private theorem bp000111011100 : Branch 0 (-951761639/4000000 : ℚ) vp00011101110 := by
  apply branch_left_normalized (c:=vp000111011100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-951761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-951761639/2000000 : ℚ) by norm_num]
  exact coverp000111011100
private noncomputable def ep000111011101_0 : Blocks := edgeBlocks% "full/vectors/000111011101-E-0000.bin"
private noncomputable def ep000111011101_1 : Blocks := edgeBlocks% "full/vectors/000111011101-E-0001.bin"
noncomputable def ep000111011101 : Blocks := (Blocks.join ep000111011101_0 ep000111011101_1)
private theorem idp000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101110.list =
    C ((2:ℤ)^157) * horner X vp000111011101.list + horner X ep000111011101.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111011101 : Branch 1 (-951761639/4000000 : ℚ) vp00011101110 := by
  apply branch_checked idp000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-951761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-953761639/2000000 : ℚ) by norm_num]
  exact coverp000111011101
theorem coverp00011101110 : Covers (-951761639/4000000 : ℚ) vp00011101110 := join_branches bp000111011100 bp000111011101
private noncomputable def vp0001110111_0 : Blocks := edgeBlocks% "full/vectors/0001110111-V-0000.bin"
private noncomputable def vp0001110111_1 : Blocks := edgeBlocks% "full/vectors/0001110111-V-0001.bin"
private noncomputable def vp0001110111_2 : Blocks := edgeBlocks% "full/vectors/0001110111-V-0002.bin"
noncomputable def vp0001110111 : Blocks := (Blocks.join vp0001110111_0 (Blocks.join vp0001110111_1 vp0001110111_2))
private theorem bp00011101110 : Branch 0 (-951761639/8000000 : ℚ) vp0001110111 := by
  apply branch_left_normalized (c:=vp00011101110) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-951761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-951761639/4000000 : ℚ) by norm_num]
  exact coverp00011101110
private noncomputable def ep00011101111_0 : Blocks := edgeBlocks% "full/vectors/00011101111-E-0000.bin"
private noncomputable def ep00011101111_1 : Blocks := edgeBlocks% "full/vectors/00011101111-E-0001.bin"
private noncomputable def ep00011101111_2 : Blocks := edgeBlocks% "full/vectors/00011101111-E-0002.bin"
noncomputable def ep00011101111 : Blocks := (Blocks.join ep00011101111_0 (Blocks.join ep00011101111_1 ep00011101111_2))
private theorem idp00011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110111.list =
    C ((2:ℤ)^294) * horner X vp00011101111.list + horner X ep00011101111.list := by
  exact edge_identity (B := (2:ℤ)^506) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101111 : Branch 1 (-951761639/8000000 : ℚ) vp0001110111 := by
  apply branch_checked idp00011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-951761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-955761639/4000000 : ℚ) by norm_num]
  exact coverp00011101111
theorem coverp0001110111 : Covers (-951761639/8000000 : ℚ) vp0001110111 := join_branches bp00011101110 bp00011101111
private noncomputable def vp0001110110111_0 : Blocks := edgeBlocks% "full/vectors/0001110110111-V-0000.bin"
noncomputable def vp0001110110111 : Blocks := vp0001110110111_0
theorem coverp0001110110111 : Covers (-950761639/1000000 : ℚ) vp0001110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110110110_0 : Blocks := edgeBlocks% "full/vectors/0001110110110-V-0000.bin"
noncomputable def vp0001110110110 : Blocks := vp0001110110110_0
theorem coverp0001110110110 : Covers (-949761639/1000000 : ℚ) vp0001110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011011_0 : Blocks := edgeBlocks% "full/vectors/000111011011-V-0000.bin"
noncomputable def vp000111011011 : Blocks := vp000111011011_0
private theorem bp0001110110110 : Branch 0 (-949761639/2000000 : ℚ) vp000111011011 := by
  apply branch_left_normalized (c:=vp0001110110110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-949761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-949761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110110
private noncomputable def ep0001110110111_0 : Blocks := edgeBlocks% "full/vectors/0001110110111-E-0000.bin"
noncomputable def ep0001110110111 : Blocks := ep0001110110111_0
private theorem idp0001110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011011.list =
    C ((2:ℤ)^89) * horner X vp0001110110111.list + horner X ep0001110110111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110110111 : Branch 1 (-949761639/2000000 : ℚ) vp000111011011 := by
  apply branch_checked idp0001110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-949761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-950761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110111
theorem coverp000111011011 : Covers (-949761639/2000000 : ℚ) vp000111011011 := join_branches bp0001110110110 bp0001110110111
private noncomputable def vp0001110110101_0 : Blocks := edgeBlocks% "full/vectors/0001110110101-V-0000.bin"
noncomputable def vp0001110110101 : Blocks := vp0001110110101_0
theorem coverp0001110110101 : Covers (-948761639/1000000 : ℚ) vp0001110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110110100_0 : Blocks := edgeBlocks% "full/vectors/0001110110100-V-0000.bin"
noncomputable def vp0001110110100 : Blocks := vp0001110110100_0
theorem coverp0001110110100 : Covers (-947761639/1000000 : ℚ) vp0001110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011010_0 : Blocks := edgeBlocks% "full/vectors/000111011010-V-0000.bin"
noncomputable def vp000111011010 : Blocks := vp000111011010_0
private theorem bp0001110110100 : Branch 0 (-947761639/2000000 : ℚ) vp000111011010 := by
  apply branch_left_normalized (c:=vp0001110110100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-947761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-947761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110100
private noncomputable def ep0001110110101_0 : Blocks := edgeBlocks% "full/vectors/0001110110101-E-0000.bin"
noncomputable def ep0001110110101 : Blocks := ep0001110110101_0
private theorem idp0001110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011010.list =
    C ((2:ℤ)^89) * horner X vp0001110110101.list + horner X ep0001110110101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110110101 : Branch 1 (-947761639/2000000 : ℚ) vp000111011010 := by
  apply branch_checked idp0001110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-947761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-948761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110101
theorem coverp000111011010 : Covers (-947761639/2000000 : ℚ) vp000111011010 := join_branches bp0001110110100 bp0001110110101
private noncomputable def vp00011101101_0 : Blocks := edgeBlocks% "full/vectors/00011101101-V-0000.bin"
private noncomputable def vp00011101101_1 : Blocks := edgeBlocks% "full/vectors/00011101101-V-0001.bin"
noncomputable def vp00011101101 : Blocks := (Blocks.join vp00011101101_0 vp00011101101_1)
private theorem bp000111011010 : Branch 0 (-947761639/4000000 : ℚ) vp00011101101 := by
  apply branch_left_normalized (c:=vp000111011010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-947761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-947761639/2000000 : ℚ) by norm_num]
  exact coverp000111011010
private noncomputable def ep000111011011_0 : Blocks := edgeBlocks% "full/vectors/000111011011-E-0000.bin"
private noncomputable def ep000111011011_1 : Blocks := edgeBlocks% "full/vectors/000111011011-E-0001.bin"
noncomputable def ep000111011011 : Blocks := (Blocks.join ep000111011011_0 ep000111011011_1)
private theorem idp000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101101.list =
    C ((2:ℤ)^160) * horner X vp000111011011.list + horner X ep000111011011.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111011011 : Branch 1 (-947761639/4000000 : ℚ) vp00011101101 := by
  apply branch_checked idp000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-947761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-949761639/2000000 : ℚ) by norm_num]
  exact coverp000111011011
theorem coverp00011101101 : Covers (-947761639/4000000 : ℚ) vp00011101101 := join_branches bp000111011010 bp000111011011
private noncomputable def vp0001110110011_0 : Blocks := edgeBlocks% "full/vectors/0001110110011-V-0000.bin"
noncomputable def vp0001110110011 : Blocks := vp0001110110011_0
theorem coverp0001110110011 : Covers (-946761639/1000000 : ℚ) vp0001110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110110010_0 : Blocks := edgeBlocks% "full/vectors/0001110110010-V-0000.bin"
noncomputable def vp0001110110010 : Blocks := vp0001110110010_0
theorem coverp0001110110010 : Covers (-945761639/1000000 : ℚ) vp0001110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011001_0 : Blocks := edgeBlocks% "full/vectors/000111011001-V-0000.bin"
noncomputable def vp000111011001 : Blocks := vp000111011001_0
private theorem bp0001110110010 : Branch 0 (-945761639/2000000 : ℚ) vp000111011001 := by
  apply branch_left_normalized (c:=vp0001110110010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-945761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-945761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110010
private noncomputable def ep0001110110011_0 : Blocks := edgeBlocks% "full/vectors/0001110110011-E-0000.bin"
noncomputable def ep0001110110011 : Blocks := ep0001110110011_0
private theorem idp0001110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011001.list =
    C ((2:ℤ)^86) * horner X vp0001110110011.list + horner X ep0001110110011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110110011 : Branch 1 (-945761639/2000000 : ℚ) vp000111011001 := by
  apply branch_checked idp0001110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-945761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-946761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110011
theorem coverp000111011001 : Covers (-945761639/2000000 : ℚ) vp000111011001 := join_branches bp0001110110010 bp0001110110011
private noncomputable def vp0001110110001_0 : Blocks := edgeBlocks% "full/vectors/0001110110001-V-0000.bin"
noncomputable def vp0001110110001 : Blocks := vp0001110110001_0
theorem coverp0001110110001 : Covers (-944761639/1000000 : ℚ) vp0001110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110110000_0 : Blocks := edgeBlocks% "full/vectors/0001110110000-V-0000.bin"
noncomputable def vp0001110110000 : Blocks := vp0001110110000_0
theorem coverp0001110110000 : Covers (-943761639/1000000 : ℚ) vp0001110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111011000_0 : Blocks := edgeBlocks% "full/vectors/000111011000-V-0000.bin"
noncomputable def vp000111011000 : Blocks := vp000111011000_0
private theorem bp0001110110000 : Branch 0 (-943761639/2000000 : ℚ) vp000111011000 := by
  apply branch_left_normalized (c:=vp0001110110000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-943761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-943761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110000
private noncomputable def ep0001110110001_0 : Blocks := edgeBlocks% "full/vectors/0001110110001-E-0000.bin"
noncomputable def ep0001110110001 : Blocks := ep0001110110001_0
private theorem idp0001110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011000.list =
    C ((2:ℤ)^86) * horner X vp0001110110001.list + horner X ep0001110110001.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110110001 : Branch 1 (-943761639/2000000 : ℚ) vp000111011000 := by
  apply branch_checked idp0001110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-943761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-944761639/1000000 : ℚ) by norm_num]
  exact coverp0001110110001
theorem coverp000111011000 : Covers (-943761639/2000000 : ℚ) vp000111011000 := join_branches bp0001110110000 bp0001110110001
private noncomputable def vp00011101100_0 : Blocks := edgeBlocks% "full/vectors/00011101100-V-0000.bin"
private noncomputable def vp00011101100_1 : Blocks := edgeBlocks% "full/vectors/00011101100-V-0001.bin"
noncomputable def vp00011101100 : Blocks := (Blocks.join vp00011101100_0 vp00011101100_1)
private theorem bp000111011000 : Branch 0 (-943761639/4000000 : ℚ) vp00011101100 := by
  apply branch_left_normalized (c:=vp000111011000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-943761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-943761639/2000000 : ℚ) by norm_num]
  exact coverp000111011000
private noncomputable def ep000111011001_0 : Blocks := edgeBlocks% "full/vectors/000111011001-E-0000.bin"
private noncomputable def ep000111011001_1 : Blocks := edgeBlocks% "full/vectors/000111011001-E-0001.bin"
noncomputable def ep000111011001 : Blocks := (Blocks.join ep000111011001_0 ep000111011001_1)
private theorem idp000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101100.list =
    C ((2:ℤ)^156) * horner X vp000111011001.list + horner X ep000111011001.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111011001 : Branch 1 (-943761639/4000000 : ℚ) vp00011101100 := by
  apply branch_checked idp000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-943761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-945761639/2000000 : ℚ) by norm_num]
  exact coverp000111011001
theorem coverp00011101100 : Covers (-943761639/4000000 : ℚ) vp00011101100 := join_branches bp000111011000 bp000111011001
private noncomputable def vp0001110110_0 : Blocks := edgeBlocks% "full/vectors/0001110110-V-0000.bin"
private noncomputable def vp0001110110_1 : Blocks := edgeBlocks% "full/vectors/0001110110-V-0001.bin"
private noncomputable def vp0001110110_2 : Blocks := edgeBlocks% "full/vectors/0001110110-V-0002.bin"
noncomputable def vp0001110110 : Blocks := (Blocks.join vp0001110110_0 (Blocks.join vp0001110110_1 vp0001110110_2))
private theorem bp00011101100 : Branch 0 (-943761639/8000000 : ℚ) vp0001110110 := by
  apply branch_left_normalized (c:=vp00011101100) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-943761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-943761639/4000000 : ℚ) by norm_num]
  exact coverp00011101100
private noncomputable def ep00011101101_0 : Blocks := edgeBlocks% "full/vectors/00011101101-E-0000.bin"
private noncomputable def ep00011101101_1 : Blocks := edgeBlocks% "full/vectors/00011101101-E-0001.bin"
private noncomputable def ep00011101101_2 : Blocks := edgeBlocks% "full/vectors/00011101101-E-0002.bin"
noncomputable def ep00011101101 : Blocks := (Blocks.join ep00011101101_0 (Blocks.join ep00011101101_1 ep00011101101_2))
private theorem idp00011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110110.list =
    C ((2:ℤ)^292) * horner X vp00011101101.list + horner X ep00011101101.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101101 : Branch 1 (-943761639/8000000 : ℚ) vp0001110110 := by
  apply branch_checked idp00011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-943761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-947761639/4000000 : ℚ) by norm_num]
  exact coverp00011101101
theorem coverp0001110110 : Covers (-943761639/8000000 : ℚ) vp0001110110 := join_branches bp00011101100 bp00011101101
private noncomputable def vp000111011_0 : Blocks := edgeBlocks% "full/vectors/000111011-V-0000.bin"
private noncomputable def vp000111011_1 : Blocks := edgeBlocks% "full/vectors/000111011-V-0001.bin"
private noncomputable def vp000111011_2 : Blocks := edgeBlocks% "full/vectors/000111011-V-0002.bin"
private noncomputable def vp000111011_3 : Blocks := edgeBlocks% "full/vectors/000111011-V-0003.bin"
private noncomputable def vp000111011_4 : Blocks := edgeBlocks% "full/vectors/000111011-V-0004.bin"
noncomputable def vp000111011 : Blocks := (Blocks.join (Blocks.join vp000111011_0 vp000111011_1) (Blocks.join vp000111011_2 (Blocks.join vp000111011_3 vp000111011_4)))
private theorem bp0001110110 : Branch 0 (-943761639/16000000 : ℚ) vp000111011 := by
  apply branch_left_normalized (c:=vp0001110110) (k:=0) (m:=272) (by decide +kernel)
  rw [show 2*(-943761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-943761639/8000000 : ℚ) by norm_num]
  exact coverp0001110110
private noncomputable def ep0001110111_0 : Blocks := edgeBlocks% "full/vectors/0001110111-E-0000.bin"
private noncomputable def ep0001110111_1 : Blocks := edgeBlocks% "full/vectors/0001110111-E-0001.bin"
private noncomputable def ep0001110111_2 : Blocks := edgeBlocks% "full/vectors/0001110111-E-0002.bin"
private noncomputable def ep0001110111_3 : Blocks := edgeBlocks% "full/vectors/0001110111-E-0003.bin"
private noncomputable def ep0001110111_4 : Blocks := edgeBlocks% "full/vectors/0001110111-E-0004.bin"
noncomputable def ep0001110111 : Blocks := (Blocks.join (Blocks.join ep0001110111_0 ep0001110111_1) (Blocks.join ep0001110111_2 (Blocks.join ep0001110111_3 ep0001110111_4)))
private theorem idp0001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111011.list =
    C ((2:ℤ)^569) * horner X vp0001110111.list + horner X ep0001110111.list := by
  exact edge_identity (B := (2:ℤ)^890) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110111 : Branch 1 (-943761639/16000000 : ℚ) vp000111011 := by
  apply branch_checked idp0001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-943761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-951761639/8000000 : ℚ) by norm_num]
  exact coverp0001110111
theorem coverp000111011 : Covers (-943761639/16000000 : ℚ) vp000111011 := join_branches bp0001110110 bp0001110111
private noncomputable def vp0001110101111_0 : Blocks := edgeBlocks% "full/vectors/0001110101111-V-0000.bin"
noncomputable def vp0001110101111 : Blocks := vp0001110101111_0
theorem coverp0001110101111 : Covers (-942761639/1000000 : ℚ) vp0001110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110101110_0 : Blocks := edgeBlocks% "full/vectors/0001110101110-V-0000.bin"
noncomputable def vp0001110101110 : Blocks := vp0001110101110_0
theorem coverp0001110101110 : Covers (-941761639/1000000 : ℚ) vp0001110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111010111_0 : Blocks := edgeBlocks% "full/vectors/000111010111-V-0000.bin"
noncomputable def vp000111010111 : Blocks := vp000111010111_0
private theorem bp0001110101110 : Branch 0 (-941761639/2000000 : ℚ) vp000111010111 := by
  apply branch_left_normalized (c:=vp0001110101110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-941761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-941761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101110
private noncomputable def ep0001110101111_0 : Blocks := edgeBlocks% "full/vectors/0001110101111-E-0000.bin"
noncomputable def ep0001110101111 : Blocks := ep0001110101111_0
private theorem idp0001110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111010111.list =
    C ((2:ℤ)^86) * horner X vp0001110101111.list + horner X ep0001110101111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110101111 : Branch 1 (-941761639/2000000 : ℚ) vp000111010111 := by
  apply branch_checked idp0001110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-941761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-942761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101111
theorem coverp000111010111 : Covers (-941761639/2000000 : ℚ) vp000111010111 := join_branches bp0001110101110 bp0001110101111
private noncomputable def vp0001110101101_0 : Blocks := edgeBlocks% "full/vectors/0001110101101-V-0000.bin"
noncomputable def vp0001110101101 : Blocks := vp0001110101101_0
theorem coverp0001110101101 : Covers (-940761639/1000000 : ℚ) vp0001110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110101100_0 : Blocks := edgeBlocks% "full/vectors/0001110101100-V-0000.bin"
noncomputable def vp0001110101100 : Blocks := vp0001110101100_0
theorem coverp0001110101100 : Covers (-939761639/1000000 : ℚ) vp0001110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111010110_0 : Blocks := edgeBlocks% "full/vectors/000111010110-V-0000.bin"
noncomputable def vp000111010110 : Blocks := vp000111010110_0
private theorem bp0001110101100 : Branch 0 (-939761639/2000000 : ℚ) vp000111010110 := by
  apply branch_left_normalized (c:=vp0001110101100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-939761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-939761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101100
private noncomputable def ep0001110101101_0 : Blocks := edgeBlocks% "full/vectors/0001110101101-E-0000.bin"
noncomputable def ep0001110101101 : Blocks := ep0001110101101_0
private theorem idp0001110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111010110.list =
    C ((2:ℤ)^85) * horner X vp0001110101101.list + horner X ep0001110101101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110101101 : Branch 1 (-939761639/2000000 : ℚ) vp000111010110 := by
  apply branch_checked idp0001110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-939761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-940761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101101
theorem coverp000111010110 : Covers (-939761639/2000000 : ℚ) vp000111010110 := join_branches bp0001110101100 bp0001110101101
private noncomputable def vp00011101011_0 : Blocks := edgeBlocks% "full/vectors/00011101011-V-0000.bin"
private noncomputable def vp00011101011_1 : Blocks := edgeBlocks% "full/vectors/00011101011-V-0001.bin"
noncomputable def vp00011101011 : Blocks := (Blocks.join vp00011101011_0 vp00011101011_1)
private theorem bp000111010110 : Branch 0 (-939761639/4000000 : ℚ) vp00011101011 := by
  apply branch_left_normalized (c:=vp000111010110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-939761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-939761639/2000000 : ℚ) by norm_num]
  exact coverp000111010110
private noncomputable def ep000111010111_0 : Blocks := edgeBlocks% "full/vectors/000111010111-E-0000.bin"
private noncomputable def ep000111010111_1 : Blocks := edgeBlocks% "full/vectors/000111010111-E-0001.bin"
noncomputable def ep000111010111 : Blocks := (Blocks.join ep000111010111_0 ep000111010111_1)
private theorem idp000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101011.list =
    C ((2:ℤ)^156) * horner X vp000111010111.list + horner X ep000111010111.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111010111 : Branch 1 (-939761639/4000000 : ℚ) vp00011101011 := by
  apply branch_checked idp000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-939761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-941761639/2000000 : ℚ) by norm_num]
  exact coverp000111010111
theorem coverp00011101011 : Covers (-939761639/4000000 : ℚ) vp00011101011 := join_branches bp000111010110 bp000111010111
private noncomputable def vp0001110101011_0 : Blocks := edgeBlocks% "full/vectors/0001110101011-V-0000.bin"
noncomputable def vp0001110101011 : Blocks := vp0001110101011_0
theorem coverp0001110101011 : Covers (-938761639/1000000 : ℚ) vp0001110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110101010_0 : Blocks := edgeBlocks% "full/vectors/0001110101010-V-0000.bin"
noncomputable def vp0001110101010 : Blocks := vp0001110101010_0
theorem coverp0001110101010 : Covers (-937761639/1000000 : ℚ) vp0001110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111010101_0 : Blocks := edgeBlocks% "full/vectors/000111010101-V-0000.bin"
noncomputable def vp000111010101 : Blocks := vp000111010101_0
private theorem bp0001110101010 : Branch 0 (-937761639/2000000 : ℚ) vp000111010101 := by
  apply branch_left_normalized (c:=vp0001110101010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-937761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-937761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101010
private noncomputable def ep0001110101011_0 : Blocks := edgeBlocks% "full/vectors/0001110101011-E-0000.bin"
noncomputable def ep0001110101011 : Blocks := ep0001110101011_0
private theorem idp0001110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111010101.list =
    C ((2:ℤ)^86) * horner X vp0001110101011.list + horner X ep0001110101011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110101011 : Branch 1 (-937761639/2000000 : ℚ) vp000111010101 := by
  apply branch_checked idp0001110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-937761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-938761639/1000000 : ℚ) by norm_num]
  exact coverp0001110101011
theorem coverp000111010101 : Covers (-937761639/2000000 : ℚ) vp000111010101 := join_branches bp0001110101010 bp0001110101011
private noncomputable def vp000111010100_0 : Blocks := edgeBlocks% "full/vectors/000111010100-V-0000.bin"
noncomputable def vp000111010100 : Blocks := vp000111010100_0
theorem coverp000111010100 : Covers (-935761639/2000000 : ℚ) vp000111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00011101010_0 : Blocks := edgeBlocks% "full/vectors/00011101010-V-0000.bin"
private noncomputable def vp00011101010_1 : Blocks := edgeBlocks% "full/vectors/00011101010-V-0001.bin"
noncomputable def vp00011101010 : Blocks := (Blocks.join vp00011101010_0 vp00011101010_1)
private theorem bp000111010100 : Branch 0 (-935761639/4000000 : ℚ) vp00011101010 := by
  apply branch_left_normalized (c:=vp000111010100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-935761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-935761639/2000000 : ℚ) by norm_num]
  exact coverp000111010100
private noncomputable def ep000111010101_0 : Blocks := edgeBlocks% "full/vectors/000111010101-E-0000.bin"
private noncomputable def ep000111010101_1 : Blocks := edgeBlocks% "full/vectors/000111010101-E-0001.bin"
noncomputable def ep000111010101 : Blocks := (Blocks.join ep000111010101_0 ep000111010101_1)
private theorem idp000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101010.list =
    C ((2:ℤ)^156) * horner X vp000111010101.list + horner X ep000111010101.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111010101 : Branch 1 (-935761639/4000000 : ℚ) vp00011101010 := by
  apply branch_checked idp000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-935761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-937761639/2000000 : ℚ) by norm_num]
  exact coverp000111010101
theorem coverp00011101010 : Covers (-935761639/4000000 : ℚ) vp00011101010 := join_branches bp000111010100 bp000111010101
private noncomputable def vp0001110101_0 : Blocks := edgeBlocks% "full/vectors/0001110101-V-0000.bin"
private noncomputable def vp0001110101_1 : Blocks := edgeBlocks% "full/vectors/0001110101-V-0001.bin"
private noncomputable def vp0001110101_2 : Blocks := edgeBlocks% "full/vectors/0001110101-V-0002.bin"
noncomputable def vp0001110101 : Blocks := (Blocks.join vp0001110101_0 (Blocks.join vp0001110101_1 vp0001110101_2))
private theorem bp00011101010 : Branch 0 (-935761639/8000000 : ℚ) vp0001110101 := by
  apply branch_left_normalized (c:=vp00011101010) (k:=0) (m:=144) (by decide +kernel)
  rw [show 2*(-935761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-935761639/4000000 : ℚ) by norm_num]
  exact coverp00011101010
private noncomputable def ep00011101011_0 : Blocks := edgeBlocks% "full/vectors/00011101011-E-0000.bin"
private noncomputable def ep00011101011_1 : Blocks := edgeBlocks% "full/vectors/00011101011-E-0001.bin"
private noncomputable def ep00011101011_2 : Blocks := edgeBlocks% "full/vectors/00011101011-E-0002.bin"
noncomputable def ep00011101011 : Blocks := (Blocks.join ep00011101011_0 (Blocks.join ep00011101011_1 ep00011101011_2))
private theorem idp00011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110101.list =
    C ((2:ℤ)^295) * horner X vp00011101011.list + horner X ep00011101011.list := by
  exact edge_identity (B := (2:ℤ)^499) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101011 : Branch 1 (-935761639/8000000 : ℚ) vp0001110101 := by
  apply branch_checked idp00011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-935761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-939761639/4000000 : ℚ) by norm_num]
  exact coverp00011101011
theorem coverp0001110101 : Covers (-935761639/8000000 : ℚ) vp0001110101 := join_branches bp00011101010 bp00011101011
private noncomputable def vp000111010011_0 : Blocks := edgeBlocks% "full/vectors/000111010011-V-0000.bin"
noncomputable def vp000111010011 : Blocks := vp000111010011_0
theorem coverp000111010011 : Covers (-933761639/2000000 : ℚ) vp000111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000111010010_0 : Blocks := edgeBlocks% "full/vectors/000111010010-V-0000.bin"
noncomputable def vp000111010010 : Blocks := vp000111010010_0
theorem coverp000111010010 : Covers (-931761639/2000000 : ℚ) vp000111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00011101001_0 : Blocks := edgeBlocks% "full/vectors/00011101001-V-0000.bin"
private noncomputable def vp00011101001_1 : Blocks := edgeBlocks% "full/vectors/00011101001-V-0001.bin"
noncomputable def vp00011101001 : Blocks := (Blocks.join vp00011101001_0 vp00011101001_1)
private theorem bp000111010010 : Branch 0 (-931761639/4000000 : ℚ) vp00011101001 := by
  apply branch_left_normalized (c:=vp000111010010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-931761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-931761639/2000000 : ℚ) by norm_num]
  exact coverp000111010010
private noncomputable def ep000111010011_0 : Blocks := edgeBlocks% "full/vectors/000111010011-E-0000.bin"
private noncomputable def ep000111010011_1 : Blocks := edgeBlocks% "full/vectors/000111010011-E-0001.bin"
noncomputable def ep000111010011 : Blocks := (Blocks.join ep000111010011_0 ep000111010011_1)
private theorem idp000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101001.list =
    C ((2:ℤ)^156) * horner X vp000111010011.list + horner X ep000111010011.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111010011 : Branch 1 (-931761639/4000000 : ℚ) vp00011101001 := by
  apply branch_checked idp000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-931761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-933761639/2000000 : ℚ) by norm_num]
  exact coverp000111010011
theorem coverp00011101001 : Covers (-931761639/4000000 : ℚ) vp00011101001 := join_branches bp000111010010 bp000111010011
private noncomputable def vp000111010001_0 : Blocks := edgeBlocks% "full/vectors/000111010001-V-0000.bin"
noncomputable def vp000111010001 : Blocks := vp000111010001_0
theorem coverp000111010001 : Covers (-929761639/2000000 : ℚ) vp000111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000111010000_0 : Blocks := edgeBlocks% "full/vectors/000111010000-V-0000.bin"
noncomputable def vp000111010000 : Blocks := vp000111010000_0
theorem coverp000111010000 : Covers (-927761639/2000000 : ℚ) vp000111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00011101000_0 : Blocks := edgeBlocks% "full/vectors/00011101000-V-0000.bin"
private noncomputable def vp00011101000_1 : Blocks := edgeBlocks% "full/vectors/00011101000-V-0001.bin"
noncomputable def vp00011101000 : Blocks := (Blocks.join vp00011101000_0 vp00011101000_1)
private theorem bp000111010000 : Branch 0 (-927761639/4000000 : ℚ) vp00011101000 := by
  apply branch_left_normalized (c:=vp000111010000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-927761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-927761639/2000000 : ℚ) by norm_num]
  exact coverp000111010000
private noncomputable def ep000111010001_0 : Blocks := edgeBlocks% "full/vectors/000111010001-E-0000.bin"
private noncomputable def ep000111010001_1 : Blocks := edgeBlocks% "full/vectors/000111010001-E-0001.bin"
noncomputable def ep000111010001 : Blocks := (Blocks.join ep000111010001_0 ep000111010001_1)
private theorem idp000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101000.list =
    C ((2:ℤ)^158) * horner X vp000111010001.list + horner X ep000111010001.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111010001 : Branch 1 (-927761639/4000000 : ℚ) vp00011101000 := by
  apply branch_checked idp000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-927761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-929761639/2000000 : ℚ) by norm_num]
  exact coverp000111010001
theorem coverp00011101000 : Covers (-927761639/4000000 : ℚ) vp00011101000 := join_branches bp000111010000 bp000111010001
private noncomputable def vp0001110100_0 : Blocks := edgeBlocks% "full/vectors/0001110100-V-0000.bin"
private noncomputable def vp0001110100_1 : Blocks := edgeBlocks% "full/vectors/0001110100-V-0001.bin"
private noncomputable def vp0001110100_2 : Blocks := edgeBlocks% "full/vectors/0001110100-V-0002.bin"
noncomputable def vp0001110100 : Blocks := (Blocks.join vp0001110100_0 (Blocks.join vp0001110100_1 vp0001110100_2))
private theorem bp00011101000 : Branch 0 (-927761639/8000000 : ℚ) vp0001110100 := by
  apply branch_left_normalized (c:=vp00011101000) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-927761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-927761639/4000000 : ℚ) by norm_num]
  exact coverp00011101000
private noncomputable def ep00011101001_0 : Blocks := edgeBlocks% "full/vectors/00011101001-E-0000.bin"
private noncomputable def ep00011101001_1 : Blocks := edgeBlocks% "full/vectors/00011101001-E-0001.bin"
private noncomputable def ep00011101001_2 : Blocks := edgeBlocks% "full/vectors/00011101001-E-0002.bin"
noncomputable def ep00011101001 : Blocks := (Blocks.join ep00011101001_0 (Blocks.join ep00011101001_1 ep00011101001_2))
private theorem idp00011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110100.list =
    C ((2:ℤ)^298) * horner X vp00011101001.list + horner X ep00011101001.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101001 : Branch 1 (-927761639/8000000 : ℚ) vp0001110100 := by
  apply branch_checked idp00011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-927761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-931761639/4000000 : ℚ) by norm_num]
  exact coverp00011101001
theorem coverp0001110100 : Covers (-927761639/8000000 : ℚ) vp0001110100 := join_branches bp00011101000 bp00011101001
private noncomputable def vp000111010_0 : Blocks := edgeBlocks% "full/vectors/000111010-V-0000.bin"
private noncomputable def vp000111010_1 : Blocks := edgeBlocks% "full/vectors/000111010-V-0001.bin"
private noncomputable def vp000111010_2 : Blocks := edgeBlocks% "full/vectors/000111010-V-0002.bin"
private noncomputable def vp000111010_3 : Blocks := edgeBlocks% "full/vectors/000111010-V-0003.bin"
private noncomputable def vp000111010_4 : Blocks := edgeBlocks% "full/vectors/000111010-V-0004.bin"
noncomputable def vp000111010 : Blocks := (Blocks.join (Blocks.join vp000111010_0 vp000111010_1) (Blocks.join vp000111010_2 (Blocks.join vp000111010_3 vp000111010_4)))
private theorem bp0001110100 : Branch 0 (-927761639/16000000 : ℚ) vp000111010 := by
  apply branch_left_normalized (c:=vp0001110100) (k:=0) (m:=273) (by decide +kernel)
  rw [show 2*(-927761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-927761639/8000000 : ℚ) by norm_num]
  exact coverp0001110100
private noncomputable def ep0001110101_0 : Blocks := edgeBlocks% "full/vectors/0001110101-E-0000.bin"
private noncomputable def ep0001110101_1 : Blocks := edgeBlocks% "full/vectors/0001110101-E-0001.bin"
private noncomputable def ep0001110101_2 : Blocks := edgeBlocks% "full/vectors/0001110101-E-0002.bin"
private noncomputable def ep0001110101_3 : Blocks := edgeBlocks% "full/vectors/0001110101-E-0003.bin"
private noncomputable def ep0001110101_4 : Blocks := edgeBlocks% "full/vectors/0001110101-E-0004.bin"
noncomputable def ep0001110101 : Blocks := (Blocks.join (Blocks.join ep0001110101_0 ep0001110101_1) (Blocks.join ep0001110101_2 (Blocks.join ep0001110101_3 ep0001110101_4)))
private theorem idp0001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111010.list =
    C ((2:ℤ)^576) * horner X vp0001110101.list + horner X ep0001110101.list := by
  exact edge_identity (B := (2:ℤ)^893) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110101 : Branch 1 (-927761639/16000000 : ℚ) vp000111010 := by
  apply branch_checked idp0001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-927761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-935761639/8000000 : ℚ) by norm_num]
  exact coverp0001110101
theorem coverp000111010 : Covers (-927761639/16000000 : ℚ) vp000111010 := join_branches bp0001110100 bp0001110101
private noncomputable def vp00011101_0 : Blocks := edgeBlocks% "full/vectors/00011101-V-0000.bin"
private noncomputable def vp00011101_1 : Blocks := edgeBlocks% "full/vectors/00011101-V-0001.bin"
private noncomputable def vp00011101_2 : Blocks := edgeBlocks% "full/vectors/00011101-V-0002.bin"
private noncomputable def vp00011101_3 : Blocks := edgeBlocks% "full/vectors/00011101-V-0003.bin"
private noncomputable def vp00011101_4 : Blocks := edgeBlocks% "full/vectors/00011101-V-0004.bin"
private noncomputable def vp00011101_5 : Blocks := edgeBlocks% "full/vectors/00011101-V-0005.bin"
private noncomputable def vp00011101_6 : Blocks := edgeBlocks% "full/vectors/00011101-V-0006.bin"
private noncomputable def vp00011101_7 : Blocks := edgeBlocks% "full/vectors/00011101-V-0007.bin"
private noncomputable def vp00011101_8 : Blocks := edgeBlocks% "full/vectors/00011101-V-0008.bin"
noncomputable def vp00011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011101_0 vp00011101_1) (Blocks.join vp00011101_2 vp00011101_3)) (Blocks.join (Blocks.join vp00011101_4 vp00011101_5) (Blocks.join vp00011101_6 (Blocks.join vp00011101_7 vp00011101_8))))
private theorem bp000111010 : Branch 0 (-927761639/32000000 : ℚ) vp00011101 := by
  apply branch_left_normalized (c:=vp000111010) (k:=0) (m:=528) (by decide +kernel)
  rw [show 2*(-927761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-927761639/16000000 : ℚ) by norm_num]
  exact coverp000111010
private noncomputable def ep000111011_0 : Blocks := edgeBlocks% "full/vectors/000111011-E-0000.bin"
private noncomputable def ep000111011_1 : Blocks := edgeBlocks% "full/vectors/000111011-E-0001.bin"
private noncomputable def ep000111011_2 : Blocks := edgeBlocks% "full/vectors/000111011-E-0002.bin"
private noncomputable def ep000111011_3 : Blocks := edgeBlocks% "full/vectors/000111011-E-0003.bin"
private noncomputable def ep000111011_4 : Blocks := edgeBlocks% "full/vectors/000111011-E-0004.bin"
private noncomputable def ep000111011_5 : Blocks := edgeBlocks% "full/vectors/000111011-E-0005.bin"
private noncomputable def ep000111011_6 : Blocks := edgeBlocks% "full/vectors/000111011-E-0006.bin"
private noncomputable def ep000111011_7 : Blocks := edgeBlocks% "full/vectors/000111011-E-0007.bin"
private noncomputable def ep000111011_8 : Blocks := edgeBlocks% "full/vectors/000111011-E-0008.bin"
noncomputable def ep000111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000111011_0 ep000111011_1) (Blocks.join ep000111011_2 ep000111011_3)) (Blocks.join (Blocks.join ep000111011_4 ep000111011_5) (Blocks.join ep000111011_6 (Blocks.join ep000111011_7 ep000111011_8))))
private theorem idp000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011101.list =
    C ((2:ℤ)^1124) * horner X vp000111011.list + horner X ep000111011.list := by
  exact edge_identity (B := (2:ℤ)^1670) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111011 : Branch 1 (-927761639/32000000 : ℚ) vp00011101 := by
  apply branch_checked idp000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-927761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-943761639/16000000 : ℚ) by norm_num]
  exact coverp000111011
theorem coverp00011101 : Covers (-927761639/32000000 : ℚ) vp00011101 := join_branches bp000111010 bp000111011
private noncomputable def vp0001110011111_0 : Blocks := edgeBlocks% "full/vectors/0001110011111-V-0000.bin"
noncomputable def vp0001110011111 : Blocks := vp0001110011111_0
theorem coverp0001110011111 : Covers (-926761639/1000000 : ℚ) vp0001110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110011110_0 : Blocks := edgeBlocks% "full/vectors/0001110011110-V-0000.bin"
noncomputable def vp0001110011110 : Blocks := vp0001110011110_0
theorem coverp0001110011110 : Covers (-925761639/1000000 : ℚ) vp0001110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001111_0 : Blocks := edgeBlocks% "full/vectors/000111001111-V-0000.bin"
noncomputable def vp000111001111 : Blocks := vp000111001111_0
private theorem bp0001110011110 : Branch 0 (-925761639/2000000 : ℚ) vp000111001111 := by
  apply branch_left_normalized (c:=vp0001110011110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-925761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-925761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011110
private noncomputable def ep0001110011111_0 : Blocks := edgeBlocks% "full/vectors/0001110011111-E-0000.bin"
noncomputable def ep0001110011111 : Blocks := ep0001110011111_0
private theorem idp0001110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001111.list =
    C ((2:ℤ)^87) * horner X vp0001110011111.list + horner X ep0001110011111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110011111 : Branch 1 (-925761639/2000000 : ℚ) vp000111001111 := by
  apply branch_checked idp0001110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-925761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-926761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011111
theorem coverp000111001111 : Covers (-925761639/2000000 : ℚ) vp000111001111 := join_branches bp0001110011110 bp0001110011111
private noncomputable def vp0001110011101_0 : Blocks := edgeBlocks% "full/vectors/0001110011101-V-0000.bin"
noncomputable def vp0001110011101 : Blocks := vp0001110011101_0
theorem coverp0001110011101 : Covers (-924761639/1000000 : ℚ) vp0001110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110011100_0 : Blocks := edgeBlocks% "full/vectors/0001110011100-V-0000.bin"
noncomputable def vp0001110011100 : Blocks := vp0001110011100_0
theorem coverp0001110011100 : Covers (-923761639/1000000 : ℚ) vp0001110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001110_0 : Blocks := edgeBlocks% "full/vectors/000111001110-V-0000.bin"
noncomputable def vp000111001110 : Blocks := vp000111001110_0
private theorem bp0001110011100 : Branch 0 (-923761639/2000000 : ℚ) vp000111001110 := by
  apply branch_left_normalized (c:=vp0001110011100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-923761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-923761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011100
private noncomputable def ep0001110011101_0 : Blocks := edgeBlocks% "full/vectors/0001110011101-E-0000.bin"
noncomputable def ep0001110011101 : Blocks := ep0001110011101_0
private theorem idp0001110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001110.list =
    C ((2:ℤ)^87) * horner X vp0001110011101.list + horner X ep0001110011101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110011101 : Branch 1 (-923761639/2000000 : ℚ) vp000111001110 := by
  apply branch_checked idp0001110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-923761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-924761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011101
theorem coverp000111001110 : Covers (-923761639/2000000 : ℚ) vp000111001110 := join_branches bp0001110011100 bp0001110011101
private noncomputable def vp00011100111_0 : Blocks := edgeBlocks% "full/vectors/00011100111-V-0000.bin"
private noncomputable def vp00011100111_1 : Blocks := edgeBlocks% "full/vectors/00011100111-V-0001.bin"
noncomputable def vp00011100111 : Blocks := (Blocks.join vp00011100111_0 vp00011100111_1)
private theorem bp000111001110 : Branch 0 (-923761639/4000000 : ℚ) vp00011100111 := by
  apply branch_left_normalized (c:=vp000111001110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-923761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-923761639/2000000 : ℚ) by norm_num]
  exact coverp000111001110
private noncomputable def ep000111001111_0 : Blocks := edgeBlocks% "full/vectors/000111001111-E-0000.bin"
private noncomputable def ep000111001111_1 : Blocks := edgeBlocks% "full/vectors/000111001111-E-0001.bin"
noncomputable def ep000111001111 : Blocks := (Blocks.join ep000111001111_0 ep000111001111_1)
private theorem idp000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100111.list =
    C ((2:ℤ)^160) * horner X vp000111001111.list + horner X ep000111001111.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111001111 : Branch 1 (-923761639/4000000 : ℚ) vp00011100111 := by
  apply branch_checked idp000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-923761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-925761639/2000000 : ℚ) by norm_num]
  exact coverp000111001111
theorem coverp00011100111 : Covers (-923761639/4000000 : ℚ) vp00011100111 := join_branches bp000111001110 bp000111001111
private noncomputable def vp0001110011011_0 : Blocks := edgeBlocks% "full/vectors/0001110011011-V-0000.bin"
noncomputable def vp0001110011011 : Blocks := vp0001110011011_0
theorem coverp0001110011011 : Covers (-922761639/1000000 : ℚ) vp0001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110011010_0 : Blocks := edgeBlocks% "full/vectors/0001110011010-V-0000.bin"
noncomputable def vp0001110011010 : Blocks := vp0001110011010_0
theorem coverp0001110011010 : Covers (-921761639/1000000 : ℚ) vp0001110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001101_0 : Blocks := edgeBlocks% "full/vectors/000111001101-V-0000.bin"
noncomputable def vp000111001101 : Blocks := vp000111001101_0
private theorem bp0001110011010 : Branch 0 (-921761639/2000000 : ℚ) vp000111001101 := by
  apply branch_left_normalized (c:=vp0001110011010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-921761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-921761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011010
private noncomputable def ep0001110011011_0 : Blocks := edgeBlocks% "full/vectors/0001110011011-E-0000.bin"
noncomputable def ep0001110011011 : Blocks := ep0001110011011_0
private theorem idp0001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001101.list =
    C ((2:ℤ)^89) * horner X vp0001110011011.list + horner X ep0001110011011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110011011 : Branch 1 (-921761639/2000000 : ℚ) vp000111001101 := by
  apply branch_checked idp0001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-921761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-922761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011011
theorem coverp000111001101 : Covers (-921761639/2000000 : ℚ) vp000111001101 := join_branches bp0001110011010 bp0001110011011
private noncomputable def vp0001110011001_0 : Blocks := edgeBlocks% "full/vectors/0001110011001-V-0000.bin"
noncomputable def vp0001110011001 : Blocks := vp0001110011001_0
theorem coverp0001110011001 : Covers (-920761639/1000000 : ℚ) vp0001110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110011000_0 : Blocks := edgeBlocks% "full/vectors/0001110011000-V-0000.bin"
noncomputable def vp0001110011000 : Blocks := vp0001110011000_0
theorem coverp0001110011000 : Covers (-919761639/1000000 : ℚ) vp0001110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001100_0 : Blocks := edgeBlocks% "full/vectors/000111001100-V-0000.bin"
noncomputable def vp000111001100 : Blocks := vp000111001100_0
private theorem bp0001110011000 : Branch 0 (-919761639/2000000 : ℚ) vp000111001100 := by
  apply branch_left_normalized (c:=vp0001110011000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-919761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-919761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011000
private noncomputable def ep0001110011001_0 : Blocks := edgeBlocks% "full/vectors/0001110011001-E-0000.bin"
noncomputable def ep0001110011001 : Blocks := ep0001110011001_0
private theorem idp0001110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001100.list =
    C ((2:ℤ)^91) * horner X vp0001110011001.list + horner X ep0001110011001.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110011001 : Branch 1 (-919761639/2000000 : ℚ) vp000111001100 := by
  apply branch_checked idp0001110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-919761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-920761639/1000000 : ℚ) by norm_num]
  exact coverp0001110011001
theorem coverp000111001100 : Covers (-919761639/2000000 : ℚ) vp000111001100 := join_branches bp0001110011000 bp0001110011001
private noncomputable def vp00011100110_0 : Blocks := edgeBlocks% "full/vectors/00011100110-V-0000.bin"
private noncomputable def vp00011100110_1 : Blocks := edgeBlocks% "full/vectors/00011100110-V-0001.bin"
noncomputable def vp00011100110 : Blocks := (Blocks.join vp00011100110_0 vp00011100110_1)
private theorem bp000111001100 : Branch 0 (-919761639/4000000 : ℚ) vp00011100110 := by
  apply branch_left_normalized (c:=vp000111001100) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-919761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-919761639/2000000 : ℚ) by norm_num]
  exact coverp000111001100
private noncomputable def ep000111001101_0 : Blocks := edgeBlocks% "full/vectors/000111001101-E-0000.bin"
private noncomputable def ep000111001101_1 : Blocks := edgeBlocks% "full/vectors/000111001101-E-0001.bin"
noncomputable def ep000111001101 : Blocks := (Blocks.join ep000111001101_0 ep000111001101_1)
private theorem idp000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100110.list =
    C ((2:ℤ)^164) * horner X vp000111001101.list + horner X ep000111001101.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111001101 : Branch 1 (-919761639/4000000 : ℚ) vp00011100110 := by
  apply branch_checked idp000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-919761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-921761639/2000000 : ℚ) by norm_num]
  exact coverp000111001101
theorem coverp00011100110 : Covers (-919761639/4000000 : ℚ) vp00011100110 := join_branches bp000111001100 bp000111001101
private noncomputable def vp0001110011_0 : Blocks := edgeBlocks% "full/vectors/0001110011-V-0000.bin"
private noncomputable def vp0001110011_1 : Blocks := edgeBlocks% "full/vectors/0001110011-V-0001.bin"
private noncomputable def vp0001110011_2 : Blocks := edgeBlocks% "full/vectors/0001110011-V-0002.bin"
noncomputable def vp0001110011 : Blocks := (Blocks.join vp0001110011_0 (Blocks.join vp0001110011_1 vp0001110011_2))
private theorem bp00011100110 : Branch 0 (-919761639/8000000 : ℚ) vp0001110011 := by
  apply branch_left_normalized (c:=vp00011100110) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-919761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-919761639/4000000 : ℚ) by norm_num]
  exact coverp00011100110
private noncomputable def ep00011100111_0 : Blocks := edgeBlocks% "full/vectors/00011100111-E-0000.bin"
private noncomputable def ep00011100111_1 : Blocks := edgeBlocks% "full/vectors/00011100111-E-0001.bin"
private noncomputable def ep00011100111_2 : Blocks := edgeBlocks% "full/vectors/00011100111-E-0002.bin"
noncomputable def ep00011100111 : Blocks := (Blocks.join ep00011100111_0 (Blocks.join ep00011100111_1 ep00011100111_2))
private theorem idp00011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110011.list =
    C ((2:ℤ)^306) * horner X vp00011100111.list + horner X ep00011100111.list := by
  exact edge_identity (B := (2:ℤ)^513) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100111 : Branch 1 (-919761639/8000000 : ℚ) vp0001110011 := by
  apply branch_checked idp00011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-919761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-923761639/4000000 : ℚ) by norm_num]
  exact coverp00011100111
theorem coverp0001110011 : Covers (-919761639/8000000 : ℚ) vp0001110011 := join_branches bp00011100110 bp00011100111
private noncomputable def vp0001110010111_0 : Blocks := edgeBlocks% "full/vectors/0001110010111-V-0000.bin"
noncomputable def vp0001110010111 : Blocks := vp0001110010111_0
theorem coverp0001110010111 : Covers (-918761639/1000000 : ℚ) vp0001110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110010110_0 : Blocks := edgeBlocks% "full/vectors/0001110010110-V-0000.bin"
noncomputable def vp0001110010110 : Blocks := vp0001110010110_0
theorem coverp0001110010110 : Covers (-917761639/1000000 : ℚ) vp0001110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001011_0 : Blocks := edgeBlocks% "full/vectors/000111001011-V-0000.bin"
noncomputable def vp000111001011 : Blocks := vp000111001011_0
private theorem bp0001110010110 : Branch 0 (-917761639/2000000 : ℚ) vp000111001011 := by
  apply branch_left_normalized (c:=vp0001110010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-917761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-917761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010110
private noncomputable def ep0001110010111_0 : Blocks := edgeBlocks% "full/vectors/0001110010111-E-0000.bin"
noncomputable def ep0001110010111 : Blocks := ep0001110010111_0
private theorem idp0001110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001011.list =
    C ((2:ℤ)^94) * horner X vp0001110010111.list + horner X ep0001110010111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110010111 : Branch 1 (-917761639/2000000 : ℚ) vp000111001011 := by
  apply branch_checked idp0001110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-917761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-918761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010111
theorem coverp000111001011 : Covers (-917761639/2000000 : ℚ) vp000111001011 := join_branches bp0001110010110 bp0001110010111
private noncomputable def vp00011100101011_0 : Blocks := edgeBlocks% "full/vectors/00011100101011-V-0000.bin"
noncomputable def vp00011100101011 : Blocks := vp00011100101011_0
theorem coverp00011100101011 : Covers (-917261639/500000 : ℚ) vp00011100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100101010_0 : Blocks := edgeBlocks% "full/vectors/00011100101010-V-0000.bin"
noncomputable def vp00011100101010 : Blocks := vp00011100101010_0
theorem coverp00011100101010 : Covers (-916761639/500000 : ℚ) vp00011100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110010101_0 : Blocks := edgeBlocks% "full/vectors/0001110010101-V-0000.bin"
noncomputable def vp0001110010101 : Blocks := vp0001110010101_0
private theorem bp00011100101010 : Branch 0 (-916761639/1000000 : ℚ) vp0001110010101 := by
  apply branch_left_normalized (c:=vp00011100101010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-916761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-916761639/500000 : ℚ) by norm_num]
  exact coverp00011100101010
private noncomputable def ep00011100101011_0 : Blocks := edgeBlocks% "full/vectors/00011100101011-E-0000.bin"
noncomputable def ep00011100101011 : Blocks := ep00011100101011_0
private theorem idp00011100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110010101.list =
    C ((2:ℤ)^54) * horner X vp00011100101011.list + horner X ep00011100101011.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100101011 : Branch 1 (-916761639/1000000 : ℚ) vp0001110010101 := by
  apply branch_checked idp00011100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-916761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-917261639/500000 : ℚ) by norm_num]
  exact coverp00011100101011
theorem coverp0001110010101 : Covers (-916761639/1000000 : ℚ) vp0001110010101 := join_branches bp00011100101010 bp00011100101011
private noncomputable def vp0001110010100_0 : Blocks := edgeBlocks% "full/vectors/0001110010100-V-0000.bin"
noncomputable def vp0001110010100 : Blocks := vp0001110010100_0
theorem coverp0001110010100 : Covers (-915761639/1000000 : ℚ) vp0001110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001010_0 : Blocks := edgeBlocks% "full/vectors/000111001010-V-0000.bin"
noncomputable def vp000111001010 : Blocks := vp000111001010_0
private theorem bp0001110010100 : Branch 0 (-915761639/2000000 : ℚ) vp000111001010 := by
  apply branch_left_normalized (c:=vp0001110010100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-915761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-915761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010100
private noncomputable def ep0001110010101_0 : Blocks := edgeBlocks% "full/vectors/0001110010101-E-0000.bin"
noncomputable def ep0001110010101 : Blocks := ep0001110010101_0
private theorem idp0001110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001010.list =
    C ((2:ℤ)^90) * horner X vp0001110010101.list + horner X ep0001110010101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110010101 : Branch 1 (-915761639/2000000 : ℚ) vp000111001010 := by
  apply branch_checked idp0001110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-915761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-916761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010101
theorem coverp000111001010 : Covers (-915761639/2000000 : ℚ) vp000111001010 := join_branches bp0001110010100 bp0001110010101
private noncomputable def vp00011100101_0 : Blocks := edgeBlocks% "full/vectors/00011100101-V-0000.bin"
private noncomputable def vp00011100101_1 : Blocks := edgeBlocks% "full/vectors/00011100101-V-0001.bin"
noncomputable def vp00011100101 : Blocks := (Blocks.join vp00011100101_0 vp00011100101_1)
private theorem bp000111001010 : Branch 0 (-915761639/4000000 : ℚ) vp00011100101 := by
  apply branch_left_normalized (c:=vp000111001010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-915761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-915761639/2000000 : ℚ) by norm_num]
  exact coverp000111001010
private noncomputable def ep000111001011_0 : Blocks := edgeBlocks% "full/vectors/000111001011-E-0000.bin"
private noncomputable def ep000111001011_1 : Blocks := edgeBlocks% "full/vectors/000111001011-E-0001.bin"
noncomputable def ep000111001011 : Blocks := (Blocks.join ep000111001011_0 ep000111001011_1)
private theorem idp000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100101.list =
    C ((2:ℤ)^160) * horner X vp000111001011.list + horner X ep000111001011.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111001011 : Branch 1 (-915761639/4000000 : ℚ) vp00011100101 := by
  apply branch_checked idp000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-915761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-917761639/2000000 : ℚ) by norm_num]
  exact coverp000111001011
theorem coverp00011100101 : Covers (-915761639/4000000 : ℚ) vp00011100101 := join_branches bp000111001010 bp000111001011
private noncomputable def vp0001110010011_0 : Blocks := edgeBlocks% "full/vectors/0001110010011-V-0000.bin"
noncomputable def vp0001110010011 : Blocks := vp0001110010011_0
theorem coverp0001110010011 : Covers (-914761639/1000000 : ℚ) vp0001110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110010010_0 : Blocks := edgeBlocks% "full/vectors/0001110010010-V-0000.bin"
noncomputable def vp0001110010010 : Blocks := vp0001110010010_0
theorem coverp0001110010010 : Covers (-913761639/1000000 : ℚ) vp0001110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001001_0 : Blocks := edgeBlocks% "full/vectors/000111001001-V-0000.bin"
noncomputable def vp000111001001 : Blocks := vp000111001001_0
private theorem bp0001110010010 : Branch 0 (-913761639/2000000 : ℚ) vp000111001001 := by
  apply branch_left_normalized (c:=vp0001110010010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-913761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-913761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010010
private noncomputable def ep0001110010011_0 : Blocks := edgeBlocks% "full/vectors/0001110010011-E-0000.bin"
noncomputable def ep0001110010011 : Blocks := ep0001110010011_0
private theorem idp0001110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001001.list =
    C ((2:ℤ)^91) * horner X vp0001110010011.list + horner X ep0001110010011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110010011 : Branch 1 (-913761639/2000000 : ℚ) vp000111001001 := by
  apply branch_checked idp0001110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-913761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-914761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010011
theorem coverp000111001001 : Covers (-913761639/2000000 : ℚ) vp000111001001 := join_branches bp0001110010010 bp0001110010011
private noncomputable def vp0001110010001_0 : Blocks := edgeBlocks% "full/vectors/0001110010001-V-0000.bin"
noncomputable def vp0001110010001 : Blocks := vp0001110010001_0
theorem coverp0001110010001 : Covers (-912761639/1000000 : ℚ) vp0001110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110010000_0 : Blocks := edgeBlocks% "full/vectors/0001110010000-V-0000.bin"
noncomputable def vp0001110010000 : Blocks := vp0001110010000_0
theorem coverp0001110010000 : Covers (-911761639/1000000 : ℚ) vp0001110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111001000_0 : Blocks := edgeBlocks% "full/vectors/000111001000-V-0000.bin"
noncomputable def vp000111001000 : Blocks := vp000111001000_0
private theorem bp0001110010000 : Branch 0 (-911761639/2000000 : ℚ) vp000111001000 := by
  apply branch_left_normalized (c:=vp0001110010000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-911761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-911761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010000
private noncomputable def ep0001110010001_0 : Blocks := edgeBlocks% "full/vectors/0001110010001-E-0000.bin"
noncomputable def ep0001110010001 : Blocks := ep0001110010001_0
private theorem idp0001110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001000.list =
    C ((2:ℤ)^93) * horner X vp0001110010001.list + horner X ep0001110010001.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110010001 : Branch 1 (-911761639/2000000 : ℚ) vp000111001000 := by
  apply branch_checked idp0001110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-911761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-912761639/1000000 : ℚ) by norm_num]
  exact coverp0001110010001
theorem coverp000111001000 : Covers (-911761639/2000000 : ℚ) vp000111001000 := join_branches bp0001110010000 bp0001110010001
private noncomputable def vp00011100100_0 : Blocks := edgeBlocks% "full/vectors/00011100100-V-0000.bin"
private noncomputable def vp00011100100_1 : Blocks := edgeBlocks% "full/vectors/00011100100-V-0001.bin"
noncomputable def vp00011100100 : Blocks := (Blocks.join vp00011100100_0 vp00011100100_1)
private theorem bp000111001000 : Branch 0 (-911761639/4000000 : ℚ) vp00011100100 := by
  apply branch_left_normalized (c:=vp000111001000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-911761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-911761639/2000000 : ℚ) by norm_num]
  exact coverp000111001000
private noncomputable def ep000111001001_0 : Blocks := edgeBlocks% "full/vectors/000111001001-E-0000.bin"
private noncomputable def ep000111001001_1 : Blocks := edgeBlocks% "full/vectors/000111001001-E-0001.bin"
noncomputable def ep000111001001 : Blocks := (Blocks.join ep000111001001_0 ep000111001001_1)
private theorem idp000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100100.list =
    C ((2:ℤ)^165) * horner X vp000111001001.list + horner X ep000111001001.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111001001 : Branch 1 (-911761639/4000000 : ℚ) vp00011100100 := by
  apply branch_checked idp000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-911761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-913761639/2000000 : ℚ) by norm_num]
  exact coverp000111001001
theorem coverp00011100100 : Covers (-911761639/4000000 : ℚ) vp00011100100 := join_branches bp000111001000 bp000111001001
private noncomputable def vp0001110010_0 : Blocks := edgeBlocks% "full/vectors/0001110010-V-0000.bin"
private noncomputable def vp0001110010_1 : Blocks := edgeBlocks% "full/vectors/0001110010-V-0001.bin"
private noncomputable def vp0001110010_2 : Blocks := edgeBlocks% "full/vectors/0001110010-V-0002.bin"
noncomputable def vp0001110010 : Blocks := (Blocks.join vp0001110010_0 (Blocks.join vp0001110010_1 vp0001110010_2))
private theorem bp00011100100 : Branch 0 (-911761639/8000000 : ℚ) vp0001110010 := by
  apply branch_left_normalized (c:=vp00011100100) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-911761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-911761639/4000000 : ℚ) by norm_num]
  exact coverp00011100100
private noncomputable def ep00011100101_0 : Blocks := edgeBlocks% "full/vectors/00011100101-E-0000.bin"
private noncomputable def ep00011100101_1 : Blocks := edgeBlocks% "full/vectors/00011100101-E-0001.bin"
private noncomputable def ep00011100101_2 : Blocks := edgeBlocks% "full/vectors/00011100101-E-0002.bin"
noncomputable def ep00011100101 : Blocks := (Blocks.join ep00011100101_0 (Blocks.join ep00011100101_1 ep00011100101_2))
private theorem idp00011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110010.list =
    C ((2:ℤ)^306) * horner X vp00011100101.list + horner X ep00011100101.list := by
  exact edge_identity (B := (2:ℤ)^520) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100101 : Branch 1 (-911761639/8000000 : ℚ) vp0001110010 := by
  apply branch_checked idp00011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-911761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-915761639/4000000 : ℚ) by norm_num]
  exact coverp00011100101
theorem coverp0001110010 : Covers (-911761639/8000000 : ℚ) vp0001110010 := join_branches bp00011100100 bp00011100101
private noncomputable def vp000111001_0 : Blocks := edgeBlocks% "full/vectors/000111001-V-0000.bin"
private noncomputable def vp000111001_1 : Blocks := edgeBlocks% "full/vectors/000111001-V-0001.bin"
private noncomputable def vp000111001_2 : Blocks := edgeBlocks% "full/vectors/000111001-V-0002.bin"
private noncomputable def vp000111001_3 : Blocks := edgeBlocks% "full/vectors/000111001-V-0003.bin"
private noncomputable def vp000111001_4 : Blocks := edgeBlocks% "full/vectors/000111001-V-0004.bin"
noncomputable def vp000111001 : Blocks := (Blocks.join (Blocks.join vp000111001_0 vp000111001_1) (Blocks.join vp000111001_2 (Blocks.join vp000111001_3 vp000111001_4)))
private theorem bp0001110010 : Branch 0 (-911761639/16000000 : ℚ) vp000111001 := by
  apply branch_left_normalized (c:=vp0001110010) (k:=0) (m:=281) (by decide +kernel)
  rw [show 2*(-911761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-911761639/8000000 : ℚ) by norm_num]
  exact coverp0001110010
private noncomputable def ep0001110011_0 : Blocks := edgeBlocks% "full/vectors/0001110011-E-0000.bin"
private noncomputable def ep0001110011_1 : Blocks := edgeBlocks% "full/vectors/0001110011-E-0001.bin"
private noncomputable def ep0001110011_2 : Blocks := edgeBlocks% "full/vectors/0001110011-E-0002.bin"
private noncomputable def ep0001110011_3 : Blocks := edgeBlocks% "full/vectors/0001110011-E-0003.bin"
private noncomputable def ep0001110011_4 : Blocks := edgeBlocks% "full/vectors/0001110011-E-0004.bin"
noncomputable def ep0001110011 : Blocks := (Blocks.join (Blocks.join ep0001110011_0 ep0001110011_1) (Blocks.join ep0001110011_2 (Blocks.join ep0001110011_3 ep0001110011_4)))
private theorem idp0001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111001.list =
    C ((2:ℤ)^588) * horner X vp0001110011.list + horner X ep0001110011.list := by
  exact edge_identity (B := (2:ℤ)^914) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110011 : Branch 1 (-911761639/16000000 : ℚ) vp000111001 := by
  apply branch_checked idp0001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-911761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-919761639/8000000 : ℚ) by norm_num]
  exact coverp0001110011
theorem coverp000111001 : Covers (-911761639/16000000 : ℚ) vp000111001 := join_branches bp0001110010 bp0001110011
private noncomputable def vp0001110001111_0 : Blocks := edgeBlocks% "full/vectors/0001110001111-V-0000.bin"
noncomputable def vp0001110001111 : Blocks := vp0001110001111_0
theorem coverp0001110001111 : Covers (-910761639/1000000 : ℚ) vp0001110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110001110_0 : Blocks := edgeBlocks% "full/vectors/0001110001110-V-0000.bin"
noncomputable def vp0001110001110 : Blocks := vp0001110001110_0
theorem coverp0001110001110 : Covers (-909761639/1000000 : ℚ) vp0001110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111000111_0 : Blocks := edgeBlocks% "full/vectors/000111000111-V-0000.bin"
noncomputable def vp000111000111 : Blocks := vp000111000111_0
private theorem bp0001110001110 : Branch 0 (-909761639/2000000 : ℚ) vp000111000111 := by
  apply branch_left_normalized (c:=vp0001110001110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-909761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-909761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001110
private noncomputable def ep0001110001111_0 : Blocks := edgeBlocks% "full/vectors/0001110001111-E-0000.bin"
noncomputable def ep0001110001111 : Blocks := ep0001110001111_0
private theorem idp0001110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000111.list =
    C ((2:ℤ)^94) * horner X vp0001110001111.list + horner X ep0001110001111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110001111 : Branch 1 (-909761639/2000000 : ℚ) vp000111000111 := by
  apply branch_checked idp0001110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-909761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-910761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001111
theorem coverp000111000111 : Covers (-909761639/2000000 : ℚ) vp000111000111 := join_branches bp0001110001110 bp0001110001111
private noncomputable def vp0001110001101_0 : Blocks := edgeBlocks% "full/vectors/0001110001101-V-0000.bin"
noncomputable def vp0001110001101 : Blocks := vp0001110001101_0
theorem coverp0001110001101 : Covers (-908761639/1000000 : ℚ) vp0001110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100011001_0 : Blocks := edgeBlocks% "full/vectors/00011100011001-V-0000.bin"
noncomputable def vp00011100011001 : Blocks := vp00011100011001_0
theorem coverp00011100011001 : Covers (-908261639/500000 : ℚ) vp00011100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100011000_0 : Blocks := edgeBlocks% "full/vectors/00011100011000-V-0000.bin"
noncomputable def vp00011100011000 : Blocks := vp00011100011000_0
theorem coverp00011100011000 : Covers (-907761639/500000 : ℚ) vp00011100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110001100_0 : Blocks := edgeBlocks% "full/vectors/0001110001100-V-0000.bin"
noncomputable def vp0001110001100 : Blocks := vp0001110001100_0
private theorem bp00011100011000 : Branch 0 (-907761639/1000000 : ℚ) vp0001110001100 := by
  apply branch_left_normalized (c:=vp00011100011000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-907761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-907761639/500000 : ℚ) by norm_num]
  exact coverp00011100011000
private noncomputable def ep00011100011001_0 : Blocks := edgeBlocks% "full/vectors/00011100011001-E-0000.bin"
noncomputable def ep00011100011001 : Blocks := ep00011100011001_0
private theorem idp00011100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110001100.list =
    C ((2:ℤ)^56) * horner X vp00011100011001.list + horner X ep00011100011001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100011001 : Branch 1 (-907761639/1000000 : ℚ) vp0001110001100 := by
  apply branch_checked idp00011100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-907761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-908261639/500000 : ℚ) by norm_num]
  exact coverp00011100011001
theorem coverp0001110001100 : Covers (-907761639/1000000 : ℚ) vp0001110001100 := join_branches bp00011100011000 bp00011100011001
private noncomputable def vp000111000110_0 : Blocks := edgeBlocks% "full/vectors/000111000110-V-0000.bin"
noncomputable def vp000111000110 : Blocks := vp000111000110_0
private theorem bp0001110001100 : Branch 0 (-907761639/2000000 : ℚ) vp000111000110 := by
  apply branch_left_normalized (c:=vp0001110001100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-907761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-907761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001100
private noncomputable def ep0001110001101_0 : Blocks := edgeBlocks% "full/vectors/0001110001101-E-0000.bin"
noncomputable def ep0001110001101 : Blocks := ep0001110001101_0
private theorem idp0001110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000110.list =
    C ((2:ℤ)^92) * horner X vp0001110001101.list + horner X ep0001110001101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110001101 : Branch 1 (-907761639/2000000 : ℚ) vp000111000110 := by
  apply branch_checked idp0001110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-907761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-908761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001101
theorem coverp000111000110 : Covers (-907761639/2000000 : ℚ) vp000111000110 := join_branches bp0001110001100 bp0001110001101
private noncomputable def vp00011100011_0 : Blocks := edgeBlocks% "full/vectors/00011100011-V-0000.bin"
private noncomputable def vp00011100011_1 : Blocks := edgeBlocks% "full/vectors/00011100011-V-0001.bin"
noncomputable def vp00011100011 : Blocks := (Blocks.join vp00011100011_0 vp00011100011_1)
private theorem bp000111000110 : Branch 0 (-907761639/4000000 : ℚ) vp00011100011 := by
  apply branch_left_normalized (c:=vp000111000110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-907761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-907761639/2000000 : ℚ) by norm_num]
  exact coverp000111000110
private noncomputable def ep000111000111_0 : Blocks := edgeBlocks% "full/vectors/000111000111-E-0000.bin"
private noncomputable def ep000111000111_1 : Blocks := edgeBlocks% "full/vectors/000111000111-E-0001.bin"
noncomputable def ep000111000111 : Blocks := (Blocks.join ep000111000111_0 ep000111000111_1)
private theorem idp000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100011.list =
    C ((2:ℤ)^165) * horner X vp000111000111.list + horner X ep000111000111.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111000111 : Branch 1 (-907761639/4000000 : ℚ) vp00011100011 := by
  apply branch_checked idp000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-907761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-909761639/2000000 : ℚ) by norm_num]
  exact coverp000111000111
theorem coverp00011100011 : Covers (-907761639/4000000 : ℚ) vp00011100011 := join_branches bp000111000110 bp000111000111
private noncomputable def vp00011100010111_0 : Blocks := edgeBlocks% "full/vectors/00011100010111-V-0000.bin"
noncomputable def vp00011100010111 : Blocks := vp00011100010111_0
theorem coverp00011100010111 : Covers (-907261639/500000 : ℚ) vp00011100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100010110_0 : Blocks := edgeBlocks% "full/vectors/00011100010110-V-0000.bin"
noncomputable def vp00011100010110 : Blocks := vp00011100010110_0
theorem coverp00011100010110 : Covers (-906761639/500000 : ℚ) vp00011100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110001011_0 : Blocks := edgeBlocks% "full/vectors/0001110001011-V-0000.bin"
noncomputable def vp0001110001011 : Blocks := vp0001110001011_0
private theorem bp00011100010110 : Branch 0 (-906761639/1000000 : ℚ) vp0001110001011 := by
  apply branch_left_normalized (c:=vp00011100010110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-906761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-906761639/500000 : ℚ) by norm_num]
  exact coverp00011100010110
private noncomputable def ep00011100010111_0 : Blocks := edgeBlocks% "full/vectors/00011100010111-E-0000.bin"
noncomputable def ep00011100010111 : Blocks := ep00011100010111_0
private theorem idp00011100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110001011.list =
    C ((2:ℤ)^56) * horner X vp00011100010111.list + horner X ep00011100010111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100010111 : Branch 1 (-906761639/1000000 : ℚ) vp0001110001011 := by
  apply branch_checked idp00011100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-906761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-907261639/500000 : ℚ) by norm_num]
  exact coverp00011100010111
theorem coverp0001110001011 : Covers (-906761639/1000000 : ℚ) vp0001110001011 := join_branches bp00011100010110 bp00011100010111
private noncomputable def vp0001110001010_0 : Blocks := edgeBlocks% "full/vectors/0001110001010-V-0000.bin"
noncomputable def vp0001110001010 : Blocks := vp0001110001010_0
theorem coverp0001110001010 : Covers (-905761639/1000000 : ℚ) vp0001110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111000101_0 : Blocks := edgeBlocks% "full/vectors/000111000101-V-0000.bin"
noncomputable def vp000111000101 : Blocks := vp000111000101_0
private theorem bp0001110001010 : Branch 0 (-905761639/2000000 : ℚ) vp000111000101 := by
  apply branch_left_normalized (c:=vp0001110001010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-905761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-905761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001010
private noncomputable def ep0001110001011_0 : Blocks := edgeBlocks% "full/vectors/0001110001011-E-0000.bin"
noncomputable def ep0001110001011 : Blocks := ep0001110001011_0
private theorem idp0001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000101.list =
    C ((2:ℤ)^93) * horner X vp0001110001011.list + horner X ep0001110001011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110001011 : Branch 1 (-905761639/2000000 : ℚ) vp000111000101 := by
  apply branch_checked idp0001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-905761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-906761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001011
theorem coverp000111000101 : Covers (-905761639/2000000 : ℚ) vp000111000101 := join_branches bp0001110001010 bp0001110001011
private noncomputable def vp0001110001001_0 : Blocks := edgeBlocks% "full/vectors/0001110001001-V-0000.bin"
noncomputable def vp0001110001001 : Blocks := vp0001110001001_0
theorem coverp0001110001001 : Covers (-904761639/1000000 : ℚ) vp0001110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110001000_0 : Blocks := edgeBlocks% "full/vectors/0001110001000-V-0000.bin"
noncomputable def vp0001110001000 : Blocks := vp0001110001000_0
theorem coverp0001110001000 : Covers (-903761639/1000000 : ℚ) vp0001110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111000100_0 : Blocks := edgeBlocks% "full/vectors/000111000100-V-0000.bin"
noncomputable def vp000111000100 : Blocks := vp000111000100_0
private theorem bp0001110001000 : Branch 0 (-903761639/2000000 : ℚ) vp000111000100 := by
  apply branch_left_normalized (c:=vp0001110001000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-903761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-903761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001000
private noncomputable def ep0001110001001_0 : Blocks := edgeBlocks% "full/vectors/0001110001001-E-0000.bin"
noncomputable def ep0001110001001 : Blocks := ep0001110001001_0
private theorem idp0001110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000100.list =
    C ((2:ℤ)^93) * horner X vp0001110001001.list + horner X ep0001110001001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110001001 : Branch 1 (-903761639/2000000 : ℚ) vp000111000100 := by
  apply branch_checked idp0001110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-903761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-904761639/1000000 : ℚ) by norm_num]
  exact coverp0001110001001
theorem coverp000111000100 : Covers (-903761639/2000000 : ℚ) vp000111000100 := join_branches bp0001110001000 bp0001110001001
private noncomputable def vp00011100010_0 : Blocks := edgeBlocks% "full/vectors/00011100010-V-0000.bin"
private noncomputable def vp00011100010_1 : Blocks := edgeBlocks% "full/vectors/00011100010-V-0001.bin"
noncomputable def vp00011100010 : Blocks := (Blocks.join vp00011100010_0 vp00011100010_1)
private theorem bp000111000100 : Branch 0 (-903761639/4000000 : ℚ) vp00011100010 := by
  apply branch_left_normalized (c:=vp000111000100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-903761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-903761639/2000000 : ℚ) by norm_num]
  exact coverp000111000100
private noncomputable def ep000111000101_0 : Blocks := edgeBlocks% "full/vectors/000111000101-E-0000.bin"
private noncomputable def ep000111000101_1 : Blocks := edgeBlocks% "full/vectors/000111000101-E-0001.bin"
noncomputable def ep000111000101 : Blocks := (Blocks.join ep000111000101_0 ep000111000101_1)
private theorem idp000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100010.list =
    C ((2:ℤ)^164) * horner X vp000111000101.list + horner X ep000111000101.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111000101 : Branch 1 (-903761639/4000000 : ℚ) vp00011100010 := by
  apply branch_checked idp000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-903761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-905761639/2000000 : ℚ) by norm_num]
  exact coverp000111000101
theorem coverp00011100010 : Covers (-903761639/4000000 : ℚ) vp00011100010 := join_branches bp000111000100 bp000111000101
private noncomputable def vp0001110001_0 : Blocks := edgeBlocks% "full/vectors/0001110001-V-0000.bin"
private noncomputable def vp0001110001_1 : Blocks := edgeBlocks% "full/vectors/0001110001-V-0001.bin"
private noncomputable def vp0001110001_2 : Blocks := edgeBlocks% "full/vectors/0001110001-V-0002.bin"
noncomputable def vp0001110001 : Blocks := (Blocks.join vp0001110001_0 (Blocks.join vp0001110001_1 vp0001110001_2))
private theorem bp00011100010 : Branch 0 (-903761639/8000000 : ℚ) vp0001110001 := by
  apply branch_left_normalized (c:=vp00011100010) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-903761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-903761639/4000000 : ℚ) by norm_num]
  exact coverp00011100010
private noncomputable def ep00011100011_0 : Blocks := edgeBlocks% "full/vectors/00011100011-E-0000.bin"
private noncomputable def ep00011100011_1 : Blocks := edgeBlocks% "full/vectors/00011100011-E-0001.bin"
private noncomputable def ep00011100011_2 : Blocks := edgeBlocks% "full/vectors/00011100011-E-0002.bin"
noncomputable def ep00011100011 : Blocks := (Blocks.join ep00011100011_0 (Blocks.join ep00011100011_1 ep00011100011_2))
private theorem idp00011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110001.list =
    C ((2:ℤ)^305) * horner X vp00011100011.list + horner X ep00011100011.list := by
  exact edge_identity (B := (2:ℤ)^522) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100011 : Branch 1 (-903761639/8000000 : ℚ) vp0001110001 := by
  apply branch_checked idp00011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-903761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-907761639/4000000 : ℚ) by norm_num]
  exact coverp00011100011
theorem coverp0001110001 : Covers (-903761639/8000000 : ℚ) vp0001110001 := join_branches bp00011100010 bp00011100011
private noncomputable def vp0001110000111_0 : Blocks := edgeBlocks% "full/vectors/0001110000111-V-0000.bin"
noncomputable def vp0001110000111 : Blocks := vp0001110000111_0
theorem coverp0001110000111 : Covers (-902761639/1000000 : ℚ) vp0001110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000110_0 : Blocks := edgeBlocks% "full/vectors/0001110000110-V-0000.bin"
noncomputable def vp0001110000110 : Blocks := vp0001110000110_0
theorem coverp0001110000110 : Covers (-901761639/1000000 : ℚ) vp0001110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111000011_0 : Blocks := edgeBlocks% "full/vectors/000111000011-V-0000.bin"
noncomputable def vp000111000011 : Blocks := vp000111000011_0
private theorem bp0001110000110 : Branch 0 (-901761639/2000000 : ℚ) vp000111000011 := by
  apply branch_left_normalized (c:=vp0001110000110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-901761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-901761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000110
private noncomputable def ep0001110000111_0 : Blocks := edgeBlocks% "full/vectors/0001110000111-E-0000.bin"
noncomputable def ep0001110000111 : Blocks := ep0001110000111_0
private theorem idp0001110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000011.list =
    C ((2:ℤ)^94) * horner X vp0001110000111.list + horner X ep0001110000111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110000111 : Branch 1 (-901761639/2000000 : ℚ) vp000111000011 := by
  apply branch_checked idp0001110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-901761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-902761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000111
theorem coverp000111000011 : Covers (-901761639/2000000 : ℚ) vp000111000011 := join_branches bp0001110000110 bp0001110000111
private noncomputable def vp00011100001011_0 : Blocks := edgeBlocks% "full/vectors/00011100001011-V-0000.bin"
noncomputable def vp00011100001011 : Blocks := vp00011100001011_0
theorem coverp00011100001011 : Covers (-901261639/500000 : ℚ) vp00011100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100001010_0 : Blocks := edgeBlocks% "full/vectors/00011100001010-V-0000.bin"
noncomputable def vp00011100001010 : Blocks := vp00011100001010_0
theorem coverp00011100001010 : Covers (-900761639/500000 : ℚ) vp00011100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000101_0 : Blocks := edgeBlocks% "full/vectors/0001110000101-V-0000.bin"
noncomputable def vp0001110000101 : Blocks := vp0001110000101_0
private theorem bp00011100001010 : Branch 0 (-900761639/1000000 : ℚ) vp0001110000101 := by
  apply branch_left_normalized (c:=vp00011100001010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-900761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-900761639/500000 : ℚ) by norm_num]
  exact coverp00011100001010
private noncomputable def ep00011100001011_0 : Blocks := edgeBlocks% "full/vectors/00011100001011-E-0000.bin"
noncomputable def ep00011100001011 : Blocks := ep00011100001011_0
private theorem idp00011100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000101.list =
    C ((2:ℤ)^55) * horner X vp00011100001011.list + horner X ep00011100001011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100001011 : Branch 1 (-900761639/1000000 : ℚ) vp0001110000101 := by
  apply branch_checked idp00011100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-900761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-901261639/500000 : ℚ) by norm_num]
  exact coverp00011100001011
theorem coverp0001110000101 : Covers (-900761639/1000000 : ℚ) vp0001110000101 := join_branches bp00011100001010 bp00011100001011
private noncomputable def vp00011100001001_0 : Blocks := edgeBlocks% "full/vectors/00011100001001-V-0000.bin"
noncomputable def vp00011100001001 : Blocks := vp00011100001001_0
theorem coverp00011100001001 : Covers (-900261639/500000 : ℚ) vp00011100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100001000_0 : Blocks := edgeBlocks% "full/vectors/00011100001000-V-0000.bin"
noncomputable def vp00011100001000 : Blocks := vp00011100001000_0
theorem coverp00011100001000 : Covers (-899761639/500000 : ℚ) vp00011100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000100_0 : Blocks := edgeBlocks% "full/vectors/0001110000100-V-0000.bin"
noncomputable def vp0001110000100 : Blocks := vp0001110000100_0
private theorem bp00011100001000 : Branch 0 (-899761639/1000000 : ℚ) vp0001110000100 := by
  apply branch_left_normalized (c:=vp00011100001000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-899761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-899761639/500000 : ℚ) by norm_num]
  exact coverp00011100001000
private noncomputable def ep00011100001001_0 : Blocks := edgeBlocks% "full/vectors/00011100001001-E-0000.bin"
noncomputable def ep00011100001001 : Blocks := ep00011100001001_0
private theorem idp00011100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000100.list =
    C ((2:ℤ)^55) * horner X vp00011100001001.list + horner X ep00011100001001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100001001 : Branch 1 (-899761639/1000000 : ℚ) vp0001110000100 := by
  apply branch_checked idp00011100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-899761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-900261639/500000 : ℚ) by norm_num]
  exact coverp00011100001001
theorem coverp0001110000100 : Covers (-899761639/1000000 : ℚ) vp0001110000100 := join_branches bp00011100001000 bp00011100001001
private noncomputable def vp000111000010_0 : Blocks := edgeBlocks% "full/vectors/000111000010-V-0000.bin"
noncomputable def vp000111000010 : Blocks := vp000111000010_0
private theorem bp0001110000100 : Branch 0 (-899761639/2000000 : ℚ) vp000111000010 := by
  apply branch_left_normalized (c:=vp0001110000100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-899761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-899761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000100
private noncomputable def ep0001110000101_0 : Blocks := edgeBlocks% "full/vectors/0001110000101-E-0000.bin"
noncomputable def ep0001110000101 : Blocks := ep0001110000101_0
private theorem idp0001110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000010.list =
    C ((2:ℤ)^92) * horner X vp0001110000101.list + horner X ep0001110000101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110000101 : Branch 1 (-899761639/2000000 : ℚ) vp000111000010 := by
  apply branch_checked idp0001110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-899761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-900761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000101
theorem coverp000111000010 : Covers (-899761639/2000000 : ℚ) vp000111000010 := join_branches bp0001110000100 bp0001110000101
private noncomputable def vp00011100001_0 : Blocks := edgeBlocks% "full/vectors/00011100001-V-0000.bin"
private noncomputable def vp00011100001_1 : Blocks := edgeBlocks% "full/vectors/00011100001-V-0001.bin"
noncomputable def vp00011100001 : Blocks := (Blocks.join vp00011100001_0 vp00011100001_1)
private theorem bp000111000010 : Branch 0 (-899761639/4000000 : ℚ) vp00011100001 := by
  apply branch_left_normalized (c:=vp000111000010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-899761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-899761639/2000000 : ℚ) by norm_num]
  exact coverp000111000010
private noncomputable def ep000111000011_0 : Blocks := edgeBlocks% "full/vectors/000111000011-E-0000.bin"
private noncomputable def ep000111000011_1 : Blocks := edgeBlocks% "full/vectors/000111000011-E-0001.bin"
noncomputable def ep000111000011 : Blocks := (Blocks.join ep000111000011_0 ep000111000011_1)
private theorem idp000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100001.list =
    C ((2:ℤ)^165) * horner X vp000111000011.list + horner X ep000111000011.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111000011 : Branch 1 (-899761639/4000000 : ℚ) vp00011100001 := by
  apply branch_checked idp000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-899761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-901761639/2000000 : ℚ) by norm_num]
  exact coverp000111000011
theorem coverp00011100001 : Covers (-899761639/4000000 : ℚ) vp00011100001 := join_branches bp000111000010 bp000111000011
private noncomputable def vp00011100000111_0 : Blocks := edgeBlocks% "full/vectors/00011100000111-V-0000.bin"
noncomputable def vp00011100000111 : Blocks := vp00011100000111_0
theorem coverp00011100000111 : Covers (-899261639/500000 : ℚ) vp00011100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100000110_0 : Blocks := edgeBlocks% "full/vectors/00011100000110-V-0000.bin"
noncomputable def vp00011100000110 : Blocks := vp00011100000110_0
theorem coverp00011100000110 : Covers (-898761639/500000 : ℚ) vp00011100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000011_0 : Blocks := edgeBlocks% "full/vectors/0001110000011-V-0000.bin"
noncomputable def vp0001110000011 : Blocks := vp0001110000011_0
private theorem bp00011100000110 : Branch 0 (-898761639/1000000 : ℚ) vp0001110000011 := by
  apply branch_left_normalized (c:=vp00011100000110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-898761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-898761639/500000 : ℚ) by norm_num]
  exact coverp00011100000110
private noncomputable def ep00011100000111_0 : Blocks := edgeBlocks% "full/vectors/00011100000111-E-0000.bin"
noncomputable def ep00011100000111 : Blocks := ep00011100000111_0
private theorem idp00011100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000011.list =
    C ((2:ℤ)^56) * horner X vp00011100000111.list + horner X ep00011100000111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100000111 : Branch 1 (-898761639/1000000 : ℚ) vp0001110000011 := by
  apply branch_checked idp00011100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-898761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-899261639/500000 : ℚ) by norm_num]
  exact coverp00011100000111
theorem coverp0001110000011 : Covers (-898761639/1000000 : ℚ) vp0001110000011 := join_branches bp00011100000110 bp00011100000111
private noncomputable def vp00011100000101_0 : Blocks := edgeBlocks% "full/vectors/00011100000101-V-0000.bin"
noncomputable def vp00011100000101 : Blocks := vp00011100000101_0
theorem coverp00011100000101 : Covers (-898261639/500000 : ℚ) vp00011100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100000100_0 : Blocks := edgeBlocks% "full/vectors/00011100000100-V-0000.bin"
noncomputable def vp00011100000100 : Blocks := vp00011100000100_0
theorem coverp00011100000100 : Covers (-897761639/500000 : ℚ) vp00011100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000010_0 : Blocks := edgeBlocks% "full/vectors/0001110000010-V-0000.bin"
noncomputable def vp0001110000010 : Blocks := vp0001110000010_0
private theorem bp00011100000100 : Branch 0 (-897761639/1000000 : ℚ) vp0001110000010 := by
  apply branch_left_normalized (c:=vp00011100000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-897761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-897761639/500000 : ℚ) by norm_num]
  exact coverp00011100000100
private noncomputable def ep00011100000101_0 : Blocks := edgeBlocks% "full/vectors/00011100000101-E-0000.bin"
noncomputable def ep00011100000101 : Blocks := ep00011100000101_0
private theorem idp00011100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000010.list =
    C ((2:ℤ)^56) * horner X vp00011100000101.list + horner X ep00011100000101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100000101 : Branch 1 (-897761639/1000000 : ℚ) vp0001110000010 := by
  apply branch_checked idp00011100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-897761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-898261639/500000 : ℚ) by norm_num]
  exact coverp00011100000101
theorem coverp0001110000010 : Covers (-897761639/1000000 : ℚ) vp0001110000010 := join_branches bp00011100000100 bp00011100000101
private noncomputable def vp000111000001_0 : Blocks := edgeBlocks% "full/vectors/000111000001-V-0000.bin"
noncomputable def vp000111000001 : Blocks := vp000111000001_0
private theorem bp0001110000010 : Branch 0 (-897761639/2000000 : ℚ) vp000111000001 := by
  apply branch_left_normalized (c:=vp0001110000010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-897761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-897761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000010
private noncomputable def ep0001110000011_0 : Blocks := edgeBlocks% "full/vectors/0001110000011-E-0000.bin"
noncomputable def ep0001110000011 : Blocks := ep0001110000011_0
private theorem idp0001110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000001.list =
    C ((2:ℤ)^93) * horner X vp0001110000011.list + horner X ep0001110000011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110000011 : Branch 1 (-897761639/2000000 : ℚ) vp000111000001 := by
  apply branch_checked idp0001110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-897761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-898761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000011
theorem coverp000111000001 : Covers (-897761639/2000000 : ℚ) vp000111000001 := join_branches bp0001110000010 bp0001110000011
private noncomputable def vp00011100000011_0 : Blocks := edgeBlocks% "full/vectors/00011100000011-V-0000.bin"
noncomputable def vp00011100000011 : Blocks := vp00011100000011_0
theorem coverp00011100000011 : Covers (-897261639/500000 : ℚ) vp00011100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100000010_0 : Blocks := edgeBlocks% "full/vectors/00011100000010-V-0000.bin"
noncomputable def vp00011100000010 : Blocks := vp00011100000010_0
theorem coverp00011100000010 : Covers (-896761639/500000 : ℚ) vp00011100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000001_0 : Blocks := edgeBlocks% "full/vectors/0001110000001-V-0000.bin"
noncomputable def vp0001110000001 : Blocks := vp0001110000001_0
private theorem bp00011100000010 : Branch 0 (-896761639/1000000 : ℚ) vp0001110000001 := by
  apply branch_left_normalized (c:=vp00011100000010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-896761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-896761639/500000 : ℚ) by norm_num]
  exact coverp00011100000010
private noncomputable def ep00011100000011_0 : Blocks := edgeBlocks% "full/vectors/00011100000011-E-0000.bin"
noncomputable def ep00011100000011 : Blocks := ep00011100000011_0
private theorem idp00011100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000001.list =
    C ((2:ℤ)^55) * horner X vp00011100000011.list + horner X ep00011100000011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100000011 : Branch 1 (-896761639/1000000 : ℚ) vp0001110000001 := by
  apply branch_checked idp00011100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-896761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-897261639/500000 : ℚ) by norm_num]
  exact coverp00011100000011
theorem coverp0001110000001 : Covers (-896761639/1000000 : ℚ) vp0001110000001 := join_branches bp00011100000010 bp00011100000011
private noncomputable def vp00011100000001_0 : Blocks := edgeBlocks% "full/vectors/00011100000001-V-0000.bin"
noncomputable def vp00011100000001 : Blocks := vp00011100000001_0
theorem coverp00011100000001 : Covers (-896261639/500000 : ℚ) vp00011100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011100000000_0 : Blocks := edgeBlocks% "full/vectors/00011100000000-V-0000.bin"
noncomputable def vp00011100000000 : Blocks := vp00011100000000_0
theorem coverp00011100000000 : Covers (-895761639/500000 : ℚ) vp00011100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001110000000_0 : Blocks := edgeBlocks% "full/vectors/0001110000000-V-0000.bin"
noncomputable def vp0001110000000 : Blocks := vp0001110000000_0
private theorem bp00011100000000 : Branch 0 (-895761639/1000000 : ℚ) vp0001110000000 := by
  apply branch_left_normalized (c:=vp00011100000000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-895761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/500000 : ℚ) by norm_num]
  exact coverp00011100000000
private noncomputable def ep00011100000001_0 : Blocks := edgeBlocks% "full/vectors/00011100000001-E-0000.bin"
noncomputable def ep00011100000001 : Blocks := ep00011100000001_0
private theorem idp00011100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000000.list =
    C ((2:ℤ)^56) * horner X vp00011100000001.list + horner X ep00011100000001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100000001 : Branch 1 (-895761639/1000000 : ℚ) vp0001110000000 := by
  apply branch_checked idp00011100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-896261639/500000 : ℚ) by norm_num]
  exact coverp00011100000001
theorem coverp0001110000000 : Covers (-895761639/1000000 : ℚ) vp0001110000000 := join_branches bp00011100000000 bp00011100000001
private noncomputable def vp000111000000_0 : Blocks := edgeBlocks% "full/vectors/000111000000-V-0000.bin"
noncomputable def vp000111000000 : Blocks := vp000111000000_0
private theorem bp0001110000000 : Branch 0 (-895761639/2000000 : ℚ) vp000111000000 := by
  apply branch_left_normalized (c:=vp0001110000000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-895761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000000
private noncomputable def ep0001110000001_0 : Blocks := edgeBlocks% "full/vectors/0001110000001-E-0000.bin"
noncomputable def ep0001110000001 : Blocks := ep0001110000001_0
private theorem idp0001110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000000.list =
    C ((2:ℤ)^94) * horner X vp0001110000001.list + horner X ep0001110000001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110000001 : Branch 1 (-895761639/2000000 : ℚ) vp000111000000 := by
  apply branch_checked idp0001110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-896761639/1000000 : ℚ) by norm_num]
  exact coverp0001110000001
theorem coverp000111000000 : Covers (-895761639/2000000 : ℚ) vp000111000000 := join_branches bp0001110000000 bp0001110000001
private noncomputable def vp00011100000_0 : Blocks := edgeBlocks% "full/vectors/00011100000-V-0000.bin"
private noncomputable def vp00011100000_1 : Blocks := edgeBlocks% "full/vectors/00011100000-V-0001.bin"
noncomputable def vp00011100000 : Blocks := (Blocks.join vp00011100000_0 vp00011100000_1)
private theorem bp000111000000 : Branch 0 (-895761639/4000000 : ℚ) vp00011100000 := by
  apply branch_left_normalized (c:=vp000111000000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-895761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/2000000 : ℚ) by norm_num]
  exact coverp000111000000
private noncomputable def ep000111000001_0 : Blocks := edgeBlocks% "full/vectors/000111000001-E-0000.bin"
private noncomputable def ep000111000001_1 : Blocks := edgeBlocks% "full/vectors/000111000001-E-0001.bin"
noncomputable def ep000111000001 : Blocks := (Blocks.join ep000111000001_0 ep000111000001_1)
private theorem idp000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100000.list =
    C ((2:ℤ)^165) * horner X vp000111000001.list + horner X ep000111000001.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111000001 : Branch 1 (-895761639/4000000 : ℚ) vp00011100000 := by
  apply branch_checked idp000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-897761639/2000000 : ℚ) by norm_num]
  exact coverp000111000001
theorem coverp00011100000 : Covers (-895761639/4000000 : ℚ) vp00011100000 := join_branches bp000111000000 bp000111000001
private noncomputable def vp0001110000_0 : Blocks := edgeBlocks% "full/vectors/0001110000-V-0000.bin"
private noncomputable def vp0001110000_1 : Blocks := edgeBlocks% "full/vectors/0001110000-V-0001.bin"
private noncomputable def vp0001110000_2 : Blocks := edgeBlocks% "full/vectors/0001110000-V-0002.bin"
noncomputable def vp0001110000 : Blocks := (Blocks.join vp0001110000_0 (Blocks.join vp0001110000_1 vp0001110000_2))
private theorem bp00011100000 : Branch 0 (-895761639/8000000 : ℚ) vp0001110000 := by
  apply branch_left_normalized (c:=vp00011100000) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-895761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/4000000 : ℚ) by norm_num]
  exact coverp00011100000
private noncomputable def ep00011100001_0 : Blocks := edgeBlocks% "full/vectors/00011100001-E-0000.bin"
private noncomputable def ep00011100001_1 : Blocks := edgeBlocks% "full/vectors/00011100001-E-0001.bin"
private noncomputable def ep00011100001_2 : Blocks := edgeBlocks% "full/vectors/00011100001-E-0002.bin"
noncomputable def ep00011100001 : Blocks := (Blocks.join ep00011100001_0 (Blocks.join ep00011100001_1 ep00011100001_2))
private theorem idp00011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110000.list =
    C ((2:ℤ)^308) * horner X vp00011100001.list + horner X ep00011100001.list := by
  exact edge_identity (B := (2:ℤ)^526) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011100001 : Branch 1 (-895761639/8000000 : ℚ) vp0001110000 := by
  apply branch_checked idp00011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-899761639/4000000 : ℚ) by norm_num]
  exact coverp00011100001
theorem coverp0001110000 : Covers (-895761639/8000000 : ℚ) vp0001110000 := join_branches bp00011100000 bp00011100001
private noncomputable def vp000111000_0 : Blocks := edgeBlocks% "full/vectors/000111000-V-0000.bin"
private noncomputable def vp000111000_1 : Blocks := edgeBlocks% "full/vectors/000111000-V-0001.bin"
private noncomputable def vp000111000_2 : Blocks := edgeBlocks% "full/vectors/000111000-V-0002.bin"
private noncomputable def vp000111000_3 : Blocks := edgeBlocks% "full/vectors/000111000-V-0003.bin"
private noncomputable def vp000111000_4 : Blocks := edgeBlocks% "full/vectors/000111000-V-0004.bin"
noncomputable def vp000111000 : Blocks := (Blocks.join (Blocks.join vp000111000_0 vp000111000_1) (Blocks.join vp000111000_2 (Blocks.join vp000111000_3 vp000111000_4)))
private theorem bp0001110000 : Branch 0 (-895761639/16000000 : ℚ) vp000111000 := by
  apply branch_left_normalized (c:=vp0001110000) (k:=0) (m:=284) (by decide +kernel)
  rw [show 2*(-895761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/8000000 : ℚ) by norm_num]
  exact coverp0001110000
private noncomputable def ep0001110001_0 : Blocks := edgeBlocks% "full/vectors/0001110001-E-0000.bin"
private noncomputable def ep0001110001_1 : Blocks := edgeBlocks% "full/vectors/0001110001-E-0001.bin"
private noncomputable def ep0001110001_2 : Blocks := edgeBlocks% "full/vectors/0001110001-E-0002.bin"
private noncomputable def ep0001110001_3 : Blocks := edgeBlocks% "full/vectors/0001110001-E-0003.bin"
private noncomputable def ep0001110001_4 : Blocks := edgeBlocks% "full/vectors/0001110001-E-0004.bin"
noncomputable def ep0001110001 : Blocks := (Blocks.join (Blocks.join ep0001110001_0 ep0001110001_1) (Blocks.join ep0001110001_2 (Blocks.join ep0001110001_3 ep0001110001_4)))
private theorem idp0001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111000.list =
    C ((2:ℤ)^592) * horner X vp0001110001.list + horner X ep0001110001.list := by
  exact edge_identity (B := (2:ℤ)^924) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001110001 : Branch 1 (-895761639/16000000 : ℚ) vp000111000 := by
  apply branch_checked idp0001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-903761639/8000000 : ℚ) by norm_num]
  exact coverp0001110001
theorem coverp000111000 : Covers (-895761639/16000000 : ℚ) vp000111000 := join_branches bp0001110000 bp0001110001
private noncomputable def vp00011100_0 : Blocks := edgeBlocks% "full/vectors/00011100-V-0000.bin"
private noncomputable def vp00011100_1 : Blocks := edgeBlocks% "full/vectors/00011100-V-0001.bin"
private noncomputable def vp00011100_2 : Blocks := edgeBlocks% "full/vectors/00011100-V-0002.bin"
private noncomputable def vp00011100_3 : Blocks := edgeBlocks% "full/vectors/00011100-V-0003.bin"
private noncomputable def vp00011100_4 : Blocks := edgeBlocks% "full/vectors/00011100-V-0004.bin"
private noncomputable def vp00011100_5 : Blocks := edgeBlocks% "full/vectors/00011100-V-0005.bin"
private noncomputable def vp00011100_6 : Blocks := edgeBlocks% "full/vectors/00011100-V-0006.bin"
private noncomputable def vp00011100_7 : Blocks := edgeBlocks% "full/vectors/00011100-V-0007.bin"
private noncomputable def vp00011100_8 : Blocks := edgeBlocks% "full/vectors/00011100-V-0008.bin"
noncomputable def vp00011100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011100_0 vp00011100_1) (Blocks.join vp00011100_2 vp00011100_3)) (Blocks.join (Blocks.join vp00011100_4 vp00011100_5) (Blocks.join vp00011100_6 (Blocks.join vp00011100_7 vp00011100_8))))
private theorem bp000111000 : Branch 0 (-895761639/32000000 : ℚ) vp00011100 := by
  apply branch_left_normalized (c:=vp000111000) (k:=0) (m:=544) (by decide +kernel)
  rw [show 2*(-895761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/16000000 : ℚ) by norm_num]
  exact coverp000111000
private noncomputable def ep000111001_0 : Blocks := edgeBlocks% "full/vectors/000111001-E-0000.bin"
private noncomputable def ep000111001_1 : Blocks := edgeBlocks% "full/vectors/000111001-E-0001.bin"
private noncomputable def ep000111001_2 : Blocks := edgeBlocks% "full/vectors/000111001-E-0002.bin"
private noncomputable def ep000111001_3 : Blocks := edgeBlocks% "full/vectors/000111001-E-0003.bin"
private noncomputable def ep000111001_4 : Blocks := edgeBlocks% "full/vectors/000111001-E-0004.bin"
private noncomputable def ep000111001_5 : Blocks := edgeBlocks% "full/vectors/000111001-E-0005.bin"
private noncomputable def ep000111001_6 : Blocks := edgeBlocks% "full/vectors/000111001-E-0006.bin"
private noncomputable def ep000111001_7 : Blocks := edgeBlocks% "full/vectors/000111001-E-0007.bin"
private noncomputable def ep000111001_8 : Blocks := edgeBlocks% "full/vectors/000111001-E-0008.bin"
noncomputable def ep000111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000111001_0 ep000111001_1) (Blocks.join ep000111001_2 ep000111001_3)) (Blocks.join (Blocks.join ep000111001_4 ep000111001_5) (Blocks.join ep000111001_6 (Blocks.join ep000111001_7 ep000111001_8))))
private theorem idp000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011100.list =
    C ((2:ℤ)^1152) * horner X vp000111001.list + horner X ep000111001.list := by
  exact edge_identity (B := (2:ℤ)^1714) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111001 : Branch 1 (-895761639/32000000 : ℚ) vp00011100 := by
  apply branch_checked idp000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-911761639/16000000 : ℚ) by norm_num]
  exact coverp000111001
theorem coverp00011100 : Covers (-895761639/32000000 : ℚ) vp00011100 := join_branches bp000111000 bp000111001
private noncomputable def vp0001110_0 : Blocks := edgeBlocks% "full/vectors/0001110-V-0000.bin"
private noncomputable def vp0001110_1 : Blocks := edgeBlocks% "full/vectors/0001110-V-0001.bin"
private noncomputable def vp0001110_2 : Blocks := edgeBlocks% "full/vectors/0001110-V-0002.bin"
private noncomputable def vp0001110_3 : Blocks := edgeBlocks% "full/vectors/0001110-V-0003.bin"
private noncomputable def vp0001110_4 : Blocks := edgeBlocks% "full/vectors/0001110-V-0004.bin"
private noncomputable def vp0001110_5 : Blocks := edgeBlocks% "full/vectors/0001110-V-0005.bin"
private noncomputable def vp0001110_6 : Blocks := edgeBlocks% "full/vectors/0001110-V-0006.bin"
private noncomputable def vp0001110_7 : Blocks := edgeBlocks% "full/vectors/0001110-V-0007.bin"
private noncomputable def vp0001110_8 : Blocks := edgeBlocks% "full/vectors/0001110-V-0008.bin"
private noncomputable def vp0001110_9 : Blocks := edgeBlocks% "full/vectors/0001110-V-0009.bin"
private noncomputable def vp0001110_10 : Blocks := edgeBlocks% "full/vectors/0001110-V-0010.bin"
private noncomputable def vp0001110_11 : Blocks := edgeBlocks% "full/vectors/0001110-V-0011.bin"
private noncomputable def vp0001110_12 : Blocks := edgeBlocks% "full/vectors/0001110-V-0012.bin"
private noncomputable def vp0001110_13 : Blocks := edgeBlocks% "full/vectors/0001110-V-0013.bin"
private noncomputable def vp0001110_14 : Blocks := edgeBlocks% "full/vectors/0001110-V-0014.bin"
private noncomputable def vp0001110_15 : Blocks := edgeBlocks% "full/vectors/0001110-V-0015.bin"
private noncomputable def vp0001110_16 : Blocks := edgeBlocks% "full/vectors/0001110-V-0016.bin"
noncomputable def vp0001110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001110_0 vp0001110_1) (Blocks.join vp0001110_2 vp0001110_3)) (Blocks.join (Blocks.join vp0001110_4 vp0001110_5) (Blocks.join vp0001110_6 vp0001110_7))) (Blocks.join (Blocks.join (Blocks.join vp0001110_8 vp0001110_9) (Blocks.join vp0001110_10 vp0001110_11)) (Blocks.join (Blocks.join vp0001110_12 vp0001110_13) (Blocks.join vp0001110_14 (Blocks.join vp0001110_15 vp0001110_16)))))
private theorem bp00011100 : Branch 0 (-895761639/64000000 : ℚ) vp0001110 := by
  apply branch_left_normalized (c:=vp00011100) (k:=0) (m:=1057) (by decide +kernel)
  rw [show 2*(-895761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/32000000 : ℚ) by norm_num]
  exact coverp00011100
private noncomputable def ep00011101_0 : Blocks := edgeBlocks% "full/vectors/00011101-E-0000.bin"
private noncomputable def ep00011101_1 : Blocks := edgeBlocks% "full/vectors/00011101-E-0001.bin"
private noncomputable def ep00011101_2 : Blocks := edgeBlocks% "full/vectors/00011101-E-0002.bin"
private noncomputable def ep00011101_3 : Blocks := edgeBlocks% "full/vectors/00011101-E-0003.bin"
private noncomputable def ep00011101_4 : Blocks := edgeBlocks% "full/vectors/00011101-E-0004.bin"
private noncomputable def ep00011101_5 : Blocks := edgeBlocks% "full/vectors/00011101-E-0005.bin"
private noncomputable def ep00011101_6 : Blocks := edgeBlocks% "full/vectors/00011101-E-0006.bin"
private noncomputable def ep00011101_7 : Blocks := edgeBlocks% "full/vectors/00011101-E-0007.bin"
private noncomputable def ep00011101_8 : Blocks := edgeBlocks% "full/vectors/00011101-E-0008.bin"
private noncomputable def ep00011101_9 : Blocks := edgeBlocks% "full/vectors/00011101-E-0009.bin"
private noncomputable def ep00011101_10 : Blocks := edgeBlocks% "full/vectors/00011101-E-0010.bin"
private noncomputable def ep00011101_11 : Blocks := edgeBlocks% "full/vectors/00011101-E-0011.bin"
private noncomputable def ep00011101_12 : Blocks := edgeBlocks% "full/vectors/00011101-E-0012.bin"
private noncomputable def ep00011101_13 : Blocks := edgeBlocks% "full/vectors/00011101-E-0013.bin"
private noncomputable def ep00011101_14 : Blocks := edgeBlocks% "full/vectors/00011101-E-0014.bin"
private noncomputable def ep00011101_15 : Blocks := edgeBlocks% "full/vectors/00011101-E-0015.bin"
private noncomputable def ep00011101_16 : Blocks := edgeBlocks% "full/vectors/00011101-E-0016.bin"
noncomputable def ep00011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00011101_0 ep00011101_1) (Blocks.join ep00011101_2 ep00011101_3)) (Blocks.join (Blocks.join ep00011101_4 ep00011101_5) (Blocks.join ep00011101_6 ep00011101_7))) (Blocks.join (Blocks.join (Blocks.join ep00011101_8 ep00011101_9) (Blocks.join ep00011101_10 ep00011101_11)) (Blocks.join (Blocks.join ep00011101_12 ep00011101_13) (Blocks.join ep00011101_14 (Blocks.join ep00011101_15 ep00011101_16)))))
private theorem idp00011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001110.list =
    C ((2:ℤ)^2255) * horner X vp00011101.list + horner X ep00011101.list := by
  exact edge_identity (B := (2:ℤ)^3265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011101 : Branch 1 (-895761639/64000000 : ℚ) vp0001110 := by
  apply branch_checked idp00011101 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-927761639/32000000 : ℚ) by norm_num]
  exact coverp00011101
theorem coverp0001110 : Covers (-895761639/64000000 : ℚ) vp0001110 := join_branches bp00011100 bp00011101
private noncomputable def vp000111_0 : Blocks := edgeBlocks% "full/vectors/000111-V-0000.bin"
private noncomputable def vp000111_1 : Blocks := edgeBlocks% "full/vectors/000111-V-0001.bin"
private noncomputable def vp000111_2 : Blocks := edgeBlocks% "full/vectors/000111-V-0002.bin"
private noncomputable def vp000111_3 : Blocks := edgeBlocks% "full/vectors/000111-V-0003.bin"
private noncomputable def vp000111_4 : Blocks := edgeBlocks% "full/vectors/000111-V-0004.bin"
private noncomputable def vp000111_5 : Blocks := edgeBlocks% "full/vectors/000111-V-0005.bin"
private noncomputable def vp000111_6 : Blocks := edgeBlocks% "full/vectors/000111-V-0006.bin"
private noncomputable def vp000111_7 : Blocks := edgeBlocks% "full/vectors/000111-V-0007.bin"
private noncomputable def vp000111_8 : Blocks := edgeBlocks% "full/vectors/000111-V-0008.bin"
private noncomputable def vp000111_9 : Blocks := edgeBlocks% "full/vectors/000111-V-0009.bin"
private noncomputable def vp000111_10 : Blocks := edgeBlocks% "full/vectors/000111-V-0010.bin"
private noncomputable def vp000111_11 : Blocks := edgeBlocks% "full/vectors/000111-V-0011.bin"
private noncomputable def vp000111_12 : Blocks := edgeBlocks% "full/vectors/000111-V-0012.bin"
private noncomputable def vp000111_13 : Blocks := edgeBlocks% "full/vectors/000111-V-0013.bin"
private noncomputable def vp000111_14 : Blocks := edgeBlocks% "full/vectors/000111-V-0014.bin"
private noncomputable def vp000111_15 : Blocks := edgeBlocks% "full/vectors/000111-V-0015.bin"
private noncomputable def vp000111_16 : Blocks := edgeBlocks% "full/vectors/000111-V-0016.bin"
private noncomputable def vp000111_17 : Blocks := edgeBlocks% "full/vectors/000111-V-0017.bin"
private noncomputable def vp000111_18 : Blocks := edgeBlocks% "full/vectors/000111-V-0018.bin"
private noncomputable def vp000111_19 : Blocks := edgeBlocks% "full/vectors/000111-V-0019.bin"
private noncomputable def vp000111_20 : Blocks := edgeBlocks% "full/vectors/000111-V-0020.bin"
private noncomputable def vp000111_21 : Blocks := edgeBlocks% "full/vectors/000111-V-0021.bin"
private noncomputable def vp000111_22 : Blocks := edgeBlocks% "full/vectors/000111-V-0022.bin"
private noncomputable def vp000111_23 : Blocks := edgeBlocks% "full/vectors/000111-V-0023.bin"
private noncomputable def vp000111_24 : Blocks := edgeBlocks% "full/vectors/000111-V-0024.bin"
private noncomputable def vp000111_25 : Blocks := edgeBlocks% "full/vectors/000111-V-0025.bin"
private noncomputable def vp000111_26 : Blocks := edgeBlocks% "full/vectors/000111-V-0026.bin"
private noncomputable def vp000111_27 : Blocks := edgeBlocks% "full/vectors/000111-V-0027.bin"
private noncomputable def vp000111_28 : Blocks := edgeBlocks% "full/vectors/000111-V-0028.bin"
private noncomputable def vp000111_29 : Blocks := edgeBlocks% "full/vectors/000111-V-0029.bin"
private noncomputable def vp000111_30 : Blocks := edgeBlocks% "full/vectors/000111-V-0030.bin"
noncomputable def vp000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000111_0 (Blocks.join vp000111_1 vp000111_2)) (Blocks.join (Blocks.join vp000111_3 vp000111_4) (Blocks.join vp000111_5 vp000111_6))) (Blocks.join (Blocks.join (Blocks.join vp000111_7 vp000111_8) (Blocks.join vp000111_9 vp000111_10)) (Blocks.join (Blocks.join vp000111_11 vp000111_12) (Blocks.join vp000111_13 vp000111_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000111_15 vp000111_16) (Blocks.join vp000111_17 vp000111_18)) (Blocks.join (Blocks.join vp000111_19 vp000111_20) (Blocks.join vp000111_21 vp000111_22))) (Blocks.join (Blocks.join (Blocks.join vp000111_23 vp000111_24) (Blocks.join vp000111_25 vp000111_26)) (Blocks.join (Blocks.join vp000111_27 vp000111_28) (Blocks.join vp000111_29 vp000111_30)))))
private theorem bp0001110 : Branch 0 (-895761639/128000000 : ℚ) vp000111 := by
  apply branch_left_normalized (c:=vp0001110) (k:=0) (m:=2059) (by decide +kernel)
  rw [show 2*(-895761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-895761639/64000000 : ℚ) by norm_num]
  exact coverp0001110
private noncomputable def ep0001111_0 : Blocks := edgeBlocks% "full/vectors/0001111-E-0000.bin"
private noncomputable def ep0001111_1 : Blocks := edgeBlocks% "full/vectors/0001111-E-0001.bin"
private noncomputable def ep0001111_2 : Blocks := edgeBlocks% "full/vectors/0001111-E-0002.bin"
private noncomputable def ep0001111_3 : Blocks := edgeBlocks% "full/vectors/0001111-E-0003.bin"
private noncomputable def ep0001111_4 : Blocks := edgeBlocks% "full/vectors/0001111-E-0004.bin"
private noncomputable def ep0001111_5 : Blocks := edgeBlocks% "full/vectors/0001111-E-0005.bin"
private noncomputable def ep0001111_6 : Blocks := edgeBlocks% "full/vectors/0001111-E-0006.bin"
private noncomputable def ep0001111_7 : Blocks := edgeBlocks% "full/vectors/0001111-E-0007.bin"
private noncomputable def ep0001111_8 : Blocks := edgeBlocks% "full/vectors/0001111-E-0008.bin"
private noncomputable def ep0001111_9 : Blocks := edgeBlocks% "full/vectors/0001111-E-0009.bin"
private noncomputable def ep0001111_10 : Blocks := edgeBlocks% "full/vectors/0001111-E-0010.bin"
private noncomputable def ep0001111_11 : Blocks := edgeBlocks% "full/vectors/0001111-E-0011.bin"
private noncomputable def ep0001111_12 : Blocks := edgeBlocks% "full/vectors/0001111-E-0012.bin"
private noncomputable def ep0001111_13 : Blocks := edgeBlocks% "full/vectors/0001111-E-0013.bin"
private noncomputable def ep0001111_14 : Blocks := edgeBlocks% "full/vectors/0001111-E-0014.bin"
private noncomputable def ep0001111_15 : Blocks := edgeBlocks% "full/vectors/0001111-E-0015.bin"
private noncomputable def ep0001111_16 : Blocks := edgeBlocks% "full/vectors/0001111-E-0016.bin"
private noncomputable def ep0001111_17 : Blocks := edgeBlocks% "full/vectors/0001111-E-0017.bin"
private noncomputable def ep0001111_18 : Blocks := edgeBlocks% "full/vectors/0001111-E-0018.bin"
private noncomputable def ep0001111_19 : Blocks := edgeBlocks% "full/vectors/0001111-E-0019.bin"
private noncomputable def ep0001111_20 : Blocks := edgeBlocks% "full/vectors/0001111-E-0020.bin"
private noncomputable def ep0001111_21 : Blocks := edgeBlocks% "full/vectors/0001111-E-0021.bin"
private noncomputable def ep0001111_22 : Blocks := edgeBlocks% "full/vectors/0001111-E-0022.bin"
private noncomputable def ep0001111_23 : Blocks := edgeBlocks% "full/vectors/0001111-E-0023.bin"
private noncomputable def ep0001111_24 : Blocks := edgeBlocks% "full/vectors/0001111-E-0024.bin"
private noncomputable def ep0001111_25 : Blocks := edgeBlocks% "full/vectors/0001111-E-0025.bin"
private noncomputable def ep0001111_26 : Blocks := edgeBlocks% "full/vectors/0001111-E-0026.bin"
private noncomputable def ep0001111_27 : Blocks := edgeBlocks% "full/vectors/0001111-E-0027.bin"
private noncomputable def ep0001111_28 : Blocks := edgeBlocks% "full/vectors/0001111-E-0028.bin"
private noncomputable def ep0001111_29 : Blocks := edgeBlocks% "full/vectors/0001111-E-0029.bin"
private noncomputable def ep0001111_30 : Blocks := edgeBlocks% "full/vectors/0001111-E-0030.bin"
noncomputable def ep0001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001111_0 (Blocks.join ep0001111_1 ep0001111_2)) (Blocks.join (Blocks.join ep0001111_3 ep0001111_4) (Blocks.join ep0001111_5 ep0001111_6))) (Blocks.join (Blocks.join (Blocks.join ep0001111_7 ep0001111_8) (Blocks.join ep0001111_9 ep0001111_10)) (Blocks.join (Blocks.join ep0001111_11 ep0001111_12) (Blocks.join ep0001111_13 ep0001111_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001111_15 ep0001111_16) (Blocks.join ep0001111_17 ep0001111_18)) (Blocks.join (Blocks.join ep0001111_19 ep0001111_20) (Blocks.join ep0001111_21 ep0001111_22))) (Blocks.join (Blocks.join (Blocks.join ep0001111_23 ep0001111_24) (Blocks.join ep0001111_25 ep0001111_26)) (Blocks.join (Blocks.join ep0001111_27 ep0001111_28) (Blocks.join ep0001111_29 ep0001111_30)))))
private def ptsp0001111 : List ℤ := [((2:ℤ)^3028+0),((2:ℤ)^3028+1),((2:ℤ)^3028+2)]
private theorem boundp0001111 : 2^vp000111.size*absSum vp000111.list + ((2:ℤ)^4334*absSum vp0001111.list+absSum ep0001111.list) < (2:ℤ)^6246 := by decide +kernel
private theorem pointp0001111_0 : fastHom 1 ((2:ℤ)^3028+0) vp000111 = ((2:ℤ)^4334)*vp0001111.subst ((2:ℤ)^3028+0)+ep0001111.subst ((2:ℤ)^3028+0) := by decide +kernel
private theorem pointp0001111_1 : fastHom 1 ((2:ℤ)^3028+1) vp000111 = ((2:ℤ)^4334)*vp0001111.subst ((2:ℤ)^3028+1)+ep0001111.subst ((2:ℤ)^3028+1) := by decide +kernel
private theorem pointp0001111_2 : fastHom 1 ((2:ℤ)^3028+2) vp000111 = ((2:ℤ)^4334)*vp0001111.subst ((2:ℤ)^3028+2)+ep0001111.subst ((2:ℤ)^3028+2) := by decide +kernel
private theorem checkp0001111 (x:ℤ) (hx:x ∈ ptsp0001111) : fastHom 1 x vp000111 = ((2:ℤ)^4334)*vp0001111.subst x+ep0001111.subst x := by
  simp only [ptsp0001111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp0001111_0
  · exact pointp0001111_1
  · exact pointp0001111_2
private theorem idp0001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111.list =
    C ((2:ℤ)^4334) * horner X vp0001111.list + horner X ep0001111.list := by
  apply edge_identity (B := (2:ℤ)^6246) (by decide) (by positivity) (by positivity) boundp0001111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0001111 (by decide +kernel)
  · have h : ptsp0001111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0001111.trans_le (by decide +kernel)
  · exact checkp0001111
private theorem bp0001111 : Branch 1 (-895761639/128000000 : ℚ) vp000111 := by
  apply branch_checked idp0001111 (by positivity) (by decide +kernel)
  rw [show 2*(-895761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-959761639/64000000 : ℚ) by norm_num]
  exact coverp0001111
theorem coverp000111 : Covers (-895761639/128000000 : ℚ) vp000111 := join_branches bp0001110 bp0001111
end NextProof.EdgeFull

