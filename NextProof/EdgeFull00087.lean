import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00086

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010000111111_0 : Blocks := edgeBlocks% "full/vectors/0010000111111-V-0000.bin"
noncomputable def vp0010000111111 : Blocks := vp0010000111111_0
theorem coverp0010000111111 : Covers (-1086761639/1000000 : ℚ) vp0010000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000111110_0 : Blocks := edgeBlocks% "full/vectors/0010000111110-V-0000.bin"
noncomputable def vp0010000111110 : Blocks := vp0010000111110_0
theorem coverp0010000111110 : Covers (-1085761639/1000000 : ℚ) vp0010000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011111_0 : Blocks := edgeBlocks% "full/vectors/001000011111-V-0000.bin"
noncomputable def vp001000011111 : Blocks := vp001000011111_0
private theorem bp0010000111110 : Branch 0 (-1085761639/2000000 : ℚ) vp001000011111 := by
  apply branch_left_normalized (c:=vp0010000111110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1085761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1085761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111110
private noncomputable def ep0010000111111_0 : Blocks := edgeBlocks% "full/vectors/0010000111111-E-0000.bin"
noncomputable def ep0010000111111 : Blocks := ep0010000111111_0
private theorem idp0010000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011111.list =
    C ((2:ℤ)^87) * horner X vp0010000111111.list + horner X ep0010000111111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000111111 : Branch 1 (-1085761639/2000000 : ℚ) vp001000011111 := by
  apply branch_checked idp0010000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1085761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1086761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111111
theorem coverp001000011111 : Covers (-1085761639/2000000 : ℚ) vp001000011111 := join_branches bp0010000111110 bp0010000111111
private noncomputable def vp0010000111101_0 : Blocks := edgeBlocks% "full/vectors/0010000111101-V-0000.bin"
noncomputable def vp0010000111101 : Blocks := vp0010000111101_0
theorem coverp0010000111101 : Covers (-1084761639/1000000 : ℚ) vp0010000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000111100_0 : Blocks := edgeBlocks% "full/vectors/0010000111100-V-0000.bin"
noncomputable def vp0010000111100 : Blocks := vp0010000111100_0
theorem coverp0010000111100 : Covers (-1083761639/1000000 : ℚ) vp0010000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011110_0 : Blocks := edgeBlocks% "full/vectors/001000011110-V-0000.bin"
noncomputable def vp001000011110 : Blocks := vp001000011110_0
private theorem bp0010000111100 : Branch 0 (-1083761639/2000000 : ℚ) vp001000011110 := by
  apply branch_left_normalized (c:=vp0010000111100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1083761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1083761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111100
private noncomputable def ep0010000111101_0 : Blocks := edgeBlocks% "full/vectors/0010000111101-E-0000.bin"
noncomputable def ep0010000111101 : Blocks := ep0010000111101_0
private theorem idp0010000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011110.list =
    C ((2:ℤ)^87) * horner X vp0010000111101.list + horner X ep0010000111101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000111101 : Branch 1 (-1083761639/2000000 : ℚ) vp001000011110 := by
  apply branch_checked idp0010000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1083761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1084761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111101
theorem coverp001000011110 : Covers (-1083761639/2000000 : ℚ) vp001000011110 := join_branches bp0010000111100 bp0010000111101
private noncomputable def vp00100001111_0 : Blocks := edgeBlocks% "full/vectors/00100001111-V-0000.bin"
private noncomputable def vp00100001111_1 : Blocks := edgeBlocks% "full/vectors/00100001111-V-0001.bin"
noncomputable def vp00100001111 : Blocks := (Blocks.join vp00100001111_0 vp00100001111_1)
private theorem bp001000011110 : Branch 0 (-1083761639/4000000 : ℚ) vp00100001111 := by
  apply branch_left_normalized (c:=vp001000011110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1083761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1083761639/2000000 : ℚ) by norm_num]
  exact coverp001000011110
private noncomputable def ep001000011111_0 : Blocks := edgeBlocks% "full/vectors/001000011111-E-0000.bin"
private noncomputable def ep001000011111_1 : Blocks := edgeBlocks% "full/vectors/001000011111-E-0001.bin"
noncomputable def ep001000011111 : Blocks := (Blocks.join ep001000011111_0 ep001000011111_1)
private theorem idp001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001111.list =
    C ((2:ℤ)^153) * horner X vp001000011111.list + horner X ep001000011111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000011111 : Branch 1 (-1083761639/4000000 : ℚ) vp00100001111 := by
  apply branch_checked idp001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1083761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1085761639/2000000 : ℚ) by norm_num]
  exact coverp001000011111
theorem coverp00100001111 : Covers (-1083761639/4000000 : ℚ) vp00100001111 := join_branches bp001000011110 bp001000011111
private noncomputable def vp0010000111011_0 : Blocks := edgeBlocks% "full/vectors/0010000111011-V-0000.bin"
noncomputable def vp0010000111011 : Blocks := vp0010000111011_0
theorem coverp0010000111011 : Covers (-1082761639/1000000 : ℚ) vp0010000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000111010_0 : Blocks := edgeBlocks% "full/vectors/0010000111010-V-0000.bin"
noncomputable def vp0010000111010 : Blocks := vp0010000111010_0
theorem coverp0010000111010 : Covers (-1081761639/1000000 : ℚ) vp0010000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011101_0 : Blocks := edgeBlocks% "full/vectors/001000011101-V-0000.bin"
noncomputable def vp001000011101 : Blocks := vp001000011101_0
private theorem bp0010000111010 : Branch 0 (-1081761639/2000000 : ℚ) vp001000011101 := by
  apply branch_left_normalized (c:=vp0010000111010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1081761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1081761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111010
private noncomputable def ep0010000111011_0 : Blocks := edgeBlocks% "full/vectors/0010000111011-E-0000.bin"
noncomputable def ep0010000111011 : Blocks := ep0010000111011_0
private theorem idp0010000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011101.list =
    C ((2:ℤ)^87) * horner X vp0010000111011.list + horner X ep0010000111011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000111011 : Branch 1 (-1081761639/2000000 : ℚ) vp001000011101 := by
  apply branch_checked idp0010000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1081761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1082761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111011
theorem coverp001000011101 : Covers (-1081761639/2000000 : ℚ) vp001000011101 := join_branches bp0010000111010 bp0010000111011
private noncomputable def vp0010000111001_0 : Blocks := edgeBlocks% "full/vectors/0010000111001-V-0000.bin"
noncomputable def vp0010000111001 : Blocks := vp0010000111001_0
theorem coverp0010000111001 : Covers (-1080761639/1000000 : ℚ) vp0010000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000111000_0 : Blocks := edgeBlocks% "full/vectors/0010000111000-V-0000.bin"
noncomputable def vp0010000111000 : Blocks := vp0010000111000_0
theorem coverp0010000111000 : Covers (-1079761639/1000000 : ℚ) vp0010000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011100_0 : Blocks := edgeBlocks% "full/vectors/001000011100-V-0000.bin"
noncomputable def vp001000011100 : Blocks := vp001000011100_0
private theorem bp0010000111000 : Branch 0 (-1079761639/2000000 : ℚ) vp001000011100 := by
  apply branch_left_normalized (c:=vp0010000111000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1079761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1079761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111000
private noncomputable def ep0010000111001_0 : Blocks := edgeBlocks% "full/vectors/0010000111001-E-0000.bin"
noncomputable def ep0010000111001 : Blocks := ep0010000111001_0
private theorem idp0010000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011100.list =
    C ((2:ℤ)^87) * horner X vp0010000111001.list + horner X ep0010000111001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000111001 : Branch 1 (-1079761639/2000000 : ℚ) vp001000011100 := by
  apply branch_checked idp0010000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1079761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1080761639/1000000 : ℚ) by norm_num]
  exact coverp0010000111001
theorem coverp001000011100 : Covers (-1079761639/2000000 : ℚ) vp001000011100 := join_branches bp0010000111000 bp0010000111001
private noncomputable def vp00100001110_0 : Blocks := edgeBlocks% "full/vectors/00100001110-V-0000.bin"
private noncomputable def vp00100001110_1 : Blocks := edgeBlocks% "full/vectors/00100001110-V-0001.bin"
noncomputable def vp00100001110 : Blocks := (Blocks.join vp00100001110_0 vp00100001110_1)
private theorem bp001000011100 : Branch 0 (-1079761639/4000000 : ℚ) vp00100001110 := by
  apply branch_left_normalized (c:=vp001000011100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1079761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1079761639/2000000 : ℚ) by norm_num]
  exact coverp001000011100
private noncomputable def ep001000011101_0 : Blocks := edgeBlocks% "full/vectors/001000011101-E-0000.bin"
private noncomputable def ep001000011101_1 : Blocks := edgeBlocks% "full/vectors/001000011101-E-0001.bin"
noncomputable def ep001000011101 : Blocks := (Blocks.join ep001000011101_0 ep001000011101_1)
private theorem idp001000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001110.list =
    C ((2:ℤ)^154) * horner X vp001000011101.list + horner X ep001000011101.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000011101 : Branch 1 (-1079761639/4000000 : ℚ) vp00100001110 := by
  apply branch_checked idp001000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1079761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1081761639/2000000 : ℚ) by norm_num]
  exact coverp001000011101
theorem coverp00100001110 : Covers (-1079761639/4000000 : ℚ) vp00100001110 := join_branches bp001000011100 bp001000011101
private noncomputable def vp0010000111_0 : Blocks := edgeBlocks% "full/vectors/0010000111-V-0000.bin"
private noncomputable def vp0010000111_1 : Blocks := edgeBlocks% "full/vectors/0010000111-V-0001.bin"
private noncomputable def vp0010000111_2 : Blocks := edgeBlocks% "full/vectors/0010000111-V-0002.bin"
noncomputable def vp0010000111 : Blocks := (Blocks.join vp0010000111_0 (Blocks.join vp0010000111_1 vp0010000111_2))
private theorem bp00100001110 : Branch 0 (-1079761639/8000000 : ℚ) vp0010000111 := by
  apply branch_left_normalized (c:=vp00100001110) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-1079761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1079761639/4000000 : ℚ) by norm_num]
  exact coverp00100001110
private noncomputable def ep00100001111_0 : Blocks := edgeBlocks% "full/vectors/00100001111-E-0000.bin"
private noncomputable def ep00100001111_1 : Blocks := edgeBlocks% "full/vectors/00100001111-E-0001.bin"
private noncomputable def ep00100001111_2 : Blocks := edgeBlocks% "full/vectors/00100001111-E-0002.bin"
noncomputable def ep00100001111 : Blocks := (Blocks.join ep00100001111_0 (Blocks.join ep00100001111_1 ep00100001111_2))
private theorem idp00100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000111.list =
    C ((2:ℤ)^285) * horner X vp00100001111.list + horner X ep00100001111.list := by
  exact edge_identity (B := (2:ℤ)^490) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100001111 : Branch 1 (-1079761639/8000000 : ℚ) vp0010000111 := by
  apply branch_checked idp00100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1079761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1083761639/4000000 : ℚ) by norm_num]
  exact coverp00100001111
theorem coverp0010000111 : Covers (-1079761639/8000000 : ℚ) vp0010000111 := join_branches bp00100001110 bp00100001111
private noncomputable def vp0010000110111_0 : Blocks := edgeBlocks% "full/vectors/0010000110111-V-0000.bin"
noncomputable def vp0010000110111 : Blocks := vp0010000110111_0
theorem coverp0010000110111 : Covers (-1078761639/1000000 : ℚ) vp0010000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000110110_0 : Blocks := edgeBlocks% "full/vectors/0010000110110-V-0000.bin"
noncomputable def vp0010000110110 : Blocks := vp0010000110110_0
theorem coverp0010000110110 : Covers (-1077761639/1000000 : ℚ) vp0010000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011011_0 : Blocks := edgeBlocks% "full/vectors/001000011011-V-0000.bin"
noncomputable def vp001000011011 : Blocks := vp001000011011_0
private theorem bp0010000110110 : Branch 0 (-1077761639/2000000 : ℚ) vp001000011011 := by
  apply branch_left_normalized (c:=vp0010000110110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1077761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1077761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110110
private noncomputable def ep0010000110111_0 : Blocks := edgeBlocks% "full/vectors/0010000110111-E-0000.bin"
noncomputable def ep0010000110111 : Blocks := ep0010000110111_0
private theorem idp0010000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011011.list =
    C ((2:ℤ)^88) * horner X vp0010000110111.list + horner X ep0010000110111.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000110111 : Branch 1 (-1077761639/2000000 : ℚ) vp001000011011 := by
  apply branch_checked idp0010000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1077761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1078761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110111
theorem coverp001000011011 : Covers (-1077761639/2000000 : ℚ) vp001000011011 := join_branches bp0010000110110 bp0010000110111
private noncomputable def vp0010000110101_0 : Blocks := edgeBlocks% "full/vectors/0010000110101-V-0000.bin"
noncomputable def vp0010000110101 : Blocks := vp0010000110101_0
theorem coverp0010000110101 : Covers (-1076761639/1000000 : ℚ) vp0010000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000110100_0 : Blocks := edgeBlocks% "full/vectors/0010000110100-V-0000.bin"
noncomputable def vp0010000110100 : Blocks := vp0010000110100_0
theorem coverp0010000110100 : Covers (-1075761639/1000000 : ℚ) vp0010000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011010_0 : Blocks := edgeBlocks% "full/vectors/001000011010-V-0000.bin"
noncomputable def vp001000011010 : Blocks := vp001000011010_0
private theorem bp0010000110100 : Branch 0 (-1075761639/2000000 : ℚ) vp001000011010 := by
  apply branch_left_normalized (c:=vp0010000110100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1075761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1075761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110100
private noncomputable def ep0010000110101_0 : Blocks := edgeBlocks% "full/vectors/0010000110101-E-0000.bin"
noncomputable def ep0010000110101 : Blocks := ep0010000110101_0
private theorem idp0010000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011010.list =
    C ((2:ℤ)^86) * horner X vp0010000110101.list + horner X ep0010000110101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000110101 : Branch 1 (-1075761639/2000000 : ℚ) vp001000011010 := by
  apply branch_checked idp0010000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1075761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1076761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110101
theorem coverp001000011010 : Covers (-1075761639/2000000 : ℚ) vp001000011010 := join_branches bp0010000110100 bp0010000110101
private noncomputable def vp00100001101_0 : Blocks := edgeBlocks% "full/vectors/00100001101-V-0000.bin"
private noncomputable def vp00100001101_1 : Blocks := edgeBlocks% "full/vectors/00100001101-V-0001.bin"
noncomputable def vp00100001101 : Blocks := (Blocks.join vp00100001101_0 vp00100001101_1)
private theorem bp001000011010 : Branch 0 (-1075761639/4000000 : ℚ) vp00100001101 := by
  apply branch_left_normalized (c:=vp001000011010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1075761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1075761639/2000000 : ℚ) by norm_num]
  exact coverp001000011010
private noncomputable def ep001000011011_0 : Blocks := edgeBlocks% "full/vectors/001000011011-E-0000.bin"
private noncomputable def ep001000011011_1 : Blocks := edgeBlocks% "full/vectors/001000011011-E-0001.bin"
noncomputable def ep001000011011 : Blocks := (Blocks.join ep001000011011_0 ep001000011011_1)
private theorem idp001000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001101.list =
    C ((2:ℤ)^153) * horner X vp001000011011.list + horner X ep001000011011.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000011011 : Branch 1 (-1075761639/4000000 : ℚ) vp00100001101 := by
  apply branch_checked idp001000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1075761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1077761639/2000000 : ℚ) by norm_num]
  exact coverp001000011011
theorem coverp00100001101 : Covers (-1075761639/4000000 : ℚ) vp00100001101 := join_branches bp001000011010 bp001000011011
private noncomputable def vp0010000110011_0 : Blocks := edgeBlocks% "full/vectors/0010000110011-V-0000.bin"
noncomputable def vp0010000110011 : Blocks := vp0010000110011_0
theorem coverp0010000110011 : Covers (-1074761639/1000000 : ℚ) vp0010000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000110010_0 : Blocks := edgeBlocks% "full/vectors/0010000110010-V-0000.bin"
noncomputable def vp0010000110010 : Blocks := vp0010000110010_0
theorem coverp0010000110010 : Covers (-1073761639/1000000 : ℚ) vp0010000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011001_0 : Blocks := edgeBlocks% "full/vectors/001000011001-V-0000.bin"
noncomputable def vp001000011001 : Blocks := vp001000011001_0
private theorem bp0010000110010 : Branch 0 (-1073761639/2000000 : ℚ) vp001000011001 := by
  apply branch_left_normalized (c:=vp0010000110010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1073761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1073761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110010
private noncomputable def ep0010000110011_0 : Blocks := edgeBlocks% "full/vectors/0010000110011-E-0000.bin"
noncomputable def ep0010000110011 : Blocks := ep0010000110011_0
private theorem idp0010000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011001.list =
    C ((2:ℤ)^86) * horner X vp0010000110011.list + horner X ep0010000110011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000110011 : Branch 1 (-1073761639/2000000 : ℚ) vp001000011001 := by
  apply branch_checked idp0010000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1073761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1074761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110011
theorem coverp001000011001 : Covers (-1073761639/2000000 : ℚ) vp001000011001 := join_branches bp0010000110010 bp0010000110011
private noncomputable def vp0010000110001_0 : Blocks := edgeBlocks% "full/vectors/0010000110001-V-0000.bin"
noncomputable def vp0010000110001 : Blocks := vp0010000110001_0
theorem coverp0010000110001 : Covers (-1072761639/1000000 : ℚ) vp0010000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000110000_0 : Blocks := edgeBlocks% "full/vectors/0010000110000-V-0000.bin"
noncomputable def vp0010000110000 : Blocks := vp0010000110000_0
theorem coverp0010000110000 : Covers (-1071761639/1000000 : ℚ) vp0010000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000011000_0 : Blocks := edgeBlocks% "full/vectors/001000011000-V-0000.bin"
noncomputable def vp001000011000 : Blocks := vp001000011000_0
private theorem bp0010000110000 : Branch 0 (-1071761639/2000000 : ℚ) vp001000011000 := by
  apply branch_left_normalized (c:=vp0010000110000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1071761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1071761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110000
private noncomputable def ep0010000110001_0 : Blocks := edgeBlocks% "full/vectors/0010000110001-E-0000.bin"
noncomputable def ep0010000110001 : Blocks := ep0010000110001_0
private theorem idp0010000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011000.list =
    C ((2:ℤ)^88) * horner X vp0010000110001.list + horner X ep0010000110001.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000110001 : Branch 1 (-1071761639/2000000 : ℚ) vp001000011000 := by
  apply branch_checked idp0010000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1071761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1072761639/1000000 : ℚ) by norm_num]
  exact coverp0010000110001
theorem coverp001000011000 : Covers (-1071761639/2000000 : ℚ) vp001000011000 := join_branches bp0010000110000 bp0010000110001
private noncomputable def vp00100001100_0 : Blocks := edgeBlocks% "full/vectors/00100001100-V-0000.bin"
private noncomputable def vp00100001100_1 : Blocks := edgeBlocks% "full/vectors/00100001100-V-0001.bin"
noncomputable def vp00100001100 : Blocks := (Blocks.join vp00100001100_0 vp00100001100_1)
private theorem bp001000011000 : Branch 0 (-1071761639/4000000 : ℚ) vp00100001100 := by
  apply branch_left_normalized (c:=vp001000011000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-1071761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1071761639/2000000 : ℚ) by norm_num]
  exact coverp001000011000
private noncomputable def ep001000011001_0 : Blocks := edgeBlocks% "full/vectors/001000011001-E-0000.bin"
private noncomputable def ep001000011001_1 : Blocks := edgeBlocks% "full/vectors/001000011001-E-0001.bin"
noncomputable def ep001000011001 : Blocks := (Blocks.join ep001000011001_0 ep001000011001_1)
private theorem idp001000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001100.list =
    C ((2:ℤ)^154) * horner X vp001000011001.list + horner X ep001000011001.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000011001 : Branch 1 (-1071761639/4000000 : ℚ) vp00100001100 := by
  apply branch_checked idp001000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1071761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1073761639/2000000 : ℚ) by norm_num]
  exact coverp001000011001
theorem coverp00100001100 : Covers (-1071761639/4000000 : ℚ) vp00100001100 := join_branches bp001000011000 bp001000011001
private noncomputable def vp0010000110_0 : Blocks := edgeBlocks% "full/vectors/0010000110-V-0000.bin"
private noncomputable def vp0010000110_1 : Blocks := edgeBlocks% "full/vectors/0010000110-V-0001.bin"
private noncomputable def vp0010000110_2 : Blocks := edgeBlocks% "full/vectors/0010000110-V-0002.bin"
noncomputable def vp0010000110 : Blocks := (Blocks.join vp0010000110_0 (Blocks.join vp0010000110_1 vp0010000110_2))
private theorem bp00100001100 : Branch 0 (-1071761639/8000000 : ℚ) vp0010000110 := by
  apply branch_left_normalized (c:=vp00100001100) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-1071761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1071761639/4000000 : ℚ) by norm_num]
  exact coverp00100001100
private noncomputable def ep00100001101_0 : Blocks := edgeBlocks% "full/vectors/00100001101-E-0000.bin"
private noncomputable def ep00100001101_1 : Blocks := edgeBlocks% "full/vectors/00100001101-E-0001.bin"
private noncomputable def ep00100001101_2 : Blocks := edgeBlocks% "full/vectors/00100001101-E-0002.bin"
noncomputable def ep00100001101 : Blocks := (Blocks.join ep00100001101_0 (Blocks.join ep00100001101_1 ep00100001101_2))
private theorem idp00100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000110.list =
    C ((2:ℤ)^285) * horner X vp00100001101.list + horner X ep00100001101.list := by
  exact edge_identity (B := (2:ℤ)^490) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100001101 : Branch 1 (-1071761639/8000000 : ℚ) vp0010000110 := by
  apply branch_checked idp00100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1071761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1075761639/4000000 : ℚ) by norm_num]
  exact coverp00100001101
theorem coverp0010000110 : Covers (-1071761639/8000000 : ℚ) vp0010000110 := join_branches bp00100001100 bp00100001101
private noncomputable def vp001000011_0 : Blocks := edgeBlocks% "full/vectors/001000011-V-0000.bin"
private noncomputable def vp001000011_1 : Blocks := edgeBlocks% "full/vectors/001000011-V-0001.bin"
private noncomputable def vp001000011_2 : Blocks := edgeBlocks% "full/vectors/001000011-V-0002.bin"
private noncomputable def vp001000011_3 : Blocks := edgeBlocks% "full/vectors/001000011-V-0003.bin"
noncomputable def vp001000011 : Blocks := (Blocks.join (Blocks.join vp001000011_0 vp001000011_1) (Blocks.join vp001000011_2 vp001000011_3))
private theorem bp0010000110 : Branch 0 (-1071761639/16000000 : ℚ) vp001000011 := by
  apply branch_left_normalized (c:=vp0010000110) (k:=0) (m:=261) (by decide +kernel)
  rw [show 2*(-1071761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1071761639/8000000 : ℚ) by norm_num]
  exact coverp0010000110
private noncomputable def ep0010000111_0 : Blocks := edgeBlocks% "full/vectors/0010000111-E-0000.bin"
private noncomputable def ep0010000111_1 : Blocks := edgeBlocks% "full/vectors/0010000111-E-0001.bin"
private noncomputable def ep0010000111_2 : Blocks := edgeBlocks% "full/vectors/0010000111-E-0002.bin"
private noncomputable def ep0010000111_3 : Blocks := edgeBlocks% "full/vectors/0010000111-E-0003.bin"
noncomputable def ep0010000111 : Blocks := (Blocks.join (Blocks.join ep0010000111_0 ep0010000111_1) (Blocks.join ep0010000111_2 ep0010000111_3))
private theorem idp0010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000011.list =
    C ((2:ℤ)^546) * horner X vp0010000111.list + horner X ep0010000111.list := by
  exact edge_identity (B := (2:ℤ)^855) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000111 : Branch 1 (-1071761639/16000000 : ℚ) vp001000011 := by
  apply branch_checked idp0010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1071761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1079761639/8000000 : ℚ) by norm_num]
  exact coverp0010000111
theorem coverp001000011 : Covers (-1071761639/16000000 : ℚ) vp001000011 := join_branches bp0010000110 bp0010000111
private noncomputable def vp0010000101111_0 : Blocks := edgeBlocks% "full/vectors/0010000101111-V-0000.bin"
noncomputable def vp0010000101111 : Blocks := vp0010000101111_0
theorem coverp0010000101111 : Covers (-1070761639/1000000 : ℚ) vp0010000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000101110_0 : Blocks := edgeBlocks% "full/vectors/0010000101110-V-0000.bin"
noncomputable def vp0010000101110 : Blocks := vp0010000101110_0
theorem coverp0010000101110 : Covers (-1069761639/1000000 : ℚ) vp0010000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010111_0 : Blocks := edgeBlocks% "full/vectors/001000010111-V-0000.bin"
noncomputable def vp001000010111 : Blocks := vp001000010111_0
private theorem bp0010000101110 : Branch 0 (-1069761639/2000000 : ℚ) vp001000010111 := by
  apply branch_left_normalized (c:=vp0010000101110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1069761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1069761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101110
private noncomputable def ep0010000101111_0 : Blocks := edgeBlocks% "full/vectors/0010000101111-E-0000.bin"
noncomputable def ep0010000101111 : Blocks := ep0010000101111_0
private theorem idp0010000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010111.list =
    C ((2:ℤ)^87) * horner X vp0010000101111.list + horner X ep0010000101111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000101111 : Branch 1 (-1069761639/2000000 : ℚ) vp001000010111 := by
  apply branch_checked idp0010000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1069761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1070761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101111
theorem coverp001000010111 : Covers (-1069761639/2000000 : ℚ) vp001000010111 := join_branches bp0010000101110 bp0010000101111
private noncomputable def vp0010000101101_0 : Blocks := edgeBlocks% "full/vectors/0010000101101-V-0000.bin"
noncomputable def vp0010000101101 : Blocks := vp0010000101101_0
theorem coverp0010000101101 : Covers (-1068761639/1000000 : ℚ) vp0010000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000101100_0 : Blocks := edgeBlocks% "full/vectors/0010000101100-V-0000.bin"
noncomputable def vp0010000101100 : Blocks := vp0010000101100_0
theorem coverp0010000101100 : Covers (-1067761639/1000000 : ℚ) vp0010000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010110_0 : Blocks := edgeBlocks% "full/vectors/001000010110-V-0000.bin"
noncomputable def vp001000010110 : Blocks := vp001000010110_0
private theorem bp0010000101100 : Branch 0 (-1067761639/2000000 : ℚ) vp001000010110 := by
  apply branch_left_normalized (c:=vp0010000101100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1067761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1067761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101100
private noncomputable def ep0010000101101_0 : Blocks := edgeBlocks% "full/vectors/0010000101101-E-0000.bin"
noncomputable def ep0010000101101 : Blocks := ep0010000101101_0
private theorem idp0010000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010110.list =
    C ((2:ℤ)^87) * horner X vp0010000101101.list + horner X ep0010000101101.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000101101 : Branch 1 (-1067761639/2000000 : ℚ) vp001000010110 := by
  apply branch_checked idp0010000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1067761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1068761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101101
theorem coverp001000010110 : Covers (-1067761639/2000000 : ℚ) vp001000010110 := join_branches bp0010000101100 bp0010000101101
private noncomputable def vp00100001011_0 : Blocks := edgeBlocks% "full/vectors/00100001011-V-0000.bin"
private noncomputable def vp00100001011_1 : Blocks := edgeBlocks% "full/vectors/00100001011-V-0001.bin"
noncomputable def vp00100001011 : Blocks := (Blocks.join vp00100001011_0 vp00100001011_1)
private theorem bp001000010110 : Branch 0 (-1067761639/4000000 : ℚ) vp00100001011 := by
  apply branch_left_normalized (c:=vp001000010110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-1067761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1067761639/2000000 : ℚ) by norm_num]
  exact coverp001000010110
private noncomputable def ep001000010111_0 : Blocks := edgeBlocks% "full/vectors/001000010111-E-0000.bin"
private noncomputable def ep001000010111_1 : Blocks := edgeBlocks% "full/vectors/001000010111-E-0001.bin"
noncomputable def ep001000010111 : Blocks := (Blocks.join ep001000010111_0 ep001000010111_1)
private theorem idp001000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001011.list =
    C ((2:ℤ)^153) * horner X vp001000010111.list + horner X ep001000010111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000010111 : Branch 1 (-1067761639/4000000 : ℚ) vp00100001011 := by
  apply branch_checked idp001000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1067761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1069761639/2000000 : ℚ) by norm_num]
  exact coverp001000010111
theorem coverp00100001011 : Covers (-1067761639/4000000 : ℚ) vp00100001011 := join_branches bp001000010110 bp001000010111
private noncomputable def vp0010000101011_0 : Blocks := edgeBlocks% "full/vectors/0010000101011-V-0000.bin"
noncomputable def vp0010000101011 : Blocks := vp0010000101011_0
theorem coverp0010000101011 : Covers (-1066761639/1000000 : ℚ) vp0010000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000101010_0 : Blocks := edgeBlocks% "full/vectors/0010000101010-V-0000.bin"
noncomputable def vp0010000101010 : Blocks := vp0010000101010_0
theorem coverp0010000101010 : Covers (-1065761639/1000000 : ℚ) vp0010000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010101_0 : Blocks := edgeBlocks% "full/vectors/001000010101-V-0000.bin"
noncomputable def vp001000010101 : Blocks := vp001000010101_0
private theorem bp0010000101010 : Branch 0 (-1065761639/2000000 : ℚ) vp001000010101 := by
  apply branch_left_normalized (c:=vp0010000101010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1065761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1065761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101010
private noncomputable def ep0010000101011_0 : Blocks := edgeBlocks% "full/vectors/0010000101011-E-0000.bin"
noncomputable def ep0010000101011 : Blocks := ep0010000101011_0
private theorem idp0010000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010101.list =
    C ((2:ℤ)^86) * horner X vp0010000101011.list + horner X ep0010000101011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000101011 : Branch 1 (-1065761639/2000000 : ℚ) vp001000010101 := by
  apply branch_checked idp0010000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1065761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1066761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101011
theorem coverp001000010101 : Covers (-1065761639/2000000 : ℚ) vp001000010101 := join_branches bp0010000101010 bp0010000101011
private noncomputable def vp0010000101001_0 : Blocks := edgeBlocks% "full/vectors/0010000101001-V-0000.bin"
noncomputable def vp0010000101001 : Blocks := vp0010000101001_0
theorem coverp0010000101001 : Covers (-1064761639/1000000 : ℚ) vp0010000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000101000_0 : Blocks := edgeBlocks% "full/vectors/0010000101000-V-0000.bin"
noncomputable def vp0010000101000 : Blocks := vp0010000101000_0
theorem coverp0010000101000 : Covers (-1063761639/1000000 : ℚ) vp0010000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010100_0 : Blocks := edgeBlocks% "full/vectors/001000010100-V-0000.bin"
noncomputable def vp001000010100 : Blocks := vp001000010100_0
private theorem bp0010000101000 : Branch 0 (-1063761639/2000000 : ℚ) vp001000010100 := by
  apply branch_left_normalized (c:=vp0010000101000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1063761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1063761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101000
private noncomputable def ep0010000101001_0 : Blocks := edgeBlocks% "full/vectors/0010000101001-E-0000.bin"
noncomputable def ep0010000101001 : Blocks := ep0010000101001_0
private theorem idp0010000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010100.list =
    C ((2:ℤ)^86) * horner X vp0010000101001.list + horner X ep0010000101001.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000101001 : Branch 1 (-1063761639/2000000 : ℚ) vp001000010100 := by
  apply branch_checked idp0010000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1063761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1064761639/1000000 : ℚ) by norm_num]
  exact coverp0010000101001
theorem coverp001000010100 : Covers (-1063761639/2000000 : ℚ) vp001000010100 := join_branches bp0010000101000 bp0010000101001
private noncomputable def vp00100001010_0 : Blocks := edgeBlocks% "full/vectors/00100001010-V-0000.bin"
private noncomputable def vp00100001010_1 : Blocks := edgeBlocks% "full/vectors/00100001010-V-0001.bin"
noncomputable def vp00100001010 : Blocks := (Blocks.join vp00100001010_0 vp00100001010_1)
private theorem bp001000010100 : Branch 0 (-1063761639/4000000 : ℚ) vp00100001010 := by
  apply branch_left_normalized (c:=vp001000010100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1063761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1063761639/2000000 : ℚ) by norm_num]
  exact coverp001000010100
private noncomputable def ep001000010101_0 : Blocks := edgeBlocks% "full/vectors/001000010101-E-0000.bin"
private noncomputable def ep001000010101_1 : Blocks := edgeBlocks% "full/vectors/001000010101-E-0001.bin"
noncomputable def ep001000010101 : Blocks := (Blocks.join ep001000010101_0 ep001000010101_1)
private theorem idp001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001010.list =
    C ((2:ℤ)^154) * horner X vp001000010101.list + horner X ep001000010101.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000010101 : Branch 1 (-1063761639/4000000 : ℚ) vp00100001010 := by
  apply branch_checked idp001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1063761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1065761639/2000000 : ℚ) by norm_num]
  exact coverp001000010101
theorem coverp00100001010 : Covers (-1063761639/4000000 : ℚ) vp00100001010 := join_branches bp001000010100 bp001000010101
private noncomputable def vp0010000101_0 : Blocks := edgeBlocks% "full/vectors/0010000101-V-0000.bin"
private noncomputable def vp0010000101_1 : Blocks := edgeBlocks% "full/vectors/0010000101-V-0001.bin"
private noncomputable def vp0010000101_2 : Blocks := edgeBlocks% "full/vectors/0010000101-V-0002.bin"
noncomputable def vp0010000101 : Blocks := (Blocks.join vp0010000101_0 (Blocks.join vp0010000101_1 vp0010000101_2))
private theorem bp00100001010 : Branch 0 (-1063761639/8000000 : ℚ) vp0010000101 := by
  apply branch_left_normalized (c:=vp00100001010) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-1063761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1063761639/4000000 : ℚ) by norm_num]
  exact coverp00100001010
private noncomputable def ep00100001011_0 : Blocks := edgeBlocks% "full/vectors/00100001011-E-0000.bin"
private noncomputable def ep00100001011_1 : Blocks := edgeBlocks% "full/vectors/00100001011-E-0001.bin"
private noncomputable def ep00100001011_2 : Blocks := edgeBlocks% "full/vectors/00100001011-E-0002.bin"
noncomputable def ep00100001011 : Blocks := (Blocks.join ep00100001011_0 (Blocks.join ep00100001011_1 ep00100001011_2))
private theorem idp00100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000101.list =
    C ((2:ℤ)^284) * horner X vp00100001011.list + horner X ep00100001011.list := by
  exact edge_identity (B := (2:ℤ)^489) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100001011 : Branch 1 (-1063761639/8000000 : ℚ) vp0010000101 := by
  apply branch_checked idp00100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1063761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1067761639/4000000 : ℚ) by norm_num]
  exact coverp00100001011
theorem coverp0010000101 : Covers (-1063761639/8000000 : ℚ) vp0010000101 := join_branches bp00100001010 bp00100001011
private noncomputable def vp0010000100111_0 : Blocks := edgeBlocks% "full/vectors/0010000100111-V-0000.bin"
noncomputable def vp0010000100111 : Blocks := vp0010000100111_0
theorem coverp0010000100111 : Covers (-1062761639/1000000 : ℚ) vp0010000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000100110_0 : Blocks := edgeBlocks% "full/vectors/0010000100110-V-0000.bin"
noncomputable def vp0010000100110 : Blocks := vp0010000100110_0
theorem coverp0010000100110 : Covers (-1061761639/1000000 : ℚ) vp0010000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010011_0 : Blocks := edgeBlocks% "full/vectors/001000010011-V-0000.bin"
noncomputable def vp001000010011 : Blocks := vp001000010011_0
private theorem bp0010000100110 : Branch 0 (-1061761639/2000000 : ℚ) vp001000010011 := by
  apply branch_left_normalized (c:=vp0010000100110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1061761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1061761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100110
private noncomputable def ep0010000100111_0 : Blocks := edgeBlocks% "full/vectors/0010000100111-E-0000.bin"
noncomputable def ep0010000100111 : Blocks := ep0010000100111_0
private theorem idp0010000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010011.list =
    C ((2:ℤ)^87) * horner X vp0010000100111.list + horner X ep0010000100111.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000100111 : Branch 1 (-1061761639/2000000 : ℚ) vp001000010011 := by
  apply branch_checked idp0010000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1061761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1062761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100111
theorem coverp001000010011 : Covers (-1061761639/2000000 : ℚ) vp001000010011 := join_branches bp0010000100110 bp0010000100111
private noncomputable def vp0010000100101_0 : Blocks := edgeBlocks% "full/vectors/0010000100101-V-0000.bin"
noncomputable def vp0010000100101 : Blocks := vp0010000100101_0
theorem coverp0010000100101 : Covers (-1060761639/1000000 : ℚ) vp0010000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000100100_0 : Blocks := edgeBlocks% "full/vectors/0010000100100-V-0000.bin"
noncomputable def vp0010000100100 : Blocks := vp0010000100100_0
theorem coverp0010000100100 : Covers (-1059761639/1000000 : ℚ) vp0010000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010010_0 : Blocks := edgeBlocks% "full/vectors/001000010010-V-0000.bin"
noncomputable def vp001000010010 : Blocks := vp001000010010_0
private theorem bp0010000100100 : Branch 0 (-1059761639/2000000 : ℚ) vp001000010010 := by
  apply branch_left_normalized (c:=vp0010000100100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1059761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1059761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100100
private noncomputable def ep0010000100101_0 : Blocks := edgeBlocks% "full/vectors/0010000100101-E-0000.bin"
noncomputable def ep0010000100101 : Blocks := ep0010000100101_0
private theorem idp0010000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010010.list =
    C ((2:ℤ)^88) * horner X vp0010000100101.list + horner X ep0010000100101.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000100101 : Branch 1 (-1059761639/2000000 : ℚ) vp001000010010 := by
  apply branch_checked idp0010000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1059761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1060761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100101
theorem coverp001000010010 : Covers (-1059761639/2000000 : ℚ) vp001000010010 := join_branches bp0010000100100 bp0010000100101
private noncomputable def vp00100001001_0 : Blocks := edgeBlocks% "full/vectors/00100001001-V-0000.bin"
private noncomputable def vp00100001001_1 : Blocks := edgeBlocks% "full/vectors/00100001001-V-0001.bin"
noncomputable def vp00100001001 : Blocks := (Blocks.join vp00100001001_0 vp00100001001_1)
private theorem bp001000010010 : Branch 0 (-1059761639/4000000 : ℚ) vp00100001001 := by
  apply branch_left_normalized (c:=vp001000010010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-1059761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1059761639/2000000 : ℚ) by norm_num]
  exact coverp001000010010
private noncomputable def ep001000010011_0 : Blocks := edgeBlocks% "full/vectors/001000010011-E-0000.bin"
private noncomputable def ep001000010011_1 : Blocks := edgeBlocks% "full/vectors/001000010011-E-0001.bin"
noncomputable def ep001000010011 : Blocks := (Blocks.join ep001000010011_0 ep001000010011_1)
private theorem idp001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001001.list =
    C ((2:ℤ)^156) * horner X vp001000010011.list + horner X ep001000010011.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000010011 : Branch 1 (-1059761639/4000000 : ℚ) vp00100001001 := by
  apply branch_checked idp001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1059761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1061761639/2000000 : ℚ) by norm_num]
  exact coverp001000010011
theorem coverp00100001001 : Covers (-1059761639/4000000 : ℚ) vp00100001001 := join_branches bp001000010010 bp001000010011
private noncomputable def vp0010000100011_0 : Blocks := edgeBlocks% "full/vectors/0010000100011-V-0000.bin"
noncomputable def vp0010000100011 : Blocks := vp0010000100011_0
theorem coverp0010000100011 : Covers (-1058761639/1000000 : ℚ) vp0010000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000100010_0 : Blocks := edgeBlocks% "full/vectors/0010000100010-V-0000.bin"
noncomputable def vp0010000100010 : Blocks := vp0010000100010_0
theorem coverp0010000100010 : Covers (-1057761639/1000000 : ℚ) vp0010000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010001_0 : Blocks := edgeBlocks% "full/vectors/001000010001-V-0000.bin"
noncomputable def vp001000010001 : Blocks := vp001000010001_0
private theorem bp0010000100010 : Branch 0 (-1057761639/2000000 : ℚ) vp001000010001 := by
  apply branch_left_normalized (c:=vp0010000100010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1057761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1057761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100010
private noncomputable def ep0010000100011_0 : Blocks := edgeBlocks% "full/vectors/0010000100011-E-0000.bin"
noncomputable def ep0010000100011 : Blocks := ep0010000100011_0
private theorem idp0010000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010001.list =
    C ((2:ℤ)^84) * horner X vp0010000100011.list + horner X ep0010000100011.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000100011 : Branch 1 (-1057761639/2000000 : ℚ) vp001000010001 := by
  apply branch_checked idp0010000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1057761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1058761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100011
theorem coverp001000010001 : Covers (-1057761639/2000000 : ℚ) vp001000010001 := join_branches bp0010000100010 bp0010000100011
private noncomputable def vp0010000100001_0 : Blocks := edgeBlocks% "full/vectors/0010000100001-V-0000.bin"
noncomputable def vp0010000100001 : Blocks := vp0010000100001_0
theorem coverp0010000100001 : Covers (-1056761639/1000000 : ℚ) vp0010000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000100000_0 : Blocks := edgeBlocks% "full/vectors/0010000100000-V-0000.bin"
noncomputable def vp0010000100000 : Blocks := vp0010000100000_0
theorem coverp0010000100000 : Covers (-1055761639/1000000 : ℚ) vp0010000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000010000_0 : Blocks := edgeBlocks% "full/vectors/001000010000-V-0000.bin"
noncomputable def vp001000010000 : Blocks := vp001000010000_0
private theorem bp0010000100000 : Branch 0 (-1055761639/2000000 : ℚ) vp001000010000 := by
  apply branch_left_normalized (c:=vp0010000100000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1055761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1055761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100000
private noncomputable def ep0010000100001_0 : Blocks := edgeBlocks% "full/vectors/0010000100001-E-0000.bin"
noncomputable def ep0010000100001 : Blocks := ep0010000100001_0
private theorem idp0010000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010000.list =
    C ((2:ℤ)^85) * horner X vp0010000100001.list + horner X ep0010000100001.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000100001 : Branch 1 (-1055761639/2000000 : ℚ) vp001000010000 := by
  apply branch_checked idp0010000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1055761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1056761639/1000000 : ℚ) by norm_num]
  exact coverp0010000100001
theorem coverp001000010000 : Covers (-1055761639/2000000 : ℚ) vp001000010000 := join_branches bp0010000100000 bp0010000100001
private noncomputable def vp00100001000_0 : Blocks := edgeBlocks% "full/vectors/00100001000-V-0000.bin"
private noncomputable def vp00100001000_1 : Blocks := edgeBlocks% "full/vectors/00100001000-V-0001.bin"
noncomputable def vp00100001000 : Blocks := (Blocks.join vp00100001000_0 vp00100001000_1)
private theorem bp001000010000 : Branch 0 (-1055761639/4000000 : ℚ) vp00100001000 := by
  apply branch_left_normalized (c:=vp001000010000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1055761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1055761639/2000000 : ℚ) by norm_num]
  exact coverp001000010000
private noncomputable def ep001000010001_0 : Blocks := edgeBlocks% "full/vectors/001000010001-E-0000.bin"
private noncomputable def ep001000010001_1 : Blocks := edgeBlocks% "full/vectors/001000010001-E-0001.bin"
noncomputable def ep001000010001 : Blocks := (Blocks.join ep001000010001_0 ep001000010001_1)
private theorem idp001000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001000.list =
    C ((2:ℤ)^151) * horner X vp001000010001.list + horner X ep001000010001.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000010001 : Branch 1 (-1055761639/4000000 : ℚ) vp00100001000 := by
  apply branch_checked idp001000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1055761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1057761639/2000000 : ℚ) by norm_num]
  exact coverp001000010001
theorem coverp00100001000 : Covers (-1055761639/4000000 : ℚ) vp00100001000 := join_branches bp001000010000 bp001000010001
private noncomputable def vp0010000100_0 : Blocks := edgeBlocks% "full/vectors/0010000100-V-0000.bin"
private noncomputable def vp0010000100_1 : Blocks := edgeBlocks% "full/vectors/0010000100-V-0001.bin"
private noncomputable def vp0010000100_2 : Blocks := edgeBlocks% "full/vectors/0010000100-V-0002.bin"
noncomputable def vp0010000100 : Blocks := (Blocks.join vp0010000100_0 (Blocks.join vp0010000100_1 vp0010000100_2))
private theorem bp00100001000 : Branch 0 (-1055761639/8000000 : ℚ) vp0010000100 := by
  apply branch_left_normalized (c:=vp00100001000) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-1055761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1055761639/4000000 : ℚ) by norm_num]
  exact coverp00100001000
private noncomputable def ep00100001001_0 : Blocks := edgeBlocks% "full/vectors/00100001001-E-0000.bin"
private noncomputable def ep00100001001_1 : Blocks := edgeBlocks% "full/vectors/00100001001-E-0001.bin"
private noncomputable def ep00100001001_2 : Blocks := edgeBlocks% "full/vectors/00100001001-E-0002.bin"
noncomputable def ep00100001001 : Blocks := (Blocks.join ep00100001001_0 (Blocks.join ep00100001001_1 ep00100001001_2))
private theorem idp00100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000100.list =
    C ((2:ℤ)^280) * horner X vp00100001001.list + horner X ep00100001001.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100001001 : Branch 1 (-1055761639/8000000 : ℚ) vp0010000100 := by
  apply branch_checked idp00100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1055761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1059761639/4000000 : ℚ) by norm_num]
  exact coverp00100001001
theorem coverp0010000100 : Covers (-1055761639/8000000 : ℚ) vp0010000100 := join_branches bp00100001000 bp00100001001
private noncomputable def vp001000010_0 : Blocks := edgeBlocks% "full/vectors/001000010-V-0000.bin"
private noncomputable def vp001000010_1 : Blocks := edgeBlocks% "full/vectors/001000010-V-0001.bin"
private noncomputable def vp001000010_2 : Blocks := edgeBlocks% "full/vectors/001000010-V-0002.bin"
private noncomputable def vp001000010_3 : Blocks := edgeBlocks% "full/vectors/001000010-V-0003.bin"
noncomputable def vp001000010 : Blocks := (Blocks.join (Blocks.join vp001000010_0 vp001000010_1) (Blocks.join vp001000010_2 vp001000010_3))
private theorem bp0010000100 : Branch 0 (-1055761639/16000000 : ℚ) vp001000010 := by
  apply branch_left_normalized (c:=vp0010000100) (k:=0) (m:=261) (by decide +kernel)
  rw [show 2*(-1055761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1055761639/8000000 : ℚ) by norm_num]
  exact coverp0010000100
private noncomputable def ep0010000101_0 : Blocks := edgeBlocks% "full/vectors/0010000101-E-0000.bin"
private noncomputable def ep0010000101_1 : Blocks := edgeBlocks% "full/vectors/0010000101-E-0001.bin"
private noncomputable def ep0010000101_2 : Blocks := edgeBlocks% "full/vectors/0010000101-E-0002.bin"
private noncomputable def ep0010000101_3 : Blocks := edgeBlocks% "full/vectors/0010000101-E-0003.bin"
noncomputable def ep0010000101 : Blocks := (Blocks.join (Blocks.join ep0010000101_0 ep0010000101_1) (Blocks.join ep0010000101_2 ep0010000101_3))
private theorem idp0010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000010.list =
    C ((2:ℤ)^544) * horner X vp0010000101.list + horner X ep0010000101.list := by
  exact edge_identity (B := (2:ℤ)^854) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000101 : Branch 1 (-1055761639/16000000 : ℚ) vp001000010 := by
  apply branch_checked idp0010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1055761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1063761639/8000000 : ℚ) by norm_num]
  exact coverp0010000101
theorem coverp001000010 : Covers (-1055761639/16000000 : ℚ) vp001000010 := join_branches bp0010000100 bp0010000101
private noncomputable def vp00100001_0 : Blocks := edgeBlocks% "full/vectors/00100001-V-0000.bin"
private noncomputable def vp00100001_1 : Blocks := edgeBlocks% "full/vectors/00100001-V-0001.bin"
private noncomputable def vp00100001_2 : Blocks := edgeBlocks% "full/vectors/00100001-V-0002.bin"
private noncomputable def vp00100001_3 : Blocks := edgeBlocks% "full/vectors/00100001-V-0003.bin"
private noncomputable def vp00100001_4 : Blocks := edgeBlocks% "full/vectors/00100001-V-0004.bin"
private noncomputable def vp00100001_5 : Blocks := edgeBlocks% "full/vectors/00100001-V-0005.bin"
private noncomputable def vp00100001_6 : Blocks := edgeBlocks% "full/vectors/00100001-V-0006.bin"
private noncomputable def vp00100001_7 : Blocks := edgeBlocks% "full/vectors/00100001-V-0007.bin"
noncomputable def vp00100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100001_0 vp00100001_1) (Blocks.join vp00100001_2 vp00100001_3)) (Blocks.join (Blocks.join vp00100001_4 vp00100001_5) (Blocks.join vp00100001_6 vp00100001_7)))
private theorem bp001000010 : Branch 0 (-1055761639/32000000 : ℚ) vp00100001 := by
  apply branch_left_normalized (c:=vp001000010) (k:=0) (m:=500) (by decide +kernel)
  rw [show 2*(-1055761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1055761639/16000000 : ℚ) by norm_num]
  exact coverp001000010
private noncomputable def ep001000011_0 : Blocks := edgeBlocks% "full/vectors/001000011-E-0000.bin"
private noncomputable def ep001000011_1 : Blocks := edgeBlocks% "full/vectors/001000011-E-0001.bin"
private noncomputable def ep001000011_2 : Blocks := edgeBlocks% "full/vectors/001000011-E-0002.bin"
private noncomputable def ep001000011_3 : Blocks := edgeBlocks% "full/vectors/001000011-E-0003.bin"
private noncomputable def ep001000011_4 : Blocks := edgeBlocks% "full/vectors/001000011-E-0004.bin"
private noncomputable def ep001000011_5 : Blocks := edgeBlocks% "full/vectors/001000011-E-0005.bin"
private noncomputable def ep001000011_6 : Blocks := edgeBlocks% "full/vectors/001000011-E-0006.bin"
private noncomputable def ep001000011_7 : Blocks := edgeBlocks% "full/vectors/001000011-E-0007.bin"
noncomputable def ep001000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001000011_0 ep001000011_1) (Blocks.join ep001000011_2 ep001000011_3)) (Blocks.join (Blocks.join ep001000011_4 ep001000011_5) (Blocks.join ep001000011_6 ep001000011_7)))
private theorem idp001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100001.list =
    C ((2:ℤ)^1063) * horner X vp001000011.list + horner X ep001000011.list := by
  exact edge_identity (B := (2:ℤ)^1583) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000011 : Branch 1 (-1055761639/32000000 : ℚ) vp00100001 := by
  apply branch_checked idp001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1055761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1071761639/16000000 : ℚ) by norm_num]
  exact coverp001000011
theorem coverp00100001 : Covers (-1055761639/32000000 : ℚ) vp00100001 := join_branches bp001000010 bp001000011
private noncomputable def vp0010000011111_0 : Blocks := edgeBlocks% "full/vectors/0010000011111-V-0000.bin"
noncomputable def vp0010000011111 : Blocks := vp0010000011111_0
theorem coverp0010000011111 : Covers (-1054761639/1000000 : ℚ) vp0010000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000011110_0 : Blocks := edgeBlocks% "full/vectors/0010000011110-V-0000.bin"
noncomputable def vp0010000011110 : Blocks := vp0010000011110_0
theorem coverp0010000011110 : Covers (-1053761639/1000000 : ℚ) vp0010000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001111_0 : Blocks := edgeBlocks% "full/vectors/001000001111-V-0000.bin"
noncomputable def vp001000001111 : Blocks := vp001000001111_0
private theorem bp0010000011110 : Branch 0 (-1053761639/2000000 : ℚ) vp001000001111 := by
  apply branch_left_normalized (c:=vp0010000011110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1053761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1053761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011110
private noncomputable def ep0010000011111_0 : Blocks := edgeBlocks% "full/vectors/0010000011111-E-0000.bin"
noncomputable def ep0010000011111 : Blocks := ep0010000011111_0
private theorem idp0010000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001111.list =
    C ((2:ℤ)^85) * horner X vp0010000011111.list + horner X ep0010000011111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000011111 : Branch 1 (-1053761639/2000000 : ℚ) vp001000001111 := by
  apply branch_checked idp0010000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1053761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1054761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011111
theorem coverp001000001111 : Covers (-1053761639/2000000 : ℚ) vp001000001111 := join_branches bp0010000011110 bp0010000011111
private noncomputable def vp0010000011101_0 : Blocks := edgeBlocks% "full/vectors/0010000011101-V-0000.bin"
noncomputable def vp0010000011101 : Blocks := vp0010000011101_0
theorem coverp0010000011101 : Covers (-1052761639/1000000 : ℚ) vp0010000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000011100_0 : Blocks := edgeBlocks% "full/vectors/0010000011100-V-0000.bin"
noncomputable def vp0010000011100 : Blocks := vp0010000011100_0
theorem coverp0010000011100 : Covers (-1051761639/1000000 : ℚ) vp0010000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001110_0 : Blocks := edgeBlocks% "full/vectors/001000001110-V-0000.bin"
noncomputable def vp001000001110 : Blocks := vp001000001110_0
private theorem bp0010000011100 : Branch 0 (-1051761639/2000000 : ℚ) vp001000001110 := by
  apply branch_left_normalized (c:=vp0010000011100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1051761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1051761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011100
private noncomputable def ep0010000011101_0 : Blocks := edgeBlocks% "full/vectors/0010000011101-E-0000.bin"
noncomputable def ep0010000011101 : Blocks := ep0010000011101_0
private theorem idp0010000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001110.list =
    C ((2:ℤ)^86) * horner X vp0010000011101.list + horner X ep0010000011101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000011101 : Branch 1 (-1051761639/2000000 : ℚ) vp001000001110 := by
  apply branch_checked idp0010000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1051761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1052761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011101
theorem coverp001000001110 : Covers (-1051761639/2000000 : ℚ) vp001000001110 := join_branches bp0010000011100 bp0010000011101
private noncomputable def vp00100000111_0 : Blocks := edgeBlocks% "full/vectors/00100000111-V-0000.bin"
private noncomputable def vp00100000111_1 : Blocks := edgeBlocks% "full/vectors/00100000111-V-0001.bin"
noncomputable def vp00100000111 : Blocks := (Blocks.join vp00100000111_0 vp00100000111_1)
private theorem bp001000001110 : Branch 0 (-1051761639/4000000 : ℚ) vp00100000111 := by
  apply branch_left_normalized (c:=vp001000001110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1051761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1051761639/2000000 : ℚ) by norm_num]
  exact coverp001000001110
private noncomputable def ep001000001111_0 : Blocks := edgeBlocks% "full/vectors/001000001111-E-0000.bin"
private noncomputable def ep001000001111_1 : Blocks := edgeBlocks% "full/vectors/001000001111-E-0001.bin"
noncomputable def ep001000001111 : Blocks := (Blocks.join ep001000001111_0 ep001000001111_1)
private theorem idp001000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000111.list =
    C ((2:ℤ)^154) * horner X vp001000001111.list + horner X ep001000001111.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000001111 : Branch 1 (-1051761639/4000000 : ℚ) vp00100000111 := by
  apply branch_checked idp001000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1051761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1053761639/2000000 : ℚ) by norm_num]
  exact coverp001000001111
theorem coverp00100000111 : Covers (-1051761639/4000000 : ℚ) vp00100000111 := join_branches bp001000001110 bp001000001111
private noncomputable def vp0010000011011_0 : Blocks := edgeBlocks% "full/vectors/0010000011011-V-0000.bin"
noncomputable def vp0010000011011 : Blocks := vp0010000011011_0
theorem coverp0010000011011 : Covers (-1050761639/1000000 : ℚ) vp0010000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000011010_0 : Blocks := edgeBlocks% "full/vectors/0010000011010-V-0000.bin"
noncomputable def vp0010000011010 : Blocks := vp0010000011010_0
theorem coverp0010000011010 : Covers (-1049761639/1000000 : ℚ) vp0010000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001101_0 : Blocks := edgeBlocks% "full/vectors/001000001101-V-0000.bin"
noncomputable def vp001000001101 : Blocks := vp001000001101_0
private theorem bp0010000011010 : Branch 0 (-1049761639/2000000 : ℚ) vp001000001101 := by
  apply branch_left_normalized (c:=vp0010000011010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1049761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1049761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011010
private noncomputable def ep0010000011011_0 : Blocks := edgeBlocks% "full/vectors/0010000011011-E-0000.bin"
noncomputable def ep0010000011011 : Blocks := ep0010000011011_0
private theorem idp0010000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001101.list =
    C ((2:ℤ)^90) * horner X vp0010000011011.list + horner X ep0010000011011.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000011011 : Branch 1 (-1049761639/2000000 : ℚ) vp001000001101 := by
  apply branch_checked idp0010000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1049761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1050761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011011
theorem coverp001000001101 : Covers (-1049761639/2000000 : ℚ) vp001000001101 := join_branches bp0010000011010 bp0010000011011
private noncomputable def vp0010000011001_0 : Blocks := edgeBlocks% "full/vectors/0010000011001-V-0000.bin"
noncomputable def vp0010000011001 : Blocks := vp0010000011001_0
theorem coverp0010000011001 : Covers (-1048761639/1000000 : ℚ) vp0010000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000011000_0 : Blocks := edgeBlocks% "full/vectors/0010000011000-V-0000.bin"
noncomputable def vp0010000011000 : Blocks := vp0010000011000_0
theorem coverp0010000011000 : Covers (-1047761639/1000000 : ℚ) vp0010000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001100_0 : Blocks := edgeBlocks% "full/vectors/001000001100-V-0000.bin"
noncomputable def vp001000001100 : Blocks := vp001000001100_0
private theorem bp0010000011000 : Branch 0 (-1047761639/2000000 : ℚ) vp001000001100 := by
  apply branch_left_normalized (c:=vp0010000011000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1047761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1047761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011000
private noncomputable def ep0010000011001_0 : Blocks := edgeBlocks% "full/vectors/0010000011001-E-0000.bin"
noncomputable def ep0010000011001 : Blocks := ep0010000011001_0
private theorem idp0010000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001100.list =
    C ((2:ℤ)^83) * horner X vp0010000011001.list + horner X ep0010000011001.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000011001 : Branch 1 (-1047761639/2000000 : ℚ) vp001000001100 := by
  apply branch_checked idp0010000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1047761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1048761639/1000000 : ℚ) by norm_num]
  exact coverp0010000011001
theorem coverp001000001100 : Covers (-1047761639/2000000 : ℚ) vp001000001100 := join_branches bp0010000011000 bp0010000011001
private noncomputable def vp00100000110_0 : Blocks := edgeBlocks% "full/vectors/00100000110-V-0000.bin"
private noncomputable def vp00100000110_1 : Blocks := edgeBlocks% "full/vectors/00100000110-V-0001.bin"
noncomputable def vp00100000110 : Blocks := (Blocks.join vp00100000110_0 vp00100000110_1)
private theorem bp001000001100 : Branch 0 (-1047761639/4000000 : ℚ) vp00100000110 := by
  apply branch_left_normalized (c:=vp001000001100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1047761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1047761639/2000000 : ℚ) by norm_num]
  exact coverp001000001100
private noncomputable def ep001000001101_0 : Blocks := edgeBlocks% "full/vectors/001000001101-E-0000.bin"
private noncomputable def ep001000001101_1 : Blocks := edgeBlocks% "full/vectors/001000001101-E-0001.bin"
noncomputable def ep001000001101 : Blocks := (Blocks.join ep001000001101_0 ep001000001101_1)
private theorem idp001000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000110.list =
    C ((2:ℤ)^148) * horner X vp001000001101.list + horner X ep001000001101.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000001101 : Branch 1 (-1047761639/4000000 : ℚ) vp00100000110 := by
  apply branch_checked idp001000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1047761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1049761639/2000000 : ℚ) by norm_num]
  exact coverp001000001101
theorem coverp00100000110 : Covers (-1047761639/4000000 : ℚ) vp00100000110 := join_branches bp001000001100 bp001000001101
private noncomputable def vp0010000011_0 : Blocks := edgeBlocks% "full/vectors/0010000011-V-0000.bin"
private noncomputable def vp0010000011_1 : Blocks := edgeBlocks% "full/vectors/0010000011-V-0001.bin"
private noncomputable def vp0010000011_2 : Blocks := edgeBlocks% "full/vectors/0010000011-V-0002.bin"
noncomputable def vp0010000011 : Blocks := (Blocks.join vp0010000011_0 (Blocks.join vp0010000011_1 vp0010000011_2))
private theorem bp00100000110 : Branch 0 (-1047761639/8000000 : ℚ) vp0010000011 := by
  apply branch_left_normalized (c:=vp00100000110) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-1047761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1047761639/4000000 : ℚ) by norm_num]
  exact coverp00100000110
private noncomputable def ep00100000111_0 : Blocks := edgeBlocks% "full/vectors/00100000111-E-0000.bin"
private noncomputable def ep00100000111_1 : Blocks := edgeBlocks% "full/vectors/00100000111-E-0001.bin"
private noncomputable def ep00100000111_2 : Blocks := edgeBlocks% "full/vectors/00100000111-E-0002.bin"
noncomputable def ep00100000111 : Blocks := (Blocks.join ep00100000111_0 (Blocks.join ep00100000111_1 ep00100000111_2))
private theorem idp00100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000011.list =
    C ((2:ℤ)^285) * horner X vp00100000111.list + horner X ep00100000111.list := by
  exact edge_identity (B := (2:ℤ)^488) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100000111 : Branch 1 (-1047761639/8000000 : ℚ) vp0010000011 := by
  apply branch_checked idp00100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1047761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1051761639/4000000 : ℚ) by norm_num]
  exact coverp00100000111
theorem coverp0010000011 : Covers (-1047761639/8000000 : ℚ) vp0010000011 := join_branches bp00100000110 bp00100000111
private noncomputable def vp0010000010111_0 : Blocks := edgeBlocks% "full/vectors/0010000010111-V-0000.bin"
noncomputable def vp0010000010111 : Blocks := vp0010000010111_0
theorem coverp0010000010111 : Covers (-1046761639/1000000 : ℚ) vp0010000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000010110_0 : Blocks := edgeBlocks% "full/vectors/0010000010110-V-0000.bin"
noncomputable def vp0010000010110 : Blocks := vp0010000010110_0
theorem coverp0010000010110 : Covers (-1045761639/1000000 : ℚ) vp0010000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001011_0 : Blocks := edgeBlocks% "full/vectors/001000001011-V-0000.bin"
noncomputable def vp001000001011 : Blocks := vp001000001011_0
private theorem bp0010000010110 : Branch 0 (-1045761639/2000000 : ℚ) vp001000001011 := by
  apply branch_left_normalized (c:=vp0010000010110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1045761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1045761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010110
private noncomputable def ep0010000010111_0 : Blocks := edgeBlocks% "full/vectors/0010000010111-E-0000.bin"
noncomputable def ep0010000010111 : Blocks := ep0010000010111_0
private theorem idp0010000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001011.list =
    C ((2:ℤ)^82) * horner X vp0010000010111.list + horner X ep0010000010111.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000010111 : Branch 1 (-1045761639/2000000 : ℚ) vp001000001011 := by
  apply branch_checked idp0010000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1045761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1046761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010111
theorem coverp001000001011 : Covers (-1045761639/2000000 : ℚ) vp001000001011 := join_branches bp0010000010110 bp0010000010111
private noncomputable def vp0010000010101_0 : Blocks := edgeBlocks% "full/vectors/0010000010101-V-0000.bin"
noncomputable def vp0010000010101 : Blocks := vp0010000010101_0
theorem coverp0010000010101 : Covers (-1044761639/1000000 : ℚ) vp0010000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000010100_0 : Blocks := edgeBlocks% "full/vectors/0010000010100-V-0000.bin"
noncomputable def vp0010000010100 : Blocks := vp0010000010100_0
theorem coverp0010000010100 : Covers (-1043761639/1000000 : ℚ) vp0010000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001010_0 : Blocks := edgeBlocks% "full/vectors/001000001010-V-0000.bin"
noncomputable def vp001000001010 : Blocks := vp001000001010_0
private theorem bp0010000010100 : Branch 0 (-1043761639/2000000 : ℚ) vp001000001010 := by
  apply branch_left_normalized (c:=vp0010000010100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1043761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1043761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010100
private noncomputable def ep0010000010101_0 : Blocks := edgeBlocks% "full/vectors/0010000010101-E-0000.bin"
noncomputable def ep0010000010101 : Blocks := ep0010000010101_0
private theorem idp0010000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001010.list =
    C ((2:ℤ)^83) * horner X vp0010000010101.list + horner X ep0010000010101.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000010101 : Branch 1 (-1043761639/2000000 : ℚ) vp001000001010 := by
  apply branch_checked idp0010000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1043761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1044761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010101
theorem coverp001000001010 : Covers (-1043761639/2000000 : ℚ) vp001000001010 := join_branches bp0010000010100 bp0010000010101
private noncomputable def vp00100000101_0 : Blocks := edgeBlocks% "full/vectors/00100000101-V-0000.bin"
private noncomputable def vp00100000101_1 : Blocks := edgeBlocks% "full/vectors/00100000101-V-0001.bin"
noncomputable def vp00100000101 : Blocks := (Blocks.join vp00100000101_0 vp00100000101_1)
private theorem bp001000001010 : Branch 0 (-1043761639/4000000 : ℚ) vp00100000101 := by
  apply branch_left_normalized (c:=vp001000001010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1043761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1043761639/2000000 : ℚ) by norm_num]
  exact coverp001000001010
private noncomputable def ep001000001011_0 : Blocks := edgeBlocks% "full/vectors/001000001011-E-0000.bin"
private noncomputable def ep001000001011_1 : Blocks := edgeBlocks% "full/vectors/001000001011-E-0001.bin"
noncomputable def ep001000001011 : Blocks := (Blocks.join ep001000001011_0 ep001000001011_1)
private theorem idp001000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000101.list =
    C ((2:ℤ)^149) * horner X vp001000001011.list + horner X ep001000001011.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000001011 : Branch 1 (-1043761639/4000000 : ℚ) vp00100000101 := by
  apply branch_checked idp001000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1043761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1045761639/2000000 : ℚ) by norm_num]
  exact coverp001000001011
theorem coverp00100000101 : Covers (-1043761639/4000000 : ℚ) vp00100000101 := join_branches bp001000001010 bp001000001011
private noncomputable def vp0010000010011_0 : Blocks := edgeBlocks% "full/vectors/0010000010011-V-0000.bin"
noncomputable def vp0010000010011 : Blocks := vp0010000010011_0
theorem coverp0010000010011 : Covers (-1042761639/1000000 : ℚ) vp0010000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010000010010_0 : Blocks := edgeBlocks% "full/vectors/0010000010010-V-0000.bin"
noncomputable def vp0010000010010 : Blocks := vp0010000010010_0
theorem coverp0010000010010 : Covers (-1041761639/1000000 : ℚ) vp0010000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000001001_0 : Blocks := edgeBlocks% "full/vectors/001000001001-V-0000.bin"
noncomputable def vp001000001001 : Blocks := vp001000001001_0
private theorem bp0010000010010 : Branch 0 (-1041761639/2000000 : ℚ) vp001000001001 := by
  apply branch_left_normalized (c:=vp0010000010010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1041761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1041761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010010
private noncomputable def ep0010000010011_0 : Blocks := edgeBlocks% "full/vectors/0010000010011-E-0000.bin"
noncomputable def ep0010000010011 : Blocks := ep0010000010011_0
private theorem idp0010000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001001.list =
    C ((2:ℤ)^83) * horner X vp0010000010011.list + horner X ep0010000010011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000010011 : Branch 1 (-1041761639/2000000 : ℚ) vp001000001001 := by
  apply branch_checked idp0010000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1041761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1042761639/1000000 : ℚ) by norm_num]
  exact coverp0010000010011
theorem coverp001000001001 : Covers (-1041761639/2000000 : ℚ) vp001000001001 := join_branches bp0010000010010 bp0010000010011
private noncomputable def vp001000001000_0 : Blocks := edgeBlocks% "full/vectors/001000001000-V-0000.bin"
noncomputable def vp001000001000 : Blocks := vp001000001000_0
theorem coverp001000001000 : Covers (-1039761639/2000000 : ℚ) vp001000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00100000100_0 : Blocks := edgeBlocks% "full/vectors/00100000100-V-0000.bin"
private noncomputable def vp00100000100_1 : Blocks := edgeBlocks% "full/vectors/00100000100-V-0001.bin"
noncomputable def vp00100000100 : Blocks := (Blocks.join vp00100000100_0 vp00100000100_1)
private theorem bp001000001000 : Branch 0 (-1039761639/4000000 : ℚ) vp00100000100 := by
  apply branch_left_normalized (c:=vp001000001000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1039761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1039761639/2000000 : ℚ) by norm_num]
  exact coverp001000001000
private noncomputable def ep001000001001_0 : Blocks := edgeBlocks% "full/vectors/001000001001-E-0000.bin"
private noncomputable def ep001000001001_1 : Blocks := edgeBlocks% "full/vectors/001000001001-E-0001.bin"
noncomputable def ep001000001001 : Blocks := (Blocks.join ep001000001001_0 ep001000001001_1)
private theorem idp001000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000100.list =
    C ((2:ℤ)^149) * horner X vp001000001001.list + horner X ep001000001001.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000001001 : Branch 1 (-1039761639/4000000 : ℚ) vp00100000100 := by
  apply branch_checked idp001000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1039761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1041761639/2000000 : ℚ) by norm_num]
  exact coverp001000001001
theorem coverp00100000100 : Covers (-1039761639/4000000 : ℚ) vp00100000100 := join_branches bp001000001000 bp001000001001
private noncomputable def vp0010000010_0 : Blocks := edgeBlocks% "full/vectors/0010000010-V-0000.bin"
private noncomputable def vp0010000010_1 : Blocks := edgeBlocks% "full/vectors/0010000010-V-0001.bin"
private noncomputable def vp0010000010_2 : Blocks := edgeBlocks% "full/vectors/0010000010-V-0002.bin"
noncomputable def vp0010000010 : Blocks := (Blocks.join vp0010000010_0 (Blocks.join vp0010000010_1 vp0010000010_2))
private theorem bp00100000100 : Branch 0 (-1039761639/8000000 : ℚ) vp0010000010 := by
  apply branch_left_normalized (c:=vp00100000100) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-1039761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1039761639/4000000 : ℚ) by norm_num]
  exact coverp00100000100
private noncomputable def ep00100000101_0 : Blocks := edgeBlocks% "full/vectors/00100000101-E-0000.bin"
private noncomputable def ep00100000101_1 : Blocks := edgeBlocks% "full/vectors/00100000101-E-0001.bin"
private noncomputable def ep00100000101_2 : Blocks := edgeBlocks% "full/vectors/00100000101-E-0002.bin"
noncomputable def ep00100000101 : Blocks := (Blocks.join ep00100000101_0 (Blocks.join ep00100000101_1 ep00100000101_2))
private theorem idp00100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000010.list =
    C ((2:ℤ)^282) * horner X vp00100000101.list + horner X ep00100000101.list := by
  exact edge_identity (B := (2:ℤ)^480) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100000101 : Branch 1 (-1039761639/8000000 : ℚ) vp0010000010 := by
  apply branch_checked idp00100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1039761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1043761639/4000000 : ℚ) by norm_num]
  exact coverp00100000101
theorem coverp0010000010 : Covers (-1039761639/8000000 : ℚ) vp0010000010 := join_branches bp00100000100 bp00100000101
private noncomputable def vp001000001_0 : Blocks := edgeBlocks% "full/vectors/001000001-V-0000.bin"
private noncomputable def vp001000001_1 : Blocks := edgeBlocks% "full/vectors/001000001-V-0001.bin"
private noncomputable def vp001000001_2 : Blocks := edgeBlocks% "full/vectors/001000001-V-0002.bin"
private noncomputable def vp001000001_3 : Blocks := edgeBlocks% "full/vectors/001000001-V-0003.bin"
noncomputable def vp001000001 : Blocks := (Blocks.join (Blocks.join vp001000001_0 vp001000001_1) (Blocks.join vp001000001_2 vp001000001_3))
private theorem bp0010000010 : Branch 0 (-1039761639/16000000 : ℚ) vp001000001 := by
  apply branch_left_normalized (c:=vp0010000010) (k:=0) (m:=259) (by decide +kernel)
  rw [show 2*(-1039761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1039761639/8000000 : ℚ) by norm_num]
  exact coverp0010000010
private noncomputable def ep0010000011_0 : Blocks := edgeBlocks% "full/vectors/0010000011-E-0000.bin"
private noncomputable def ep0010000011_1 : Blocks := edgeBlocks% "full/vectors/0010000011-E-0001.bin"
private noncomputable def ep0010000011_2 : Blocks := edgeBlocks% "full/vectors/0010000011-E-0002.bin"
private noncomputable def ep0010000011_3 : Blocks := edgeBlocks% "full/vectors/0010000011-E-0003.bin"
noncomputable def ep0010000011 : Blocks := (Blocks.join (Blocks.join ep0010000011_0 ep0010000011_1) (Blocks.join ep0010000011_2 ep0010000011_3))
private theorem idp0010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000001.list =
    C ((2:ℤ)^542) * horner X vp0010000011.list + horner X ep0010000011.list := by
  exact edge_identity (B := (2:ℤ)^850) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000011 : Branch 1 (-1039761639/16000000 : ℚ) vp001000001 := by
  apply branch_checked idp0010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1039761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1047761639/8000000 : ℚ) by norm_num]
  exact coverp0010000011
theorem coverp001000001 : Covers (-1039761639/16000000 : ℚ) vp001000001 := join_branches bp0010000010 bp0010000011
private noncomputable def vp001000000111_0 : Blocks := edgeBlocks% "full/vectors/001000000111-V-0000.bin"
noncomputable def vp001000000111 : Blocks := vp001000000111_0
theorem coverp001000000111 : Covers (-1037761639/2000000 : ℚ) vp001000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp001000000110_0 : Blocks := edgeBlocks% "full/vectors/001000000110-V-0000.bin"
noncomputable def vp001000000110 : Blocks := vp001000000110_0
theorem coverp001000000110 : Covers (-1035761639/2000000 : ℚ) vp001000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00100000011_0 : Blocks := edgeBlocks% "full/vectors/00100000011-V-0000.bin"
private noncomputable def vp00100000011_1 : Blocks := edgeBlocks% "full/vectors/00100000011-V-0001.bin"
noncomputable def vp00100000011 : Blocks := (Blocks.join vp00100000011_0 vp00100000011_1)
private theorem bp001000000110 : Branch 0 (-1035761639/4000000 : ℚ) vp00100000011 := by
  apply branch_left_normalized (c:=vp001000000110) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1035761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1035761639/2000000 : ℚ) by norm_num]
  exact coverp001000000110
private noncomputable def ep001000000111_0 : Blocks := edgeBlocks% "full/vectors/001000000111-E-0000.bin"
private noncomputable def ep001000000111_1 : Blocks := edgeBlocks% "full/vectors/001000000111-E-0001.bin"
noncomputable def ep001000000111 : Blocks := (Blocks.join ep001000000111_0 ep001000000111_1)
private theorem idp001000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000011.list =
    C ((2:ℤ)^149) * horner X vp001000000111.list + horner X ep001000000111.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000000111 : Branch 1 (-1035761639/4000000 : ℚ) vp00100000011 := by
  apply branch_checked idp001000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1035761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1037761639/2000000 : ℚ) by norm_num]
  exact coverp001000000111
theorem coverp00100000011 : Covers (-1035761639/4000000 : ℚ) vp00100000011 := join_branches bp001000000110 bp001000000111
private noncomputable def vp001000000101_0 : Blocks := edgeBlocks% "full/vectors/001000000101-V-0000.bin"
noncomputable def vp001000000101 : Blocks := vp001000000101_0
theorem coverp001000000101 : Covers (-1033761639/2000000 : ℚ) vp001000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp001000000100_0 : Blocks := edgeBlocks% "full/vectors/001000000100-V-0000.bin"
noncomputable def vp001000000100 : Blocks := vp001000000100_0
theorem coverp001000000100 : Covers (-1031761639/2000000 : ℚ) vp001000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00100000010_0 : Blocks := edgeBlocks% "full/vectors/00100000010-V-0000.bin"
private noncomputable def vp00100000010_1 : Blocks := edgeBlocks% "full/vectors/00100000010-V-0001.bin"
noncomputable def vp00100000010 : Blocks := (Blocks.join vp00100000010_0 vp00100000010_1)
private theorem bp001000000100 : Branch 0 (-1031761639/4000000 : ℚ) vp00100000010 := by
  apply branch_left_normalized (c:=vp001000000100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1031761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1031761639/2000000 : ℚ) by norm_num]
  exact coverp001000000100
private noncomputable def ep001000000101_0 : Blocks := edgeBlocks% "full/vectors/001000000101-E-0000.bin"
private noncomputable def ep001000000101_1 : Blocks := edgeBlocks% "full/vectors/001000000101-E-0001.bin"
noncomputable def ep001000000101 : Blocks := (Blocks.join ep001000000101_0 ep001000000101_1)
private theorem idp001000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000010.list =
    C ((2:ℤ)^149) * horner X vp001000000101.list + horner X ep001000000101.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000000101 : Branch 1 (-1031761639/4000000 : ℚ) vp00100000010 := by
  apply branch_checked idp001000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1031761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1033761639/2000000 : ℚ) by norm_num]
  exact coverp001000000101
theorem coverp00100000010 : Covers (-1031761639/4000000 : ℚ) vp00100000010 := join_branches bp001000000100 bp001000000101
private noncomputable def vp0010000001_0 : Blocks := edgeBlocks% "full/vectors/0010000001-V-0000.bin"
private noncomputable def vp0010000001_1 : Blocks := edgeBlocks% "full/vectors/0010000001-V-0001.bin"
private noncomputable def vp0010000001_2 : Blocks := edgeBlocks% "full/vectors/0010000001-V-0002.bin"
noncomputable def vp0010000001 : Blocks := (Blocks.join vp0010000001_0 (Blocks.join vp0010000001_1 vp0010000001_2))
private theorem bp00100000010 : Branch 0 (-1031761639/8000000 : ℚ) vp0010000001 := by
  apply branch_left_normalized (c:=vp00100000010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-1031761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1031761639/4000000 : ℚ) by norm_num]
  exact coverp00100000010
private noncomputable def ep00100000011_0 : Blocks := edgeBlocks% "full/vectors/00100000011-E-0000.bin"
private noncomputable def ep00100000011_1 : Blocks := edgeBlocks% "full/vectors/00100000011-E-0001.bin"
private noncomputable def ep00100000011_2 : Blocks := edgeBlocks% "full/vectors/00100000011-E-0002.bin"
noncomputable def ep00100000011 : Blocks := (Blocks.join ep00100000011_0 (Blocks.join ep00100000011_1 ep00100000011_2))
private theorem idp00100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000001.list =
    C ((2:ℤ)^284) * horner X vp00100000011.list + horner X ep00100000011.list := by
  exact edge_identity (B := (2:ℤ)^481) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100000011 : Branch 1 (-1031761639/8000000 : ℚ) vp0010000001 := by
  apply branch_checked idp00100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1031761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1035761639/4000000 : ℚ) by norm_num]
  exact coverp00100000011
theorem coverp0010000001 : Covers (-1031761639/8000000 : ℚ) vp0010000001 := join_branches bp00100000010 bp00100000011
private noncomputable def vp001000000011_0 : Blocks := edgeBlocks% "full/vectors/001000000011-V-0000.bin"
noncomputable def vp001000000011 : Blocks := vp001000000011_0
theorem coverp001000000011 : Covers (-1029761639/2000000 : ℚ) vp001000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp001000000010_0 : Blocks := edgeBlocks% "full/vectors/001000000010-V-0000.bin"
noncomputable def vp001000000010 : Blocks := vp001000000010_0
theorem coverp001000000010 : Covers (-1027761639/2000000 : ℚ) vp001000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00100000001_0 : Blocks := edgeBlocks% "full/vectors/00100000001-V-0000.bin"
private noncomputable def vp00100000001_1 : Blocks := edgeBlocks% "full/vectors/00100000001-V-0001.bin"
noncomputable def vp00100000001 : Blocks := (Blocks.join vp00100000001_0 vp00100000001_1)
private theorem bp001000000010 : Branch 0 (-1027761639/4000000 : ℚ) vp00100000001 := by
  apply branch_left_normalized (c:=vp001000000010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1027761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1027761639/2000000 : ℚ) by norm_num]
  exact coverp001000000010
private noncomputable def ep001000000011_0 : Blocks := edgeBlocks% "full/vectors/001000000011-E-0000.bin"
private noncomputable def ep001000000011_1 : Blocks := edgeBlocks% "full/vectors/001000000011-E-0001.bin"
noncomputable def ep001000000011 : Blocks := (Blocks.join ep001000000011_0 ep001000000011_1)
private theorem idp001000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000001.list =
    C ((2:ℤ)^151) * horner X vp001000000011.list + horner X ep001000000011.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000000011 : Branch 1 (-1027761639/4000000 : ℚ) vp00100000001 := by
  apply branch_checked idp001000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1027761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1029761639/2000000 : ℚ) by norm_num]
  exact coverp001000000011
theorem coverp00100000001 : Covers (-1027761639/4000000 : ℚ) vp00100000001 := join_branches bp001000000010 bp001000000011
private noncomputable def vp001000000001_0 : Blocks := edgeBlocks% "full/vectors/001000000001-V-0000.bin"
noncomputable def vp001000000001 : Blocks := vp001000000001_0
theorem coverp001000000001 : Covers (-1025761639/2000000 : ℚ) vp001000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp001000000000_0 : Blocks := edgeBlocks% "full/vectors/001000000000-V-0000.bin"
noncomputable def vp001000000000 : Blocks := vp001000000000_0
theorem coverp001000000000 : Covers (-1023761639/2000000 : ℚ) vp001000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00100000000_0 : Blocks := edgeBlocks% "full/vectors/00100000000-V-0000.bin"
private noncomputable def vp00100000000_1 : Blocks := edgeBlocks% "full/vectors/00100000000-V-0001.bin"
noncomputable def vp00100000000 : Blocks := (Blocks.join vp00100000000_0 vp00100000000_1)
private theorem bp001000000000 : Branch 0 (-1023761639/4000000 : ℚ) vp00100000000 := by
  apply branch_left_normalized (c:=vp001000000000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1023761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/2000000 : ℚ) by norm_num]
  exact coverp001000000000
private noncomputable def ep001000000001_0 : Blocks := edgeBlocks% "full/vectors/001000000001-E-0000.bin"
private noncomputable def ep001000000001_1 : Blocks := edgeBlocks% "full/vectors/001000000001-E-0001.bin"
noncomputable def ep001000000001 : Blocks := (Blocks.join ep001000000001_0 ep001000000001_1)
private theorem idp001000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000000.list =
    C ((2:ℤ)^153) * horner X vp001000000001.list + horner X ep001000000001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000000001 : Branch 1 (-1023761639/4000000 : ℚ) vp00100000000 := by
  apply branch_checked idp001000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1025761639/2000000 : ℚ) by norm_num]
  exact coverp001000000001
theorem coverp00100000000 : Covers (-1023761639/4000000 : ℚ) vp00100000000 := join_branches bp001000000000 bp001000000001
private noncomputable def vp0010000000_0 : Blocks := edgeBlocks% "full/vectors/0010000000-V-0000.bin"
private noncomputable def vp0010000000_1 : Blocks := edgeBlocks% "full/vectors/0010000000-V-0001.bin"
private noncomputable def vp0010000000_2 : Blocks := edgeBlocks% "full/vectors/0010000000-V-0002.bin"
noncomputable def vp0010000000 : Blocks := (Blocks.join vp0010000000_0 (Blocks.join vp0010000000_1 vp0010000000_2))
private theorem bp00100000000 : Branch 0 (-1023761639/8000000 : ℚ) vp0010000000 := by
  apply branch_left_normalized (c:=vp00100000000) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-1023761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/4000000 : ℚ) by norm_num]
  exact coverp00100000000
private noncomputable def ep00100000001_0 : Blocks := edgeBlocks% "full/vectors/00100000001-E-0000.bin"
private noncomputable def ep00100000001_1 : Blocks := edgeBlocks% "full/vectors/00100000001-E-0001.bin"
private noncomputable def ep00100000001_2 : Blocks := edgeBlocks% "full/vectors/00100000001-E-0002.bin"
noncomputable def ep00100000001 : Blocks := (Blocks.join ep00100000001_0 (Blocks.join ep00100000001_1 ep00100000001_2))
private theorem idp00100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000000.list =
    C ((2:ℤ)^289) * horner X vp00100000001.list + horner X ep00100000001.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100000001 : Branch 1 (-1023761639/8000000 : ℚ) vp0010000000 := by
  apply branch_checked idp00100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1027761639/4000000 : ℚ) by norm_num]
  exact coverp00100000001
theorem coverp0010000000 : Covers (-1023761639/8000000 : ℚ) vp0010000000 := join_branches bp00100000000 bp00100000001
private noncomputable def vp001000000_0 : Blocks := edgeBlocks% "full/vectors/001000000-V-0000.bin"
private noncomputable def vp001000000_1 : Blocks := edgeBlocks% "full/vectors/001000000-V-0001.bin"
private noncomputable def vp001000000_2 : Blocks := edgeBlocks% "full/vectors/001000000-V-0002.bin"
private noncomputable def vp001000000_3 : Blocks := edgeBlocks% "full/vectors/001000000-V-0003.bin"
noncomputable def vp001000000 : Blocks := (Blocks.join (Blocks.join vp001000000_0 vp001000000_1) (Blocks.join vp001000000_2 vp001000000_3))
private theorem bp0010000000 : Branch 0 (-1023761639/16000000 : ℚ) vp001000000 := by
  apply branch_left_normalized (c:=vp0010000000) (k:=0) (m:=262) (by decide +kernel)
  rw [show 2*(-1023761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/8000000 : ℚ) by norm_num]
  exact coverp0010000000
private noncomputable def ep0010000001_0 : Blocks := edgeBlocks% "full/vectors/0010000001-E-0000.bin"
private noncomputable def ep0010000001_1 : Blocks := edgeBlocks% "full/vectors/0010000001-E-0001.bin"
private noncomputable def ep0010000001_2 : Blocks := edgeBlocks% "full/vectors/0010000001-E-0002.bin"
private noncomputable def ep0010000001_3 : Blocks := edgeBlocks% "full/vectors/0010000001-E-0003.bin"
noncomputable def ep0010000001 : Blocks := (Blocks.join (Blocks.join ep0010000001_0 ep0010000001_1) (Blocks.join ep0010000001_2 ep0010000001_3))
private theorem idp0010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000000.list =
    C ((2:ℤ)^557) * horner X vp0010000001.list + horner X ep0010000001.list := by
  exact edge_identity (B := (2:ℤ)^861) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010000001 : Branch 1 (-1023761639/16000000 : ℚ) vp001000000 := by
  apply branch_checked idp0010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1031761639/8000000 : ℚ) by norm_num]
  exact coverp0010000001
theorem coverp001000000 : Covers (-1023761639/16000000 : ℚ) vp001000000 := join_branches bp0010000000 bp0010000001
private noncomputable def vp00100000_0 : Blocks := edgeBlocks% "full/vectors/00100000-V-0000.bin"
private noncomputable def vp00100000_1 : Blocks := edgeBlocks% "full/vectors/00100000-V-0001.bin"
private noncomputable def vp00100000_2 : Blocks := edgeBlocks% "full/vectors/00100000-V-0002.bin"
private noncomputable def vp00100000_3 : Blocks := edgeBlocks% "full/vectors/00100000-V-0003.bin"
private noncomputable def vp00100000_4 : Blocks := edgeBlocks% "full/vectors/00100000-V-0004.bin"
private noncomputable def vp00100000_5 : Blocks := edgeBlocks% "full/vectors/00100000-V-0005.bin"
private noncomputable def vp00100000_6 : Blocks := edgeBlocks% "full/vectors/00100000-V-0006.bin"
private noncomputable def vp00100000_7 : Blocks := edgeBlocks% "full/vectors/00100000-V-0007.bin"
noncomputable def vp00100000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100000_0 vp00100000_1) (Blocks.join vp00100000_2 vp00100000_3)) (Blocks.join (Blocks.join vp00100000_4 vp00100000_5) (Blocks.join vp00100000_6 vp00100000_7)))
private theorem bp001000000 : Branch 0 (-1023761639/32000000 : ℚ) vp00100000 := by
  apply branch_left_normalized (c:=vp001000000) (k:=0) (m:=506) (by decide +kernel)
  rw [show 2*(-1023761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/16000000 : ℚ) by norm_num]
  exact coverp001000000
private noncomputable def ep001000001_0 : Blocks := edgeBlocks% "full/vectors/001000001-E-0000.bin"
private noncomputable def ep001000001_1 : Blocks := edgeBlocks% "full/vectors/001000001-E-0001.bin"
private noncomputable def ep001000001_2 : Blocks := edgeBlocks% "full/vectors/001000001-E-0002.bin"
private noncomputable def ep001000001_3 : Blocks := edgeBlocks% "full/vectors/001000001-E-0003.bin"
private noncomputable def ep001000001_4 : Blocks := edgeBlocks% "full/vectors/001000001-E-0004.bin"
private noncomputable def ep001000001_5 : Blocks := edgeBlocks% "full/vectors/001000001-E-0005.bin"
private noncomputable def ep001000001_6 : Blocks := edgeBlocks% "full/vectors/001000001-E-0006.bin"
private noncomputable def ep001000001_7 : Blocks := edgeBlocks% "full/vectors/001000001-E-0007.bin"
noncomputable def ep001000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001000001_0 ep001000001_1) (Blocks.join ep001000001_2 ep001000001_3)) (Blocks.join (Blocks.join ep001000001_4 ep001000001_5) (Blocks.join ep001000001_6 ep001000001_7)))
private theorem idp001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100000.list =
    C ((2:ℤ)^1082) * horner X vp001000001.list + horner X ep001000001.list := by
  exact edge_identity (B := (2:ℤ)^1600) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000001 : Branch 1 (-1023761639/32000000 : ℚ) vp00100000 := by
  apply branch_checked idp001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1039761639/16000000 : ℚ) by norm_num]
  exact coverp001000001
theorem coverp00100000 : Covers (-1023761639/32000000 : ℚ) vp00100000 := join_branches bp001000000 bp001000001
private noncomputable def vp0010000_0 : Blocks := edgeBlocks% "full/vectors/0010000-V-0000.bin"
private noncomputable def vp0010000_1 : Blocks := edgeBlocks% "full/vectors/0010000-V-0001.bin"
private noncomputable def vp0010000_2 : Blocks := edgeBlocks% "full/vectors/0010000-V-0002.bin"
private noncomputable def vp0010000_3 : Blocks := edgeBlocks% "full/vectors/0010000-V-0003.bin"
private noncomputable def vp0010000_4 : Blocks := edgeBlocks% "full/vectors/0010000-V-0004.bin"
private noncomputable def vp0010000_5 : Blocks := edgeBlocks% "full/vectors/0010000-V-0005.bin"
private noncomputable def vp0010000_6 : Blocks := edgeBlocks% "full/vectors/0010000-V-0006.bin"
private noncomputable def vp0010000_7 : Blocks := edgeBlocks% "full/vectors/0010000-V-0007.bin"
private noncomputable def vp0010000_8 : Blocks := edgeBlocks% "full/vectors/0010000-V-0008.bin"
private noncomputable def vp0010000_9 : Blocks := edgeBlocks% "full/vectors/0010000-V-0009.bin"
private noncomputable def vp0010000_10 : Blocks := edgeBlocks% "full/vectors/0010000-V-0010.bin"
private noncomputable def vp0010000_11 : Blocks := edgeBlocks% "full/vectors/0010000-V-0011.bin"
private noncomputable def vp0010000_12 : Blocks := edgeBlocks% "full/vectors/0010000-V-0012.bin"
private noncomputable def vp0010000_13 : Blocks := edgeBlocks% "full/vectors/0010000-V-0013.bin"
private noncomputable def vp0010000_14 : Blocks := edgeBlocks% "full/vectors/0010000-V-0014.bin"
private noncomputable def vp0010000_15 : Blocks := edgeBlocks% "full/vectors/0010000-V-0015.bin"
noncomputable def vp0010000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0010000_0 vp0010000_1) (Blocks.join vp0010000_2 vp0010000_3)) (Blocks.join (Blocks.join vp0010000_4 vp0010000_5) (Blocks.join vp0010000_6 vp0010000_7))) (Blocks.join (Blocks.join (Blocks.join vp0010000_8 vp0010000_9) (Blocks.join vp0010000_10 vp0010000_11)) (Blocks.join (Blocks.join vp0010000_12 vp0010000_13) (Blocks.join vp0010000_14 vp0010000_15))))
private theorem bp00100000 : Branch 0 (-1023761639/64000000 : ℚ) vp0010000 := by
  apply branch_left_normalized (c:=vp00100000) (k:=0) (m:=986) (by decide +kernel)
  rw [show 2*(-1023761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/32000000 : ℚ) by norm_num]
  exact coverp00100000
private noncomputable def ep00100001_0 : Blocks := edgeBlocks% "full/vectors/00100001-E-0000.bin"
private noncomputable def ep00100001_1 : Blocks := edgeBlocks% "full/vectors/00100001-E-0001.bin"
private noncomputable def ep00100001_2 : Blocks := edgeBlocks% "full/vectors/00100001-E-0002.bin"
private noncomputable def ep00100001_3 : Blocks := edgeBlocks% "full/vectors/00100001-E-0003.bin"
private noncomputable def ep00100001_4 : Blocks := edgeBlocks% "full/vectors/00100001-E-0004.bin"
private noncomputable def ep00100001_5 : Blocks := edgeBlocks% "full/vectors/00100001-E-0005.bin"
private noncomputable def ep00100001_6 : Blocks := edgeBlocks% "full/vectors/00100001-E-0006.bin"
private noncomputable def ep00100001_7 : Blocks := edgeBlocks% "full/vectors/00100001-E-0007.bin"
private noncomputable def ep00100001_8 : Blocks := edgeBlocks% "full/vectors/00100001-E-0008.bin"
private noncomputable def ep00100001_9 : Blocks := edgeBlocks% "full/vectors/00100001-E-0009.bin"
private noncomputable def ep00100001_10 : Blocks := edgeBlocks% "full/vectors/00100001-E-0010.bin"
private noncomputable def ep00100001_11 : Blocks := edgeBlocks% "full/vectors/00100001-E-0011.bin"
private noncomputable def ep00100001_12 : Blocks := edgeBlocks% "full/vectors/00100001-E-0012.bin"
private noncomputable def ep00100001_13 : Blocks := edgeBlocks% "full/vectors/00100001-E-0013.bin"
private noncomputable def ep00100001_14 : Blocks := edgeBlocks% "full/vectors/00100001-E-0014.bin"
private noncomputable def ep00100001_15 : Blocks := edgeBlocks% "full/vectors/00100001-E-0015.bin"
noncomputable def ep00100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00100001_0 ep00100001_1) (Blocks.join ep00100001_2 ep00100001_3)) (Blocks.join (Blocks.join ep00100001_4 ep00100001_5) (Blocks.join ep00100001_6 ep00100001_7))) (Blocks.join (Blocks.join (Blocks.join ep00100001_8 ep00100001_9) (Blocks.join ep00100001_10 ep00100001_11)) (Blocks.join (Blocks.join ep00100001_12 ep00100001_13) (Blocks.join ep00100001_14 ep00100001_15))))
private theorem idp00100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010000.list =
    C ((2:ℤ)^2109) * horner X vp00100001.list + horner X ep00100001.list := by
  exact edge_identity (B := (2:ℤ)^3054) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100001 : Branch 1 (-1023761639/64000000 : ℚ) vp0010000 := by
  apply branch_checked idp00100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1055761639/32000000 : ℚ) by norm_num]
  exact coverp00100001
theorem coverp0010000 : Covers (-1023761639/64000000 : ℚ) vp0010000 := join_branches bp00100000 bp00100001
private noncomputable def vp001000_0 : Blocks := edgeBlocks% "full/vectors/001000-V-0000.bin"
private noncomputable def vp001000_1 : Blocks := edgeBlocks% "full/vectors/001000-V-0001.bin"
private noncomputable def vp001000_2 : Blocks := edgeBlocks% "full/vectors/001000-V-0002.bin"
private noncomputable def vp001000_3 : Blocks := edgeBlocks% "full/vectors/001000-V-0003.bin"
private noncomputable def vp001000_4 : Blocks := edgeBlocks% "full/vectors/001000-V-0004.bin"
private noncomputable def vp001000_5 : Blocks := edgeBlocks% "full/vectors/001000-V-0005.bin"
private noncomputable def vp001000_6 : Blocks := edgeBlocks% "full/vectors/001000-V-0006.bin"
private noncomputable def vp001000_7 : Blocks := edgeBlocks% "full/vectors/001000-V-0007.bin"
private noncomputable def vp001000_8 : Blocks := edgeBlocks% "full/vectors/001000-V-0008.bin"
private noncomputable def vp001000_9 : Blocks := edgeBlocks% "full/vectors/001000-V-0009.bin"
private noncomputable def vp001000_10 : Blocks := edgeBlocks% "full/vectors/001000-V-0010.bin"
private noncomputable def vp001000_11 : Blocks := edgeBlocks% "full/vectors/001000-V-0011.bin"
private noncomputable def vp001000_12 : Blocks := edgeBlocks% "full/vectors/001000-V-0012.bin"
private noncomputable def vp001000_13 : Blocks := edgeBlocks% "full/vectors/001000-V-0013.bin"
private noncomputable def vp001000_14 : Blocks := edgeBlocks% "full/vectors/001000-V-0014.bin"
private noncomputable def vp001000_15 : Blocks := edgeBlocks% "full/vectors/001000-V-0015.bin"
private noncomputable def vp001000_16 : Blocks := edgeBlocks% "full/vectors/001000-V-0016.bin"
private noncomputable def vp001000_17 : Blocks := edgeBlocks% "full/vectors/001000-V-0017.bin"
private noncomputable def vp001000_18 : Blocks := edgeBlocks% "full/vectors/001000-V-0018.bin"
private noncomputable def vp001000_19 : Blocks := edgeBlocks% "full/vectors/001000-V-0019.bin"
private noncomputable def vp001000_20 : Blocks := edgeBlocks% "full/vectors/001000-V-0020.bin"
private noncomputable def vp001000_21 : Blocks := edgeBlocks% "full/vectors/001000-V-0021.bin"
private noncomputable def vp001000_22 : Blocks := edgeBlocks% "full/vectors/001000-V-0022.bin"
private noncomputable def vp001000_23 : Blocks := edgeBlocks% "full/vectors/001000-V-0023.bin"
private noncomputable def vp001000_24 : Blocks := edgeBlocks% "full/vectors/001000-V-0024.bin"
private noncomputable def vp001000_25 : Blocks := edgeBlocks% "full/vectors/001000-V-0025.bin"
private noncomputable def vp001000_26 : Blocks := edgeBlocks% "full/vectors/001000-V-0026.bin"
private noncomputable def vp001000_27 : Blocks := edgeBlocks% "full/vectors/001000-V-0027.bin"
private noncomputable def vp001000_28 : Blocks := edgeBlocks% "full/vectors/001000-V-0028.bin"
private noncomputable def vp001000_29 : Blocks := edgeBlocks% "full/vectors/001000-V-0029.bin"
noncomputable def vp001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001000_0 (Blocks.join vp001000_1 vp001000_2)) (Blocks.join (Blocks.join vp001000_3 vp001000_4) (Blocks.join vp001000_5 vp001000_6))) (Blocks.join (Blocks.join (Blocks.join vp001000_7 vp001000_8) (Blocks.join vp001000_9 vp001000_10)) (Blocks.join (Blocks.join vp001000_11 vp001000_12) (Blocks.join vp001000_13 vp001000_14)))) (Blocks.join (Blocks.join (Blocks.join vp001000_15 (Blocks.join vp001000_16 vp001000_17)) (Blocks.join (Blocks.join vp001000_18 vp001000_19) (Blocks.join vp001000_20 vp001000_21))) (Blocks.join (Blocks.join (Blocks.join vp001000_22 vp001000_23) (Blocks.join vp001000_24 vp001000_25)) (Blocks.join (Blocks.join vp001000_26 vp001000_27) (Blocks.join vp001000_28 vp001000_29)))))
private theorem bp0010000 : Branch 0 (-1023761639/128000000 : ℚ) vp001000 := by
  apply branch_left_normalized (c:=vp0010000) (k:=0) (m:=1926) (by decide +kernel)
  rw [show 2*(-1023761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/64000000 : ℚ) by norm_num]
  exact coverp0010000
private noncomputable def ep0010001_0 : Blocks := edgeBlocks% "full/vectors/0010001-E-0000.bin"
private noncomputable def ep0010001_1 : Blocks := edgeBlocks% "full/vectors/0010001-E-0001.bin"
private noncomputable def ep0010001_2 : Blocks := edgeBlocks% "full/vectors/0010001-E-0002.bin"
private noncomputable def ep0010001_3 : Blocks := edgeBlocks% "full/vectors/0010001-E-0003.bin"
private noncomputable def ep0010001_4 : Blocks := edgeBlocks% "full/vectors/0010001-E-0004.bin"
private noncomputable def ep0010001_5 : Blocks := edgeBlocks% "full/vectors/0010001-E-0005.bin"
private noncomputable def ep0010001_6 : Blocks := edgeBlocks% "full/vectors/0010001-E-0006.bin"
private noncomputable def ep0010001_7 : Blocks := edgeBlocks% "full/vectors/0010001-E-0007.bin"
private noncomputable def ep0010001_8 : Blocks := edgeBlocks% "full/vectors/0010001-E-0008.bin"
private noncomputable def ep0010001_9 : Blocks := edgeBlocks% "full/vectors/0010001-E-0009.bin"
private noncomputable def ep0010001_10 : Blocks := edgeBlocks% "full/vectors/0010001-E-0010.bin"
private noncomputable def ep0010001_11 : Blocks := edgeBlocks% "full/vectors/0010001-E-0011.bin"
private noncomputable def ep0010001_12 : Blocks := edgeBlocks% "full/vectors/0010001-E-0012.bin"
private noncomputable def ep0010001_13 : Blocks := edgeBlocks% "full/vectors/0010001-E-0013.bin"
private noncomputable def ep0010001_14 : Blocks := edgeBlocks% "full/vectors/0010001-E-0014.bin"
private noncomputable def ep0010001_15 : Blocks := edgeBlocks% "full/vectors/0010001-E-0015.bin"
private noncomputable def ep0010001_16 : Blocks := edgeBlocks% "full/vectors/0010001-E-0016.bin"
private noncomputable def ep0010001_17 : Blocks := edgeBlocks% "full/vectors/0010001-E-0017.bin"
private noncomputable def ep0010001_18 : Blocks := edgeBlocks% "full/vectors/0010001-E-0018.bin"
private noncomputable def ep0010001_19 : Blocks := edgeBlocks% "full/vectors/0010001-E-0019.bin"
private noncomputable def ep0010001_20 : Blocks := edgeBlocks% "full/vectors/0010001-E-0020.bin"
private noncomputable def ep0010001_21 : Blocks := edgeBlocks% "full/vectors/0010001-E-0021.bin"
private noncomputable def ep0010001_22 : Blocks := edgeBlocks% "full/vectors/0010001-E-0022.bin"
private noncomputable def ep0010001_23 : Blocks := edgeBlocks% "full/vectors/0010001-E-0023.bin"
private noncomputable def ep0010001_24 : Blocks := edgeBlocks% "full/vectors/0010001-E-0024.bin"
private noncomputable def ep0010001_25 : Blocks := edgeBlocks% "full/vectors/0010001-E-0025.bin"
private noncomputable def ep0010001_26 : Blocks := edgeBlocks% "full/vectors/0010001-E-0026.bin"
private noncomputable def ep0010001_27 : Blocks := edgeBlocks% "full/vectors/0010001-E-0027.bin"
private noncomputable def ep0010001_28 : Blocks := edgeBlocks% "full/vectors/0010001-E-0028.bin"
private noncomputable def ep0010001_29 : Blocks := edgeBlocks% "full/vectors/0010001-E-0029.bin"
noncomputable def ep0010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0010001_0 (Blocks.join ep0010001_1 ep0010001_2)) (Blocks.join (Blocks.join ep0010001_3 ep0010001_4) (Blocks.join ep0010001_5 ep0010001_6))) (Blocks.join (Blocks.join (Blocks.join ep0010001_7 ep0010001_8) (Blocks.join ep0010001_9 ep0010001_10)) (Blocks.join (Blocks.join ep0010001_11 ep0010001_12) (Blocks.join ep0010001_13 ep0010001_14)))) (Blocks.join (Blocks.join (Blocks.join ep0010001_15 (Blocks.join ep0010001_16 ep0010001_17)) (Blocks.join (Blocks.join ep0010001_18 ep0010001_19) (Blocks.join ep0010001_20 ep0010001_21))) (Blocks.join (Blocks.join (Blocks.join ep0010001_22 ep0010001_23) (Blocks.join ep0010001_24 ep0010001_25)) (Blocks.join (Blocks.join ep0010001_26 ep0010001_27) (Blocks.join ep0010001_28 ep0010001_29)))))
private def ptsp0010001 : List ℤ := [((2:ℤ)^3226+0),((2:ℤ)^3226+1)]
private theorem boundp0010001 : 2^vp001000.size*absSum vp001000.list + ((2:ℤ)^4080*absSum vp0010001.list+absSum ep0010001.list) < (2:ℤ)^5857 := by decide +kernel
private theorem pointp0010001_0 : fastHom 1 ((2:ℤ)^3226+0) vp001000 = ((2:ℤ)^4080)*vp0010001.subst ((2:ℤ)^3226+0)+ep0010001.subst ((2:ℤ)^3226+0) := by decide +kernel
private theorem pointp0010001_1 : fastHom 1 ((2:ℤ)^3226+1) vp001000 = ((2:ℤ)^4080)*vp0010001.subst ((2:ℤ)^3226+1)+ep0010001.subst ((2:ℤ)^3226+1) := by decide +kernel
private theorem checkp0010001 (x:ℤ) (hx:x ∈ ptsp0010001) : fastHom 1 x vp001000 = ((2:ℤ)^4080)*vp0010001.subst x+ep0010001.subst x := by
  simp only [ptsp0010001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0010001_0
  · exact pointp0010001_1
private theorem idp0010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000.list =
    C ((2:ℤ)^4080) * horner X vp0010001.list + horner X ep0010001.list := by
  apply edge_identity (B := (2:ℤ)^5857) (by decide) (by positivity) (by positivity) boundp0010001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0010001 (by decide +kernel)
  · have h : ptsp0010001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0010001.trans_le (by decide +kernel)
  · exact checkp0010001
private theorem bp0010001 : Branch 1 (-1023761639/128000000 : ℚ) vp001000 := by
  apply branch_checked idp0010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1087761639/64000000 : ℚ) by norm_num]
  exact coverp0010001
theorem coverp001000 : Covers (-1023761639/128000000 : ℚ) vp001000 := join_branches bp0010000 bp0010001
end NextProof.EdgeFull

