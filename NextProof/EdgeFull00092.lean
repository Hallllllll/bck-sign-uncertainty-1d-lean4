import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00091

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010100111111_0 : Blocks := edgeBlocks% "full/vectors/0010100111111-V-0000.bin"
noncomputable def vp0010100111111 : Blocks := vp0010100111111_0
theorem coverp0010100111111 : Covers (-1342761639/1000000 : ℚ) vp0010100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100111110_0 : Blocks := edgeBlocks% "full/vectors/0010100111110-V-0000.bin"
noncomputable def vp0010100111110 : Blocks := vp0010100111110_0
theorem coverp0010100111110 : Covers (-1341761639/1000000 : ℚ) vp0010100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011111_0 : Blocks := edgeBlocks% "full/vectors/001010011111-V-0000.bin"
noncomputable def vp001010011111 : Blocks := vp001010011111_0
private theorem bp0010100111110 : Branch 0 (-1341761639/2000000 : ℚ) vp001010011111 := by
  apply branch_left_normalized (c:=vp0010100111110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1341761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1341761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111110
private noncomputable def ep0010100111111_0 : Blocks := edgeBlocks% "full/vectors/0010100111111-E-0000.bin"
noncomputable def ep0010100111111 : Blocks := ep0010100111111_0
private theorem idp0010100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011111.list =
    C ((2:ℤ)^81) * horner X vp0010100111111.list + horner X ep0010100111111.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100111111 : Branch 1 (-1341761639/2000000 : ℚ) vp001010011111 := by
  apply branch_checked idp0010100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1341761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1342761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111111
theorem coverp001010011111 : Covers (-1341761639/2000000 : ℚ) vp001010011111 := join_branches bp0010100111110 bp0010100111111
private noncomputable def vp0010100111101_0 : Blocks := edgeBlocks% "full/vectors/0010100111101-V-0000.bin"
noncomputable def vp0010100111101 : Blocks := vp0010100111101_0
theorem coverp0010100111101 : Covers (-1340761639/1000000 : ℚ) vp0010100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100111100_0 : Blocks := edgeBlocks% "full/vectors/0010100111100-V-0000.bin"
noncomputable def vp0010100111100 : Blocks := vp0010100111100_0
theorem coverp0010100111100 : Covers (-1339761639/1000000 : ℚ) vp0010100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011110_0 : Blocks := edgeBlocks% "full/vectors/001010011110-V-0000.bin"
noncomputable def vp001010011110 : Blocks := vp001010011110_0
private theorem bp0010100111100 : Branch 0 (-1339761639/2000000 : ℚ) vp001010011110 := by
  apply branch_left_normalized (c:=vp0010100111100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1339761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1339761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111100
private noncomputable def ep0010100111101_0 : Blocks := edgeBlocks% "full/vectors/0010100111101-E-0000.bin"
noncomputable def ep0010100111101 : Blocks := ep0010100111101_0
private theorem idp0010100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011110.list =
    C ((2:ℤ)^81) * horner X vp0010100111101.list + horner X ep0010100111101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100111101 : Branch 1 (-1339761639/2000000 : ℚ) vp001010011110 := by
  apply branch_checked idp0010100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1339761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1340761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111101
theorem coverp001010011110 : Covers (-1339761639/2000000 : ℚ) vp001010011110 := join_branches bp0010100111100 bp0010100111101
private noncomputable def vp00101001111_0 : Blocks := edgeBlocks% "full/vectors/00101001111-V-0000.bin"
private noncomputable def vp00101001111_1 : Blocks := edgeBlocks% "full/vectors/00101001111-V-0001.bin"
noncomputable def vp00101001111 : Blocks := (Blocks.join vp00101001111_0 vp00101001111_1)
private theorem bp001010011110 : Branch 0 (-1339761639/4000000 : ℚ) vp00101001111 := by
  apply branch_left_normalized (c:=vp001010011110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1339761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1339761639/2000000 : ℚ) by norm_num]
  exact coverp001010011110
private noncomputable def ep001010011111_0 : Blocks := edgeBlocks% "full/vectors/001010011111-E-0000.bin"
private noncomputable def ep001010011111_1 : Blocks := edgeBlocks% "full/vectors/001010011111-E-0001.bin"
noncomputable def ep001010011111 : Blocks := (Blocks.join ep001010011111_0 ep001010011111_1)
private theorem idp001010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001111.list =
    C ((2:ℤ)^143) * horner X vp001010011111.list + horner X ep001010011111.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010011111 : Branch 1 (-1339761639/4000000 : ℚ) vp00101001111 := by
  apply branch_checked idp001010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1339761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1341761639/2000000 : ℚ) by norm_num]
  exact coverp001010011111
theorem coverp00101001111 : Covers (-1339761639/4000000 : ℚ) vp00101001111 := join_branches bp001010011110 bp001010011111
private noncomputable def vp0010100111011_0 : Blocks := edgeBlocks% "full/vectors/0010100111011-V-0000.bin"
noncomputable def vp0010100111011 : Blocks := vp0010100111011_0
theorem coverp0010100111011 : Covers (-1338761639/1000000 : ℚ) vp0010100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100111010_0 : Blocks := edgeBlocks% "full/vectors/0010100111010-V-0000.bin"
noncomputable def vp0010100111010 : Blocks := vp0010100111010_0
theorem coverp0010100111010 : Covers (-1337761639/1000000 : ℚ) vp0010100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011101_0 : Blocks := edgeBlocks% "full/vectors/001010011101-V-0000.bin"
noncomputable def vp001010011101 : Blocks := vp001010011101_0
private theorem bp0010100111010 : Branch 0 (-1337761639/2000000 : ℚ) vp001010011101 := by
  apply branch_left_normalized (c:=vp0010100111010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1337761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1337761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111010
private noncomputable def ep0010100111011_0 : Blocks := edgeBlocks% "full/vectors/0010100111011-E-0000.bin"
noncomputable def ep0010100111011 : Blocks := ep0010100111011_0
private theorem idp0010100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011101.list =
    C ((2:ℤ)^80) * horner X vp0010100111011.list + horner X ep0010100111011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100111011 : Branch 1 (-1337761639/2000000 : ℚ) vp001010011101 := by
  apply branch_checked idp0010100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1337761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1338761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111011
theorem coverp001010011101 : Covers (-1337761639/2000000 : ℚ) vp001010011101 := join_branches bp0010100111010 bp0010100111011
private noncomputable def vp0010100111001_0 : Blocks := edgeBlocks% "full/vectors/0010100111001-V-0000.bin"
noncomputable def vp0010100111001 : Blocks := vp0010100111001_0
theorem coverp0010100111001 : Covers (-1336761639/1000000 : ℚ) vp0010100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100111000_0 : Blocks := edgeBlocks% "full/vectors/0010100111000-V-0000.bin"
noncomputable def vp0010100111000 : Blocks := vp0010100111000_0
theorem coverp0010100111000 : Covers (-1335761639/1000000 : ℚ) vp0010100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011100_0 : Blocks := edgeBlocks% "full/vectors/001010011100-V-0000.bin"
noncomputable def vp001010011100 : Blocks := vp001010011100_0
private theorem bp0010100111000 : Branch 0 (-1335761639/2000000 : ℚ) vp001010011100 := by
  apply branch_left_normalized (c:=vp0010100111000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1335761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1335761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111000
private noncomputable def ep0010100111001_0 : Blocks := edgeBlocks% "full/vectors/0010100111001-E-0000.bin"
noncomputable def ep0010100111001 : Blocks := ep0010100111001_0
private theorem idp0010100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011100.list =
    C ((2:ℤ)^80) * horner X vp0010100111001.list + horner X ep0010100111001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100111001 : Branch 1 (-1335761639/2000000 : ℚ) vp001010011100 := by
  apply branch_checked idp0010100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1335761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1336761639/1000000 : ℚ) by norm_num]
  exact coverp0010100111001
theorem coverp001010011100 : Covers (-1335761639/2000000 : ℚ) vp001010011100 := join_branches bp0010100111000 bp0010100111001
private noncomputable def vp00101001110_0 : Blocks := edgeBlocks% "full/vectors/00101001110-V-0000.bin"
private noncomputable def vp00101001110_1 : Blocks := edgeBlocks% "full/vectors/00101001110-V-0001.bin"
noncomputable def vp00101001110 : Blocks := (Blocks.join vp00101001110_0 vp00101001110_1)
private theorem bp001010011100 : Branch 0 (-1335761639/4000000 : ℚ) vp00101001110 := by
  apply branch_left_normalized (c:=vp001010011100) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1335761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1335761639/2000000 : ℚ) by norm_num]
  exact coverp001010011100
private noncomputable def ep001010011101_0 : Blocks := edgeBlocks% "full/vectors/001010011101-E-0000.bin"
private noncomputable def ep001010011101_1 : Blocks := edgeBlocks% "full/vectors/001010011101-E-0001.bin"
noncomputable def ep001010011101 : Blocks := (Blocks.join ep001010011101_0 ep001010011101_1)
private theorem idp001010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001110.list =
    C ((2:ℤ)^142) * horner X vp001010011101.list + horner X ep001010011101.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010011101 : Branch 1 (-1335761639/4000000 : ℚ) vp00101001110 := by
  apply branch_checked idp001010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1335761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1337761639/2000000 : ℚ) by norm_num]
  exact coverp001010011101
theorem coverp00101001110 : Covers (-1335761639/4000000 : ℚ) vp00101001110 := join_branches bp001010011100 bp001010011101
private noncomputable def vp0010100111_0 : Blocks := edgeBlocks% "full/vectors/0010100111-V-0000.bin"
private noncomputable def vp0010100111_1 : Blocks := edgeBlocks% "full/vectors/0010100111-V-0001.bin"
noncomputable def vp0010100111 : Blocks := (Blocks.join vp0010100111_0 vp0010100111_1)
private theorem bp00101001110 : Branch 0 (-1335761639/8000000 : ℚ) vp0010100111 := by
  apply branch_left_normalized (c:=vp00101001110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-1335761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1335761639/4000000 : ℚ) by norm_num]
  exact coverp00101001110
private noncomputable def ep00101001111_0 : Blocks := edgeBlocks% "full/vectors/00101001111-E-0000.bin"
private noncomputable def ep00101001111_1 : Blocks := edgeBlocks% "full/vectors/00101001111-E-0001.bin"
noncomputable def ep00101001111 : Blocks := (Blocks.join ep00101001111_0 ep00101001111_1)
private theorem idp00101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100111.list =
    C ((2:ℤ)^261) * horner X vp00101001111.list + horner X ep00101001111.list := by
  exact edge_identity (B := (2:ℤ)^453) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101001111 : Branch 1 (-1335761639/8000000 : ℚ) vp0010100111 := by
  apply branch_checked idp00101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1335761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1339761639/4000000 : ℚ) by norm_num]
  exact coverp00101001111
theorem coverp0010100111 : Covers (-1335761639/8000000 : ℚ) vp0010100111 := join_branches bp00101001110 bp00101001111
private noncomputable def vp0010100110111_0 : Blocks := edgeBlocks% "full/vectors/0010100110111-V-0000.bin"
noncomputable def vp0010100110111 : Blocks := vp0010100110111_0
theorem coverp0010100110111 : Covers (-1334761639/1000000 : ℚ) vp0010100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100110110_0 : Blocks := edgeBlocks% "full/vectors/0010100110110-V-0000.bin"
noncomputable def vp0010100110110 : Blocks := vp0010100110110_0
theorem coverp0010100110110 : Covers (-1333761639/1000000 : ℚ) vp0010100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011011_0 : Blocks := edgeBlocks% "full/vectors/001010011011-V-0000.bin"
noncomputable def vp001010011011 : Blocks := vp001010011011_0
private theorem bp0010100110110 : Branch 0 (-1333761639/2000000 : ℚ) vp001010011011 := by
  apply branch_left_normalized (c:=vp0010100110110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1333761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1333761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110110
private noncomputable def ep0010100110111_0 : Blocks := edgeBlocks% "full/vectors/0010100110111-E-0000.bin"
noncomputable def ep0010100110111 : Blocks := ep0010100110111_0
private theorem idp0010100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011011.list =
    C ((2:ℤ)^81) * horner X vp0010100110111.list + horner X ep0010100110111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100110111 : Branch 1 (-1333761639/2000000 : ℚ) vp001010011011 := by
  apply branch_checked idp0010100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1333761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1334761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110111
theorem coverp001010011011 : Covers (-1333761639/2000000 : ℚ) vp001010011011 := join_branches bp0010100110110 bp0010100110111
private noncomputable def vp0010100110101_0 : Blocks := edgeBlocks% "full/vectors/0010100110101-V-0000.bin"
noncomputable def vp0010100110101 : Blocks := vp0010100110101_0
theorem coverp0010100110101 : Covers (-1332761639/1000000 : ℚ) vp0010100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100110100_0 : Blocks := edgeBlocks% "full/vectors/0010100110100-V-0000.bin"
noncomputable def vp0010100110100 : Blocks := vp0010100110100_0
theorem coverp0010100110100 : Covers (-1331761639/1000000 : ℚ) vp0010100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011010_0 : Blocks := edgeBlocks% "full/vectors/001010011010-V-0000.bin"
noncomputable def vp001010011010 : Blocks := vp001010011010_0
private theorem bp0010100110100 : Branch 0 (-1331761639/2000000 : ℚ) vp001010011010 := by
  apply branch_left_normalized (c:=vp0010100110100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1331761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1331761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110100
private noncomputable def ep0010100110101_0 : Blocks := edgeBlocks% "full/vectors/0010100110101-E-0000.bin"
noncomputable def ep0010100110101 : Blocks := ep0010100110101_0
private theorem idp0010100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011010.list =
    C ((2:ℤ)^80) * horner X vp0010100110101.list + horner X ep0010100110101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100110101 : Branch 1 (-1331761639/2000000 : ℚ) vp001010011010 := by
  apply branch_checked idp0010100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1331761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1332761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110101
theorem coverp001010011010 : Covers (-1331761639/2000000 : ℚ) vp001010011010 := join_branches bp0010100110100 bp0010100110101
private noncomputable def vp00101001101_0 : Blocks := edgeBlocks% "full/vectors/00101001101-V-0000.bin"
private noncomputable def vp00101001101_1 : Blocks := edgeBlocks% "full/vectors/00101001101-V-0001.bin"
noncomputable def vp00101001101 : Blocks := (Blocks.join vp00101001101_0 vp00101001101_1)
private theorem bp001010011010 : Branch 0 (-1331761639/4000000 : ℚ) vp00101001101 := by
  apply branch_left_normalized (c:=vp001010011010) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1331761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1331761639/2000000 : ℚ) by norm_num]
  exact coverp001010011010
private noncomputable def ep001010011011_0 : Blocks := edgeBlocks% "full/vectors/001010011011-E-0000.bin"
private noncomputable def ep001010011011_1 : Blocks := edgeBlocks% "full/vectors/001010011011-E-0001.bin"
noncomputable def ep001010011011 : Blocks := (Blocks.join ep001010011011_0 ep001010011011_1)
private theorem idp001010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001101.list =
    C ((2:ℤ)^141) * horner X vp001010011011.list + horner X ep001010011011.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010011011 : Branch 1 (-1331761639/4000000 : ℚ) vp00101001101 := by
  apply branch_checked idp001010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1331761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1333761639/2000000 : ℚ) by norm_num]
  exact coverp001010011011
theorem coverp00101001101 : Covers (-1331761639/4000000 : ℚ) vp00101001101 := join_branches bp001010011010 bp001010011011
private noncomputable def vp0010100110011_0 : Blocks := edgeBlocks% "full/vectors/0010100110011-V-0000.bin"
noncomputable def vp0010100110011 : Blocks := vp0010100110011_0
theorem coverp0010100110011 : Covers (-1330761639/1000000 : ℚ) vp0010100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100110010_0 : Blocks := edgeBlocks% "full/vectors/0010100110010-V-0000.bin"
noncomputable def vp0010100110010 : Blocks := vp0010100110010_0
theorem coverp0010100110010 : Covers (-1329761639/1000000 : ℚ) vp0010100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011001_0 : Blocks := edgeBlocks% "full/vectors/001010011001-V-0000.bin"
noncomputable def vp001010011001 : Blocks := vp001010011001_0
private theorem bp0010100110010 : Branch 0 (-1329761639/2000000 : ℚ) vp001010011001 := by
  apply branch_left_normalized (c:=vp0010100110010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1329761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1329761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110010
private noncomputable def ep0010100110011_0 : Blocks := edgeBlocks% "full/vectors/0010100110011-E-0000.bin"
noncomputable def ep0010100110011 : Blocks := ep0010100110011_0
private theorem idp0010100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011001.list =
    C ((2:ℤ)^81) * horner X vp0010100110011.list + horner X ep0010100110011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100110011 : Branch 1 (-1329761639/2000000 : ℚ) vp001010011001 := by
  apply branch_checked idp0010100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1329761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1330761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110011
theorem coverp001010011001 : Covers (-1329761639/2000000 : ℚ) vp001010011001 := join_branches bp0010100110010 bp0010100110011
private noncomputable def vp0010100110001_0 : Blocks := edgeBlocks% "full/vectors/0010100110001-V-0000.bin"
noncomputable def vp0010100110001 : Blocks := vp0010100110001_0
theorem coverp0010100110001 : Covers (-1328761639/1000000 : ℚ) vp0010100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100110000_0 : Blocks := edgeBlocks% "full/vectors/0010100110000-V-0000.bin"
noncomputable def vp0010100110000 : Blocks := vp0010100110000_0
theorem coverp0010100110000 : Covers (-1327761639/1000000 : ℚ) vp0010100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010011000_0 : Blocks := edgeBlocks% "full/vectors/001010011000-V-0000.bin"
noncomputable def vp001010011000 : Blocks := vp001010011000_0
private theorem bp0010100110000 : Branch 0 (-1327761639/2000000 : ℚ) vp001010011000 := by
  apply branch_left_normalized (c:=vp0010100110000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1327761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1327761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110000
private noncomputable def ep0010100110001_0 : Blocks := edgeBlocks% "full/vectors/0010100110001-E-0000.bin"
noncomputable def ep0010100110001 : Blocks := ep0010100110001_0
private theorem idp0010100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011000.list =
    C ((2:ℤ)^80) * horner X vp0010100110001.list + horner X ep0010100110001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100110001 : Branch 1 (-1327761639/2000000 : ℚ) vp001010011000 := by
  apply branch_checked idp0010100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1327761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1328761639/1000000 : ℚ) by norm_num]
  exact coverp0010100110001
theorem coverp001010011000 : Covers (-1327761639/2000000 : ℚ) vp001010011000 := join_branches bp0010100110000 bp0010100110001
private noncomputable def vp00101001100_0 : Blocks := edgeBlocks% "full/vectors/00101001100-V-0000.bin"
private noncomputable def vp00101001100_1 : Blocks := edgeBlocks% "full/vectors/00101001100-V-0001.bin"
noncomputable def vp00101001100 : Blocks := (Blocks.join vp00101001100_0 vp00101001100_1)
private theorem bp001010011000 : Branch 0 (-1327761639/4000000 : ℚ) vp00101001100 := by
  apply branch_left_normalized (c:=vp001010011000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1327761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1327761639/2000000 : ℚ) by norm_num]
  exact coverp001010011000
private noncomputable def ep001010011001_0 : Blocks := edgeBlocks% "full/vectors/001010011001-E-0000.bin"
private noncomputable def ep001010011001_1 : Blocks := edgeBlocks% "full/vectors/001010011001-E-0001.bin"
noncomputable def ep001010011001 : Blocks := (Blocks.join ep001010011001_0 ep001010011001_1)
private theorem idp001010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001100.list =
    C ((2:ℤ)^141) * horner X vp001010011001.list + horner X ep001010011001.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010011001 : Branch 1 (-1327761639/4000000 : ℚ) vp00101001100 := by
  apply branch_checked idp001010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1327761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1329761639/2000000 : ℚ) by norm_num]
  exact coverp001010011001
theorem coverp00101001100 : Covers (-1327761639/4000000 : ℚ) vp00101001100 := join_branches bp001010011000 bp001010011001
private noncomputable def vp0010100110_0 : Blocks := edgeBlocks% "full/vectors/0010100110-V-0000.bin"
private noncomputable def vp0010100110_1 : Blocks := edgeBlocks% "full/vectors/0010100110-V-0001.bin"
noncomputable def vp0010100110 : Blocks := (Blocks.join vp0010100110_0 vp0010100110_1)
private theorem bp00101001100 : Branch 0 (-1327761639/8000000 : ℚ) vp0010100110 := by
  apply branch_left_normalized (c:=vp00101001100) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-1327761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1327761639/4000000 : ℚ) by norm_num]
  exact coverp00101001100
private noncomputable def ep00101001101_0 : Blocks := edgeBlocks% "full/vectors/00101001101-E-0000.bin"
private noncomputable def ep00101001101_1 : Blocks := edgeBlocks% "full/vectors/00101001101-E-0001.bin"
noncomputable def ep00101001101 : Blocks := (Blocks.join ep00101001101_0 ep00101001101_1)
private theorem idp00101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100110.list =
    C ((2:ℤ)^262) * horner X vp00101001101.list + horner X ep00101001101.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101001101 : Branch 1 (-1327761639/8000000 : ℚ) vp0010100110 := by
  apply branch_checked idp00101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1327761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1331761639/4000000 : ℚ) by norm_num]
  exact coverp00101001101
theorem coverp0010100110 : Covers (-1327761639/8000000 : ℚ) vp0010100110 := join_branches bp00101001100 bp00101001101
private noncomputable def vp001010011_0 : Blocks := edgeBlocks% "full/vectors/001010011-V-0000.bin"
private noncomputable def vp001010011_1 : Blocks := edgeBlocks% "full/vectors/001010011-V-0001.bin"
private noncomputable def vp001010011_2 : Blocks := edgeBlocks% "full/vectors/001010011-V-0002.bin"
private noncomputable def vp001010011_3 : Blocks := edgeBlocks% "full/vectors/001010011-V-0003.bin"
noncomputable def vp001010011 : Blocks := (Blocks.join (Blocks.join vp001010011_0 vp001010011_1) (Blocks.join vp001010011_2 vp001010011_3))
private theorem bp0010100110 : Branch 0 (-1327761639/16000000 : ℚ) vp001010011 := by
  apply branch_left_normalized (c:=vp0010100110) (k:=0) (m:=238) (by decide +kernel)
  rw [show 2*(-1327761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1327761639/8000000 : ℚ) by norm_num]
  exact coverp0010100110
private noncomputable def ep0010100111_0 : Blocks := edgeBlocks% "full/vectors/0010100111-E-0000.bin"
private noncomputable def ep0010100111_1 : Blocks := edgeBlocks% "full/vectors/0010100111-E-0001.bin"
private noncomputable def ep0010100111_2 : Blocks := edgeBlocks% "full/vectors/0010100111-E-0002.bin"
private noncomputable def ep0010100111_3 : Blocks := edgeBlocks% "full/vectors/0010100111-E-0003.bin"
noncomputable def ep0010100111 : Blocks := (Blocks.join (Blocks.join ep0010100111_0 ep0010100111_1) (Blocks.join ep0010100111_2 ep0010100111_3))
private theorem idp0010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010011.list =
    C ((2:ℤ)^498) * horner X vp0010100111.list + horner X ep0010100111.list := by
  exact edge_identity (B := (2:ℤ)^782) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100111 : Branch 1 (-1327761639/16000000 : ℚ) vp001010011 := by
  apply branch_checked idp0010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1327761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1335761639/8000000 : ℚ) by norm_num]
  exact coverp0010100111
theorem coverp001010011 : Covers (-1327761639/16000000 : ℚ) vp001010011 := join_branches bp0010100110 bp0010100111
private noncomputable def vp0010100101111_0 : Blocks := edgeBlocks% "full/vectors/0010100101111-V-0000.bin"
noncomputable def vp0010100101111 : Blocks := vp0010100101111_0
theorem coverp0010100101111 : Covers (-1326761639/1000000 : ℚ) vp0010100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100101110_0 : Blocks := edgeBlocks% "full/vectors/0010100101110-V-0000.bin"
noncomputable def vp0010100101110 : Blocks := vp0010100101110_0
theorem coverp0010100101110 : Covers (-1325761639/1000000 : ℚ) vp0010100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010111_0 : Blocks := edgeBlocks% "full/vectors/001010010111-V-0000.bin"
noncomputable def vp001010010111 : Blocks := vp001010010111_0
private theorem bp0010100101110 : Branch 0 (-1325761639/2000000 : ℚ) vp001010010111 := by
  apply branch_left_normalized (c:=vp0010100101110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1325761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1325761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101110
private noncomputable def ep0010100101111_0 : Blocks := edgeBlocks% "full/vectors/0010100101111-E-0000.bin"
noncomputable def ep0010100101111 : Blocks := ep0010100101111_0
private theorem idp0010100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010111.list =
    C ((2:ℤ)^81) * horner X vp0010100101111.list + horner X ep0010100101111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100101111 : Branch 1 (-1325761639/2000000 : ℚ) vp001010010111 := by
  apply branch_checked idp0010100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1325761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1326761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101111
theorem coverp001010010111 : Covers (-1325761639/2000000 : ℚ) vp001010010111 := join_branches bp0010100101110 bp0010100101111
private noncomputable def vp0010100101101_0 : Blocks := edgeBlocks% "full/vectors/0010100101101-V-0000.bin"
noncomputable def vp0010100101101 : Blocks := vp0010100101101_0
theorem coverp0010100101101 : Covers (-1324761639/1000000 : ℚ) vp0010100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100101100_0 : Blocks := edgeBlocks% "full/vectors/0010100101100-V-0000.bin"
noncomputable def vp0010100101100 : Blocks := vp0010100101100_0
theorem coverp0010100101100 : Covers (-1323761639/1000000 : ℚ) vp0010100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010110_0 : Blocks := edgeBlocks% "full/vectors/001010010110-V-0000.bin"
noncomputable def vp001010010110 : Blocks := vp001010010110_0
private theorem bp0010100101100 : Branch 0 (-1323761639/2000000 : ℚ) vp001010010110 := by
  apply branch_left_normalized (c:=vp0010100101100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1323761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1323761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101100
private noncomputable def ep0010100101101_0 : Blocks := edgeBlocks% "full/vectors/0010100101101-E-0000.bin"
noncomputable def ep0010100101101 : Blocks := ep0010100101101_0
private theorem idp0010100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010110.list =
    C ((2:ℤ)^81) * horner X vp0010100101101.list + horner X ep0010100101101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100101101 : Branch 1 (-1323761639/2000000 : ℚ) vp001010010110 := by
  apply branch_checked idp0010100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1323761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1324761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101101
theorem coverp001010010110 : Covers (-1323761639/2000000 : ℚ) vp001010010110 := join_branches bp0010100101100 bp0010100101101
private noncomputable def vp00101001011_0 : Blocks := edgeBlocks% "full/vectors/00101001011-V-0000.bin"
private noncomputable def vp00101001011_1 : Blocks := edgeBlocks% "full/vectors/00101001011-V-0001.bin"
noncomputable def vp00101001011 : Blocks := (Blocks.join vp00101001011_0 vp00101001011_1)
private theorem bp001010010110 : Branch 0 (-1323761639/4000000 : ℚ) vp00101001011 := by
  apply branch_left_normalized (c:=vp001010010110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1323761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1323761639/2000000 : ℚ) by norm_num]
  exact coverp001010010110
private noncomputable def ep001010010111_0 : Blocks := edgeBlocks% "full/vectors/001010010111-E-0000.bin"
private noncomputable def ep001010010111_1 : Blocks := edgeBlocks% "full/vectors/001010010111-E-0001.bin"
noncomputable def ep001010010111 : Blocks := (Blocks.join ep001010010111_0 ep001010010111_1)
private theorem idp001010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001011.list =
    C ((2:ℤ)^142) * horner X vp001010010111.list + horner X ep001010010111.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010010111 : Branch 1 (-1323761639/4000000 : ℚ) vp00101001011 := by
  apply branch_checked idp001010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1323761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1325761639/2000000 : ℚ) by norm_num]
  exact coverp001010010111
theorem coverp00101001011 : Covers (-1323761639/4000000 : ℚ) vp00101001011 := join_branches bp001010010110 bp001010010111
private noncomputable def vp0010100101011_0 : Blocks := edgeBlocks% "full/vectors/0010100101011-V-0000.bin"
noncomputable def vp0010100101011 : Blocks := vp0010100101011_0
theorem coverp0010100101011 : Covers (-1322761639/1000000 : ℚ) vp0010100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100101010_0 : Blocks := edgeBlocks% "full/vectors/0010100101010-V-0000.bin"
noncomputable def vp0010100101010 : Blocks := vp0010100101010_0
theorem coverp0010100101010 : Covers (-1321761639/1000000 : ℚ) vp0010100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010101_0 : Blocks := edgeBlocks% "full/vectors/001010010101-V-0000.bin"
noncomputable def vp001010010101 : Blocks := vp001010010101_0
private theorem bp0010100101010 : Branch 0 (-1321761639/2000000 : ℚ) vp001010010101 := by
  apply branch_left_normalized (c:=vp0010100101010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1321761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1321761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101010
private noncomputable def ep0010100101011_0 : Blocks := edgeBlocks% "full/vectors/0010100101011-E-0000.bin"
noncomputable def ep0010100101011 : Blocks := ep0010100101011_0
private theorem idp0010100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010101.list =
    C ((2:ℤ)^81) * horner X vp0010100101011.list + horner X ep0010100101011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100101011 : Branch 1 (-1321761639/2000000 : ℚ) vp001010010101 := by
  apply branch_checked idp0010100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1321761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1322761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101011
theorem coverp001010010101 : Covers (-1321761639/2000000 : ℚ) vp001010010101 := join_branches bp0010100101010 bp0010100101011
private noncomputable def vp0010100101001_0 : Blocks := edgeBlocks% "full/vectors/0010100101001-V-0000.bin"
noncomputable def vp0010100101001 : Blocks := vp0010100101001_0
theorem coverp0010100101001 : Covers (-1320761639/1000000 : ℚ) vp0010100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100101000_0 : Blocks := edgeBlocks% "full/vectors/0010100101000-V-0000.bin"
noncomputable def vp0010100101000 : Blocks := vp0010100101000_0
theorem coverp0010100101000 : Covers (-1319761639/1000000 : ℚ) vp0010100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010100_0 : Blocks := edgeBlocks% "full/vectors/001010010100-V-0000.bin"
noncomputable def vp001010010100 : Blocks := vp001010010100_0
private theorem bp0010100101000 : Branch 0 (-1319761639/2000000 : ℚ) vp001010010100 := by
  apply branch_left_normalized (c:=vp0010100101000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1319761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1319761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101000
private noncomputable def ep0010100101001_0 : Blocks := edgeBlocks% "full/vectors/0010100101001-E-0000.bin"
noncomputable def ep0010100101001 : Blocks := ep0010100101001_0
private theorem idp0010100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010100.list =
    C ((2:ℤ)^81) * horner X vp0010100101001.list + horner X ep0010100101001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100101001 : Branch 1 (-1319761639/2000000 : ℚ) vp001010010100 := by
  apply branch_checked idp0010100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1319761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1320761639/1000000 : ℚ) by norm_num]
  exact coverp0010100101001
theorem coverp001010010100 : Covers (-1319761639/2000000 : ℚ) vp001010010100 := join_branches bp0010100101000 bp0010100101001
private noncomputable def vp00101001010_0 : Blocks := edgeBlocks% "full/vectors/00101001010-V-0000.bin"
private noncomputable def vp00101001010_1 : Blocks := edgeBlocks% "full/vectors/00101001010-V-0001.bin"
noncomputable def vp00101001010 : Blocks := (Blocks.join vp00101001010_0 vp00101001010_1)
private theorem bp001010010100 : Branch 0 (-1319761639/4000000 : ℚ) vp00101001010 := by
  apply branch_left_normalized (c:=vp001010010100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1319761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1319761639/2000000 : ℚ) by norm_num]
  exact coverp001010010100
private noncomputable def ep001010010101_0 : Blocks := edgeBlocks% "full/vectors/001010010101-E-0000.bin"
private noncomputable def ep001010010101_1 : Blocks := edgeBlocks% "full/vectors/001010010101-E-0001.bin"
noncomputable def ep001010010101 : Blocks := (Blocks.join ep001010010101_0 ep001010010101_1)
private theorem idp001010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001010.list =
    C ((2:ℤ)^143) * horner X vp001010010101.list + horner X ep001010010101.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010010101 : Branch 1 (-1319761639/4000000 : ℚ) vp00101001010 := by
  apply branch_checked idp001010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1319761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1321761639/2000000 : ℚ) by norm_num]
  exact coverp001010010101
theorem coverp00101001010 : Covers (-1319761639/4000000 : ℚ) vp00101001010 := join_branches bp001010010100 bp001010010101
private noncomputable def vp0010100101_0 : Blocks := edgeBlocks% "full/vectors/0010100101-V-0000.bin"
private noncomputable def vp0010100101_1 : Blocks := edgeBlocks% "full/vectors/0010100101-V-0001.bin"
noncomputable def vp0010100101 : Blocks := (Blocks.join vp0010100101_0 vp0010100101_1)
private theorem bp00101001010 : Branch 0 (-1319761639/8000000 : ℚ) vp0010100101 := by
  apply branch_left_normalized (c:=vp00101001010) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-1319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1319761639/4000000 : ℚ) by norm_num]
  exact coverp00101001010
private noncomputable def ep00101001011_0 : Blocks := edgeBlocks% "full/vectors/00101001011-E-0000.bin"
private noncomputable def ep00101001011_1 : Blocks := edgeBlocks% "full/vectors/00101001011-E-0001.bin"
noncomputable def ep00101001011 : Blocks := (Blocks.join ep00101001011_0 ep00101001011_1)
private theorem idp00101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100101.list =
    C ((2:ℤ)^262) * horner X vp00101001011.list + horner X ep00101001011.list := by
  exact edge_identity (B := (2:ℤ)^456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101001011 : Branch 1 (-1319761639/8000000 : ℚ) vp0010100101 := by
  apply branch_checked idp00101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1323761639/4000000 : ℚ) by norm_num]
  exact coverp00101001011
theorem coverp0010100101 : Covers (-1319761639/8000000 : ℚ) vp0010100101 := join_branches bp00101001010 bp00101001011
private noncomputable def vp0010100100111_0 : Blocks := edgeBlocks% "full/vectors/0010100100111-V-0000.bin"
noncomputable def vp0010100100111 : Blocks := vp0010100100111_0
theorem coverp0010100100111 : Covers (-1318761639/1000000 : ℚ) vp0010100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100100110_0 : Blocks := edgeBlocks% "full/vectors/0010100100110-V-0000.bin"
noncomputable def vp0010100100110 : Blocks := vp0010100100110_0
theorem coverp0010100100110 : Covers (-1317761639/1000000 : ℚ) vp0010100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010011_0 : Blocks := edgeBlocks% "full/vectors/001010010011-V-0000.bin"
noncomputable def vp001010010011 : Blocks := vp001010010011_0
private theorem bp0010100100110 : Branch 0 (-1317761639/2000000 : ℚ) vp001010010011 := by
  apply branch_left_normalized (c:=vp0010100100110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1317761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1317761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100110
private noncomputable def ep0010100100111_0 : Blocks := edgeBlocks% "full/vectors/0010100100111-E-0000.bin"
noncomputable def ep0010100100111 : Blocks := ep0010100100111_0
private theorem idp0010100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010011.list =
    C ((2:ℤ)^82) * horner X vp0010100100111.list + horner X ep0010100100111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100100111 : Branch 1 (-1317761639/2000000 : ℚ) vp001010010011 := by
  apply branch_checked idp0010100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1317761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1318761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100111
theorem coverp001010010011 : Covers (-1317761639/2000000 : ℚ) vp001010010011 := join_branches bp0010100100110 bp0010100100111
private noncomputable def vp0010100100101_0 : Blocks := edgeBlocks% "full/vectors/0010100100101-V-0000.bin"
noncomputable def vp0010100100101 : Blocks := vp0010100100101_0
theorem coverp0010100100101 : Covers (-1316761639/1000000 : ℚ) vp0010100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100100100_0 : Blocks := edgeBlocks% "full/vectors/0010100100100-V-0000.bin"
noncomputable def vp0010100100100 : Blocks := vp0010100100100_0
theorem coverp0010100100100 : Covers (-1315761639/1000000 : ℚ) vp0010100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010010_0 : Blocks := edgeBlocks% "full/vectors/001010010010-V-0000.bin"
noncomputable def vp001010010010 : Blocks := vp001010010010_0
private theorem bp0010100100100 : Branch 0 (-1315761639/2000000 : ℚ) vp001010010010 := by
  apply branch_left_normalized (c:=vp0010100100100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1315761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1315761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100100
private noncomputable def ep0010100100101_0 : Blocks := edgeBlocks% "full/vectors/0010100100101-E-0000.bin"
noncomputable def ep0010100100101 : Blocks := ep0010100100101_0
private theorem idp0010100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010010.list =
    C ((2:ℤ)^82) * horner X vp0010100100101.list + horner X ep0010100100101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100100101 : Branch 1 (-1315761639/2000000 : ℚ) vp001010010010 := by
  apply branch_checked idp0010100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1315761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1316761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100101
theorem coverp001010010010 : Covers (-1315761639/2000000 : ℚ) vp001010010010 := join_branches bp0010100100100 bp0010100100101
private noncomputable def vp00101001001_0 : Blocks := edgeBlocks% "full/vectors/00101001001-V-0000.bin"
private noncomputable def vp00101001001_1 : Blocks := edgeBlocks% "full/vectors/00101001001-V-0001.bin"
noncomputable def vp00101001001 : Blocks := (Blocks.join vp00101001001_0 vp00101001001_1)
private theorem bp001010010010 : Branch 0 (-1315761639/4000000 : ℚ) vp00101001001 := by
  apply branch_left_normalized (c:=vp001010010010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1315761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1315761639/2000000 : ℚ) by norm_num]
  exact coverp001010010010
private noncomputable def ep001010010011_0 : Blocks := edgeBlocks% "full/vectors/001010010011-E-0000.bin"
private noncomputable def ep001010010011_1 : Blocks := edgeBlocks% "full/vectors/001010010011-E-0001.bin"
noncomputable def ep001010010011 : Blocks := (Blocks.join ep001010010011_0 ep001010010011_1)
private theorem idp001010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001001.list =
    C ((2:ℤ)^143) * horner X vp001010010011.list + horner X ep001010010011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010010011 : Branch 1 (-1315761639/4000000 : ℚ) vp00101001001 := by
  apply branch_checked idp001010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1315761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1317761639/2000000 : ℚ) by norm_num]
  exact coverp001010010011
theorem coverp00101001001 : Covers (-1315761639/4000000 : ℚ) vp00101001001 := join_branches bp001010010010 bp001010010011
private noncomputable def vp0010100100011_0 : Blocks := edgeBlocks% "full/vectors/0010100100011-V-0000.bin"
noncomputable def vp0010100100011 : Blocks := vp0010100100011_0
theorem coverp0010100100011 : Covers (-1314761639/1000000 : ℚ) vp0010100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100100010_0 : Blocks := edgeBlocks% "full/vectors/0010100100010-V-0000.bin"
noncomputable def vp0010100100010 : Blocks := vp0010100100010_0
theorem coverp0010100100010 : Covers (-1313761639/1000000 : ℚ) vp0010100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010001_0 : Blocks := edgeBlocks% "full/vectors/001010010001-V-0000.bin"
noncomputable def vp001010010001 : Blocks := vp001010010001_0
private theorem bp0010100100010 : Branch 0 (-1313761639/2000000 : ℚ) vp001010010001 := by
  apply branch_left_normalized (c:=vp0010100100010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1313761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1313761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100010
private noncomputable def ep0010100100011_0 : Blocks := edgeBlocks% "full/vectors/0010100100011-E-0000.bin"
noncomputable def ep0010100100011 : Blocks := ep0010100100011_0
private theorem idp0010100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010001.list =
    C ((2:ℤ)^82) * horner X vp0010100100011.list + horner X ep0010100100011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100100011 : Branch 1 (-1313761639/2000000 : ℚ) vp001010010001 := by
  apply branch_checked idp0010100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1313761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1314761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100011
theorem coverp001010010001 : Covers (-1313761639/2000000 : ℚ) vp001010010001 := join_branches bp0010100100010 bp0010100100011
private noncomputable def vp0010100100001_0 : Blocks := edgeBlocks% "full/vectors/0010100100001-V-0000.bin"
noncomputable def vp0010100100001 : Blocks := vp0010100100001_0
theorem coverp0010100100001 : Covers (-1312761639/1000000 : ℚ) vp0010100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100100000_0 : Blocks := edgeBlocks% "full/vectors/0010100100000-V-0000.bin"
noncomputable def vp0010100100000 : Blocks := vp0010100100000_0
theorem coverp0010100100000 : Covers (-1311761639/1000000 : ℚ) vp0010100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010010000_0 : Blocks := edgeBlocks% "full/vectors/001010010000-V-0000.bin"
noncomputable def vp001010010000 : Blocks := vp001010010000_0
private theorem bp0010100100000 : Branch 0 (-1311761639/2000000 : ℚ) vp001010010000 := by
  apply branch_left_normalized (c:=vp0010100100000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1311761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1311761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100000
private noncomputable def ep0010100100001_0 : Blocks := edgeBlocks% "full/vectors/0010100100001-E-0000.bin"
noncomputable def ep0010100100001 : Blocks := ep0010100100001_0
private theorem idp0010100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010000.list =
    C ((2:ℤ)^82) * horner X vp0010100100001.list + horner X ep0010100100001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100100001 : Branch 1 (-1311761639/2000000 : ℚ) vp001010010000 := by
  apply branch_checked idp0010100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1311761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1312761639/1000000 : ℚ) by norm_num]
  exact coverp0010100100001
theorem coverp001010010000 : Covers (-1311761639/2000000 : ℚ) vp001010010000 := join_branches bp0010100100000 bp0010100100001
private noncomputable def vp00101001000_0 : Blocks := edgeBlocks% "full/vectors/00101001000-V-0000.bin"
private noncomputable def vp00101001000_1 : Blocks := edgeBlocks% "full/vectors/00101001000-V-0001.bin"
noncomputable def vp00101001000 : Blocks := (Blocks.join vp00101001000_0 vp00101001000_1)
private theorem bp001010010000 : Branch 0 (-1311761639/4000000 : ℚ) vp00101001000 := by
  apply branch_left_normalized (c:=vp001010010000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1311761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1311761639/2000000 : ℚ) by norm_num]
  exact coverp001010010000
private noncomputable def ep001010010001_0 : Blocks := edgeBlocks% "full/vectors/001010010001-E-0000.bin"
private noncomputable def ep001010010001_1 : Blocks := edgeBlocks% "full/vectors/001010010001-E-0001.bin"
noncomputable def ep001010010001 : Blocks := (Blocks.join ep001010010001_0 ep001010010001_1)
private theorem idp001010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001000.list =
    C ((2:ℤ)^143) * horner X vp001010010001.list + horner X ep001010010001.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010010001 : Branch 1 (-1311761639/4000000 : ℚ) vp00101001000 := by
  apply branch_checked idp001010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1311761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1313761639/2000000 : ℚ) by norm_num]
  exact coverp001010010001
theorem coverp00101001000 : Covers (-1311761639/4000000 : ℚ) vp00101001000 := join_branches bp001010010000 bp001010010001
private noncomputable def vp0010100100_0 : Blocks := edgeBlocks% "full/vectors/0010100100-V-0000.bin"
private noncomputable def vp0010100100_1 : Blocks := edgeBlocks% "full/vectors/0010100100-V-0001.bin"
noncomputable def vp0010100100 : Blocks := (Blocks.join vp0010100100_0 vp0010100100_1)
private theorem bp00101001000 : Branch 0 (-1311761639/8000000 : ℚ) vp0010100100 := by
  apply branch_left_normalized (c:=vp00101001000) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-1311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1311761639/4000000 : ℚ) by norm_num]
  exact coverp00101001000
private noncomputable def ep00101001001_0 : Blocks := edgeBlocks% "full/vectors/00101001001-E-0000.bin"
private noncomputable def ep00101001001_1 : Blocks := edgeBlocks% "full/vectors/00101001001-E-0001.bin"
noncomputable def ep00101001001 : Blocks := (Blocks.join ep00101001001_0 ep00101001001_1)
private theorem idp00101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100100.list =
    C ((2:ℤ)^263) * horner X vp00101001001.list + horner X ep00101001001.list := by
  exact edge_identity (B := (2:ℤ)^457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101001001 : Branch 1 (-1311761639/8000000 : ℚ) vp0010100100 := by
  apply branch_checked idp00101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1315761639/4000000 : ℚ) by norm_num]
  exact coverp00101001001
theorem coverp0010100100 : Covers (-1311761639/8000000 : ℚ) vp0010100100 := join_branches bp00101001000 bp00101001001
private noncomputable def vp001010010_0 : Blocks := edgeBlocks% "full/vectors/001010010-V-0000.bin"
private noncomputable def vp001010010_1 : Blocks := edgeBlocks% "full/vectors/001010010-V-0001.bin"
private noncomputable def vp001010010_2 : Blocks := edgeBlocks% "full/vectors/001010010-V-0002.bin"
private noncomputable def vp001010010_3 : Blocks := edgeBlocks% "full/vectors/001010010-V-0003.bin"
noncomputable def vp001010010 : Blocks := (Blocks.join (Blocks.join vp001010010_0 vp001010010_1) (Blocks.join vp001010010_2 vp001010010_3))
private theorem bp0010100100 : Branch 0 (-1311761639/16000000 : ℚ) vp001010010 := by
  apply branch_left_normalized (c:=vp0010100100) (k:=0) (m:=239) (by decide +kernel)
  rw [show 2*(-1311761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1311761639/8000000 : ℚ) by norm_num]
  exact coverp0010100100
private noncomputable def ep0010100101_0 : Blocks := edgeBlocks% "full/vectors/0010100101-E-0000.bin"
private noncomputable def ep0010100101_1 : Blocks := edgeBlocks% "full/vectors/0010100101-E-0001.bin"
private noncomputable def ep0010100101_2 : Blocks := edgeBlocks% "full/vectors/0010100101-E-0002.bin"
private noncomputable def ep0010100101_3 : Blocks := edgeBlocks% "full/vectors/0010100101-E-0003.bin"
noncomputable def ep0010100101 : Blocks := (Blocks.join (Blocks.join ep0010100101_0 ep0010100101_1) (Blocks.join ep0010100101_2 ep0010100101_3))
private theorem idp0010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010010.list =
    C ((2:ℤ)^501) * horner X vp0010100101.list + horner X ep0010100101.list := by
  exact edge_identity (B := (2:ℤ)^787) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100101 : Branch 1 (-1311761639/16000000 : ℚ) vp001010010 := by
  apply branch_checked idp0010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1311761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1319761639/8000000 : ℚ) by norm_num]
  exact coverp0010100101
theorem coverp001010010 : Covers (-1311761639/16000000 : ℚ) vp001010010 := join_branches bp0010100100 bp0010100101
private noncomputable def vp00101001_0 : Blocks := edgeBlocks% "full/vectors/00101001-V-0000.bin"
private noncomputable def vp00101001_1 : Blocks := edgeBlocks% "full/vectors/00101001-V-0001.bin"
private noncomputable def vp00101001_2 : Blocks := edgeBlocks% "full/vectors/00101001-V-0002.bin"
private noncomputable def vp00101001_3 : Blocks := edgeBlocks% "full/vectors/00101001-V-0003.bin"
private noncomputable def vp00101001_4 : Blocks := edgeBlocks% "full/vectors/00101001-V-0004.bin"
private noncomputable def vp00101001_5 : Blocks := edgeBlocks% "full/vectors/00101001-V-0005.bin"
private noncomputable def vp00101001_6 : Blocks := edgeBlocks% "full/vectors/00101001-V-0006.bin"
noncomputable def vp00101001 : Blocks := (Blocks.join (Blocks.join vp00101001_0 (Blocks.join vp00101001_1 vp00101001_2)) (Blocks.join (Blocks.join vp00101001_3 vp00101001_4) (Blocks.join vp00101001_5 vp00101001_6)))
private theorem bp001010010 : Branch 0 (-1311761639/32000000 : ℚ) vp00101001 := by
  apply branch_left_normalized (c:=vp001010010) (k:=0) (m:=454) (by decide +kernel)
  rw [show 2*(-1311761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1311761639/16000000 : ℚ) by norm_num]
  exact coverp001010010
private noncomputable def ep001010011_0 : Blocks := edgeBlocks% "full/vectors/001010011-E-0000.bin"
private noncomputable def ep001010011_1 : Blocks := edgeBlocks% "full/vectors/001010011-E-0001.bin"
private noncomputable def ep001010011_2 : Blocks := edgeBlocks% "full/vectors/001010011-E-0002.bin"
private noncomputable def ep001010011_3 : Blocks := edgeBlocks% "full/vectors/001010011-E-0003.bin"
private noncomputable def ep001010011_4 : Blocks := edgeBlocks% "full/vectors/001010011-E-0004.bin"
private noncomputable def ep001010011_5 : Blocks := edgeBlocks% "full/vectors/001010011-E-0005.bin"
private noncomputable def ep001010011_6 : Blocks := edgeBlocks% "full/vectors/001010011-E-0006.bin"
noncomputable def ep001010011 : Blocks := (Blocks.join (Blocks.join ep001010011_0 (Blocks.join ep001010011_1 ep001010011_2)) (Blocks.join (Blocks.join ep001010011_3 ep001010011_4) (Blocks.join ep001010011_5 ep001010011_6)))
private theorem idp001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101001.list =
    C ((2:ℤ)^974) * horner X vp001010011.list + horner X ep001010011.list := by
  exact edge_identity (B := (2:ℤ)^1442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010011 : Branch 1 (-1311761639/32000000 : ℚ) vp00101001 := by
  apply branch_checked idp001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1311761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1327761639/16000000 : ℚ) by norm_num]
  exact coverp001010011
theorem coverp00101001 : Covers (-1311761639/32000000 : ℚ) vp00101001 := join_branches bp001010010 bp001010011
private noncomputable def vp0010100011111_0 : Blocks := edgeBlocks% "full/vectors/0010100011111-V-0000.bin"
noncomputable def vp0010100011111 : Blocks := vp0010100011111_0
theorem coverp0010100011111 : Covers (-1310761639/1000000 : ℚ) vp0010100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100011110_0 : Blocks := edgeBlocks% "full/vectors/0010100011110-V-0000.bin"
noncomputable def vp0010100011110 : Blocks := vp0010100011110_0
theorem coverp0010100011110 : Covers (-1309761639/1000000 : ℚ) vp0010100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001111_0 : Blocks := edgeBlocks% "full/vectors/001010001111-V-0000.bin"
noncomputable def vp001010001111 : Blocks := vp001010001111_0
private theorem bp0010100011110 : Branch 0 (-1309761639/2000000 : ℚ) vp001010001111 := by
  apply branch_left_normalized (c:=vp0010100011110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1309761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1309761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011110
private noncomputable def ep0010100011111_0 : Blocks := edgeBlocks% "full/vectors/0010100011111-E-0000.bin"
noncomputable def ep0010100011111 : Blocks := ep0010100011111_0
private theorem idp0010100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001111.list =
    C ((2:ℤ)^80) * horner X vp0010100011111.list + horner X ep0010100011111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100011111 : Branch 1 (-1309761639/2000000 : ℚ) vp001010001111 := by
  apply branch_checked idp0010100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1309761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1310761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011111
theorem coverp001010001111 : Covers (-1309761639/2000000 : ℚ) vp001010001111 := join_branches bp0010100011110 bp0010100011111
private noncomputable def vp0010100011101_0 : Blocks := edgeBlocks% "full/vectors/0010100011101-V-0000.bin"
noncomputable def vp0010100011101 : Blocks := vp0010100011101_0
theorem coverp0010100011101 : Covers (-1308761639/1000000 : ℚ) vp0010100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100011100_0 : Blocks := edgeBlocks% "full/vectors/0010100011100-V-0000.bin"
noncomputable def vp0010100011100 : Blocks := vp0010100011100_0
theorem coverp0010100011100 : Covers (-1307761639/1000000 : ℚ) vp0010100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001110_0 : Blocks := edgeBlocks% "full/vectors/001010001110-V-0000.bin"
noncomputable def vp001010001110 : Blocks := vp001010001110_0
private theorem bp0010100011100 : Branch 0 (-1307761639/2000000 : ℚ) vp001010001110 := by
  apply branch_left_normalized (c:=vp0010100011100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1307761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1307761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011100
private noncomputable def ep0010100011101_0 : Blocks := edgeBlocks% "full/vectors/0010100011101-E-0000.bin"
noncomputable def ep0010100011101 : Blocks := ep0010100011101_0
private theorem idp0010100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001110.list =
    C ((2:ℤ)^82) * horner X vp0010100011101.list + horner X ep0010100011101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100011101 : Branch 1 (-1307761639/2000000 : ℚ) vp001010001110 := by
  apply branch_checked idp0010100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1307761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1308761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011101
theorem coverp001010001110 : Covers (-1307761639/2000000 : ℚ) vp001010001110 := join_branches bp0010100011100 bp0010100011101
private noncomputable def vp00101000111_0 : Blocks := edgeBlocks% "full/vectors/00101000111-V-0000.bin"
private noncomputable def vp00101000111_1 : Blocks := edgeBlocks% "full/vectors/00101000111-V-0001.bin"
noncomputable def vp00101000111 : Blocks := (Blocks.join vp00101000111_0 vp00101000111_1)
private theorem bp001010001110 : Branch 0 (-1307761639/4000000 : ℚ) vp00101000111 := by
  apply branch_left_normalized (c:=vp001010001110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1307761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1307761639/2000000 : ℚ) by norm_num]
  exact coverp001010001110
private noncomputable def ep001010001111_0 : Blocks := edgeBlocks% "full/vectors/001010001111-E-0000.bin"
private noncomputable def ep001010001111_1 : Blocks := edgeBlocks% "full/vectors/001010001111-E-0001.bin"
noncomputable def ep001010001111 : Blocks := (Blocks.join ep001010001111_0 ep001010001111_1)
private theorem idp001010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000111.list =
    C ((2:ℤ)^143) * horner X vp001010001111.list + horner X ep001010001111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010001111 : Branch 1 (-1307761639/4000000 : ℚ) vp00101000111 := by
  apply branch_checked idp001010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1307761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1309761639/2000000 : ℚ) by norm_num]
  exact coverp001010001111
theorem coverp00101000111 : Covers (-1307761639/4000000 : ℚ) vp00101000111 := join_branches bp001010001110 bp001010001111
private noncomputable def vp0010100011011_0 : Blocks := edgeBlocks% "full/vectors/0010100011011-V-0000.bin"
noncomputable def vp0010100011011 : Blocks := vp0010100011011_0
theorem coverp0010100011011 : Covers (-1306761639/1000000 : ℚ) vp0010100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100011010_0 : Blocks := edgeBlocks% "full/vectors/0010100011010-V-0000.bin"
noncomputable def vp0010100011010 : Blocks := vp0010100011010_0
theorem coverp0010100011010 : Covers (-1305761639/1000000 : ℚ) vp0010100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001101_0 : Blocks := edgeBlocks% "full/vectors/001010001101-V-0000.bin"
noncomputable def vp001010001101 : Blocks := vp001010001101_0
private theorem bp0010100011010 : Branch 0 (-1305761639/2000000 : ℚ) vp001010001101 := by
  apply branch_left_normalized (c:=vp0010100011010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1305761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1305761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011010
private noncomputable def ep0010100011011_0 : Blocks := edgeBlocks% "full/vectors/0010100011011-E-0000.bin"
noncomputable def ep0010100011011 : Blocks := ep0010100011011_0
private theorem idp0010100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001101.list =
    C ((2:ℤ)^81) * horner X vp0010100011011.list + horner X ep0010100011011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100011011 : Branch 1 (-1305761639/2000000 : ℚ) vp001010001101 := by
  apply branch_checked idp0010100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1305761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1306761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011011
theorem coverp001010001101 : Covers (-1305761639/2000000 : ℚ) vp001010001101 := join_branches bp0010100011010 bp0010100011011
private noncomputable def vp0010100011001_0 : Blocks := edgeBlocks% "full/vectors/0010100011001-V-0000.bin"
noncomputable def vp0010100011001 : Blocks := vp0010100011001_0
theorem coverp0010100011001 : Covers (-1304761639/1000000 : ℚ) vp0010100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100011000_0 : Blocks := edgeBlocks% "full/vectors/0010100011000-V-0000.bin"
noncomputable def vp0010100011000 : Blocks := vp0010100011000_0
theorem coverp0010100011000 : Covers (-1303761639/1000000 : ℚ) vp0010100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001100_0 : Blocks := edgeBlocks% "full/vectors/001010001100-V-0000.bin"
noncomputable def vp001010001100 : Blocks := vp001010001100_0
private theorem bp0010100011000 : Branch 0 (-1303761639/2000000 : ℚ) vp001010001100 := by
  apply branch_left_normalized (c:=vp0010100011000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1303761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1303761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011000
private noncomputable def ep0010100011001_0 : Blocks := edgeBlocks% "full/vectors/0010100011001-E-0000.bin"
noncomputable def ep0010100011001 : Blocks := ep0010100011001_0
private theorem idp0010100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001100.list =
    C ((2:ℤ)^82) * horner X vp0010100011001.list + horner X ep0010100011001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100011001 : Branch 1 (-1303761639/2000000 : ℚ) vp001010001100 := by
  apply branch_checked idp0010100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1303761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1304761639/1000000 : ℚ) by norm_num]
  exact coverp0010100011001
theorem coverp001010001100 : Covers (-1303761639/2000000 : ℚ) vp001010001100 := join_branches bp0010100011000 bp0010100011001
private noncomputable def vp00101000110_0 : Blocks := edgeBlocks% "full/vectors/00101000110-V-0000.bin"
private noncomputable def vp00101000110_1 : Blocks := edgeBlocks% "full/vectors/00101000110-V-0001.bin"
noncomputable def vp00101000110 : Blocks := (Blocks.join vp00101000110_0 vp00101000110_1)
private theorem bp001010001100 : Branch 0 (-1303761639/4000000 : ℚ) vp00101000110 := by
  apply branch_left_normalized (c:=vp001010001100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1303761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1303761639/2000000 : ℚ) by norm_num]
  exact coverp001010001100
private noncomputable def ep001010001101_0 : Blocks := edgeBlocks% "full/vectors/001010001101-E-0000.bin"
private noncomputable def ep001010001101_1 : Blocks := edgeBlocks% "full/vectors/001010001101-E-0001.bin"
noncomputable def ep001010001101 : Blocks := (Blocks.join ep001010001101_0 ep001010001101_1)
private theorem idp001010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000110.list =
    C ((2:ℤ)^144) * horner X vp001010001101.list + horner X ep001010001101.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010001101 : Branch 1 (-1303761639/4000000 : ℚ) vp00101000110 := by
  apply branch_checked idp001010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1303761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1305761639/2000000 : ℚ) by norm_num]
  exact coverp001010001101
theorem coverp00101000110 : Covers (-1303761639/4000000 : ℚ) vp00101000110 := join_branches bp001010001100 bp001010001101
private noncomputable def vp0010100011_0 : Blocks := edgeBlocks% "full/vectors/0010100011-V-0000.bin"
private noncomputable def vp0010100011_1 : Blocks := edgeBlocks% "full/vectors/0010100011-V-0001.bin"
noncomputable def vp0010100011 : Blocks := (Blocks.join vp0010100011_0 vp0010100011_1)
private theorem bp00101000110 : Branch 0 (-1303761639/8000000 : ℚ) vp0010100011 := by
  apply branch_left_normalized (c:=vp00101000110) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-1303761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1303761639/4000000 : ℚ) by norm_num]
  exact coverp00101000110
private noncomputable def ep00101000111_0 : Blocks := edgeBlocks% "full/vectors/00101000111-E-0000.bin"
private noncomputable def ep00101000111_1 : Blocks := edgeBlocks% "full/vectors/00101000111-E-0001.bin"
noncomputable def ep00101000111 : Blocks := (Blocks.join ep00101000111_0 ep00101000111_1)
private theorem idp00101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100011.list =
    C ((2:ℤ)^264) * horner X vp00101000111.list + horner X ep00101000111.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101000111 : Branch 1 (-1303761639/8000000 : ℚ) vp0010100011 := by
  apply branch_checked idp00101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1303761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1307761639/4000000 : ℚ) by norm_num]
  exact coverp00101000111
theorem coverp0010100011 : Covers (-1303761639/8000000 : ℚ) vp0010100011 := join_branches bp00101000110 bp00101000111
private noncomputable def vp0010100010111_0 : Blocks := edgeBlocks% "full/vectors/0010100010111-V-0000.bin"
noncomputable def vp0010100010111 : Blocks := vp0010100010111_0
theorem coverp0010100010111 : Covers (-1302761639/1000000 : ℚ) vp0010100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100010110_0 : Blocks := edgeBlocks% "full/vectors/0010100010110-V-0000.bin"
noncomputable def vp0010100010110 : Blocks := vp0010100010110_0
theorem coverp0010100010110 : Covers (-1301761639/1000000 : ℚ) vp0010100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001011_0 : Blocks := edgeBlocks% "full/vectors/001010001011-V-0000.bin"
noncomputable def vp001010001011 : Blocks := vp001010001011_0
private theorem bp0010100010110 : Branch 0 (-1301761639/2000000 : ℚ) vp001010001011 := by
  apply branch_left_normalized (c:=vp0010100010110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1301761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1301761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010110
private noncomputable def ep0010100010111_0 : Blocks := edgeBlocks% "full/vectors/0010100010111-E-0000.bin"
noncomputable def ep0010100010111 : Blocks := ep0010100010111_0
private theorem idp0010100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001011.list =
    C ((2:ℤ)^82) * horner X vp0010100010111.list + horner X ep0010100010111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100010111 : Branch 1 (-1301761639/2000000 : ℚ) vp001010001011 := by
  apply branch_checked idp0010100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1301761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1302761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010111
theorem coverp001010001011 : Covers (-1301761639/2000000 : ℚ) vp001010001011 := join_branches bp0010100010110 bp0010100010111
private noncomputable def vp0010100010101_0 : Blocks := edgeBlocks% "full/vectors/0010100010101-V-0000.bin"
noncomputable def vp0010100010101 : Blocks := vp0010100010101_0
theorem coverp0010100010101 : Covers (-1300761639/1000000 : ℚ) vp0010100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100010100_0 : Blocks := edgeBlocks% "full/vectors/0010100010100-V-0000.bin"
noncomputable def vp0010100010100 : Blocks := vp0010100010100_0
theorem coverp0010100010100 : Covers (-1299761639/1000000 : ℚ) vp0010100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001010_0 : Blocks := edgeBlocks% "full/vectors/001010001010-V-0000.bin"
noncomputable def vp001010001010 : Blocks := vp001010001010_0
private theorem bp0010100010100 : Branch 0 (-1299761639/2000000 : ℚ) vp001010001010 := by
  apply branch_left_normalized (c:=vp0010100010100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1299761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1299761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010100
private noncomputable def ep0010100010101_0 : Blocks := edgeBlocks% "full/vectors/0010100010101-E-0000.bin"
noncomputable def ep0010100010101 : Blocks := ep0010100010101_0
private theorem idp0010100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001010.list =
    C ((2:ℤ)^82) * horner X vp0010100010101.list + horner X ep0010100010101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100010101 : Branch 1 (-1299761639/2000000 : ℚ) vp001010001010 := by
  apply branch_checked idp0010100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1299761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1300761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010101
theorem coverp001010001010 : Covers (-1299761639/2000000 : ℚ) vp001010001010 := join_branches bp0010100010100 bp0010100010101
private noncomputable def vp00101000101_0 : Blocks := edgeBlocks% "full/vectors/00101000101-V-0000.bin"
private noncomputable def vp00101000101_1 : Blocks := edgeBlocks% "full/vectors/00101000101-V-0001.bin"
noncomputable def vp00101000101 : Blocks := (Blocks.join vp00101000101_0 vp00101000101_1)
private theorem bp001010001010 : Branch 0 (-1299761639/4000000 : ℚ) vp00101000101 := by
  apply branch_left_normalized (c:=vp001010001010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1299761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1299761639/2000000 : ℚ) by norm_num]
  exact coverp001010001010
private noncomputable def ep001010001011_0 : Blocks := edgeBlocks% "full/vectors/001010001011-E-0000.bin"
private noncomputable def ep001010001011_1 : Blocks := edgeBlocks% "full/vectors/001010001011-E-0001.bin"
noncomputable def ep001010001011 : Blocks := (Blocks.join ep001010001011_0 ep001010001011_1)
private theorem idp001010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000101.list =
    C ((2:ℤ)^143) * horner X vp001010001011.list + horner X ep001010001011.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010001011 : Branch 1 (-1299761639/4000000 : ℚ) vp00101000101 := by
  apply branch_checked idp001010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1299761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1301761639/2000000 : ℚ) by norm_num]
  exact coverp001010001011
theorem coverp00101000101 : Covers (-1299761639/4000000 : ℚ) vp00101000101 := join_branches bp001010001010 bp001010001011
private noncomputable def vp0010100010011_0 : Blocks := edgeBlocks% "full/vectors/0010100010011-V-0000.bin"
noncomputable def vp0010100010011 : Blocks := vp0010100010011_0
theorem coverp0010100010011 : Covers (-1298761639/1000000 : ℚ) vp0010100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100010010_0 : Blocks := edgeBlocks% "full/vectors/0010100010010-V-0000.bin"
noncomputable def vp0010100010010 : Blocks := vp0010100010010_0
theorem coverp0010100010010 : Covers (-1297761639/1000000 : ℚ) vp0010100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001001_0 : Blocks := edgeBlocks% "full/vectors/001010001001-V-0000.bin"
noncomputable def vp001010001001 : Blocks := vp001010001001_0
private theorem bp0010100010010 : Branch 0 (-1297761639/2000000 : ℚ) vp001010001001 := by
  apply branch_left_normalized (c:=vp0010100010010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1297761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1297761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010010
private noncomputable def ep0010100010011_0 : Blocks := edgeBlocks% "full/vectors/0010100010011-E-0000.bin"
noncomputable def ep0010100010011 : Blocks := ep0010100010011_0
private theorem idp0010100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001001.list =
    C ((2:ℤ)^81) * horner X vp0010100010011.list + horner X ep0010100010011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100010011 : Branch 1 (-1297761639/2000000 : ℚ) vp001010001001 := by
  apply branch_checked idp0010100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1297761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1298761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010011
theorem coverp001010001001 : Covers (-1297761639/2000000 : ℚ) vp001010001001 := join_branches bp0010100010010 bp0010100010011
private noncomputable def vp0010100010001_0 : Blocks := edgeBlocks% "full/vectors/0010100010001-V-0000.bin"
noncomputable def vp0010100010001 : Blocks := vp0010100010001_0
theorem coverp0010100010001 : Covers (-1296761639/1000000 : ℚ) vp0010100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100010000_0 : Blocks := edgeBlocks% "full/vectors/0010100010000-V-0000.bin"
noncomputable def vp0010100010000 : Blocks := vp0010100010000_0
theorem coverp0010100010000 : Covers (-1295761639/1000000 : ℚ) vp0010100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010001000_0 : Blocks := edgeBlocks% "full/vectors/001010001000-V-0000.bin"
noncomputable def vp001010001000 : Blocks := vp001010001000_0
private theorem bp0010100010000 : Branch 0 (-1295761639/2000000 : ℚ) vp001010001000 := by
  apply branch_left_normalized (c:=vp0010100010000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1295761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1295761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010000
private noncomputable def ep0010100010001_0 : Blocks := edgeBlocks% "full/vectors/0010100010001-E-0000.bin"
noncomputable def ep0010100010001 : Blocks := ep0010100010001_0
private theorem idp0010100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001000.list =
    C ((2:ℤ)^82) * horner X vp0010100010001.list + horner X ep0010100010001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100010001 : Branch 1 (-1295761639/2000000 : ℚ) vp001010001000 := by
  apply branch_checked idp0010100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1295761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1296761639/1000000 : ℚ) by norm_num]
  exact coverp0010100010001
theorem coverp001010001000 : Covers (-1295761639/2000000 : ℚ) vp001010001000 := join_branches bp0010100010000 bp0010100010001
private noncomputable def vp00101000100_0 : Blocks := edgeBlocks% "full/vectors/00101000100-V-0000.bin"
private noncomputable def vp00101000100_1 : Blocks := edgeBlocks% "full/vectors/00101000100-V-0001.bin"
noncomputable def vp00101000100 : Blocks := (Blocks.join vp00101000100_0 vp00101000100_1)
private theorem bp001010001000 : Branch 0 (-1295761639/4000000 : ℚ) vp00101000100 := by
  apply branch_left_normalized (c:=vp001010001000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1295761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1295761639/2000000 : ℚ) by norm_num]
  exact coverp001010001000
private noncomputable def ep001010001001_0 : Blocks := edgeBlocks% "full/vectors/001010001001-E-0000.bin"
private noncomputable def ep001010001001_1 : Blocks := edgeBlocks% "full/vectors/001010001001-E-0001.bin"
noncomputable def ep001010001001 : Blocks := (Blocks.join ep001010001001_0 ep001010001001_1)
private theorem idp001010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000100.list =
    C ((2:ℤ)^143) * horner X vp001010001001.list + horner X ep001010001001.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010001001 : Branch 1 (-1295761639/4000000 : ℚ) vp00101000100 := by
  apply branch_checked idp001010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1295761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1297761639/2000000 : ℚ) by norm_num]
  exact coverp001010001001
theorem coverp00101000100 : Covers (-1295761639/4000000 : ℚ) vp00101000100 := join_branches bp001010001000 bp001010001001
private noncomputable def vp0010100010_0 : Blocks := edgeBlocks% "full/vectors/0010100010-V-0000.bin"
private noncomputable def vp0010100010_1 : Blocks := edgeBlocks% "full/vectors/0010100010-V-0001.bin"
noncomputable def vp0010100010 : Blocks := (Blocks.join vp0010100010_0 vp0010100010_1)
private theorem bp00101000100 : Branch 0 (-1295761639/8000000 : ℚ) vp0010100010 := by
  apply branch_left_normalized (c:=vp00101000100) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-1295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1295761639/4000000 : ℚ) by norm_num]
  exact coverp00101000100
private noncomputable def ep00101000101_0 : Blocks := edgeBlocks% "full/vectors/00101000101-E-0000.bin"
private noncomputable def ep00101000101_1 : Blocks := edgeBlocks% "full/vectors/00101000101-E-0001.bin"
noncomputable def ep00101000101 : Blocks := (Blocks.join ep00101000101_0 ep00101000101_1)
private theorem idp00101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100010.list =
    C ((2:ℤ)^264) * horner X vp00101000101.list + horner X ep00101000101.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101000101 : Branch 1 (-1295761639/8000000 : ℚ) vp0010100010 := by
  apply branch_checked idp00101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1299761639/4000000 : ℚ) by norm_num]
  exact coverp00101000101
theorem coverp0010100010 : Covers (-1295761639/8000000 : ℚ) vp0010100010 := join_branches bp00101000100 bp00101000101
private noncomputable def vp001010001_0 : Blocks := edgeBlocks% "full/vectors/001010001-V-0000.bin"
private noncomputable def vp001010001_1 : Blocks := edgeBlocks% "full/vectors/001010001-V-0001.bin"
private noncomputable def vp001010001_2 : Blocks := edgeBlocks% "full/vectors/001010001-V-0002.bin"
private noncomputable def vp001010001_3 : Blocks := edgeBlocks% "full/vectors/001010001-V-0003.bin"
noncomputable def vp001010001 : Blocks := (Blocks.join (Blocks.join vp001010001_0 vp001010001_1) (Blocks.join vp001010001_2 vp001010001_3))
private theorem bp0010100010 : Branch 0 (-1295761639/16000000 : ℚ) vp001010001 := by
  apply branch_left_normalized (c:=vp0010100010) (k:=0) (m:=240) (by decide +kernel)
  rw [show 2*(-1295761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1295761639/8000000 : ℚ) by norm_num]
  exact coverp0010100010
private noncomputable def ep0010100011_0 : Blocks := edgeBlocks% "full/vectors/0010100011-E-0000.bin"
private noncomputable def ep0010100011_1 : Blocks := edgeBlocks% "full/vectors/0010100011-E-0001.bin"
private noncomputable def ep0010100011_2 : Blocks := edgeBlocks% "full/vectors/0010100011-E-0002.bin"
private noncomputable def ep0010100011_3 : Blocks := edgeBlocks% "full/vectors/0010100011-E-0003.bin"
noncomputable def ep0010100011 : Blocks := (Blocks.join (Blocks.join ep0010100011_0 ep0010100011_1) (Blocks.join ep0010100011_2 ep0010100011_3))
private theorem idp0010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010001.list =
    C ((2:ℤ)^504) * horner X vp0010100011.list + horner X ep0010100011.list := by
  exact edge_identity (B := (2:ℤ)^791) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100011 : Branch 1 (-1295761639/16000000 : ℚ) vp001010001 := by
  apply branch_checked idp0010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1295761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1303761639/8000000 : ℚ) by norm_num]
  exact coverp0010100011
theorem coverp001010001 : Covers (-1295761639/16000000 : ℚ) vp001010001 := join_branches bp0010100010 bp0010100011
private noncomputable def vp0010100001111_0 : Blocks := edgeBlocks% "full/vectors/0010100001111-V-0000.bin"
noncomputable def vp0010100001111 : Blocks := vp0010100001111_0
theorem coverp0010100001111 : Covers (-1294761639/1000000 : ℚ) vp0010100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100001110_0 : Blocks := edgeBlocks% "full/vectors/0010100001110-V-0000.bin"
noncomputable def vp0010100001110 : Blocks := vp0010100001110_0
theorem coverp0010100001110 : Covers (-1293761639/1000000 : ℚ) vp0010100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000111_0 : Blocks := edgeBlocks% "full/vectors/001010000111-V-0000.bin"
noncomputable def vp001010000111 : Blocks := vp001010000111_0
private theorem bp0010100001110 : Branch 0 (-1293761639/2000000 : ℚ) vp001010000111 := by
  apply branch_left_normalized (c:=vp0010100001110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1293761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1293761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001110
private noncomputable def ep0010100001111_0 : Blocks := edgeBlocks% "full/vectors/0010100001111-E-0000.bin"
noncomputable def ep0010100001111 : Blocks := ep0010100001111_0
private theorem idp0010100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000111.list =
    C ((2:ℤ)^82) * horner X vp0010100001111.list + horner X ep0010100001111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100001111 : Branch 1 (-1293761639/2000000 : ℚ) vp001010000111 := by
  apply branch_checked idp0010100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1293761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1294761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001111
theorem coverp001010000111 : Covers (-1293761639/2000000 : ℚ) vp001010000111 := join_branches bp0010100001110 bp0010100001111
private noncomputable def vp0010100001101_0 : Blocks := edgeBlocks% "full/vectors/0010100001101-V-0000.bin"
noncomputable def vp0010100001101 : Blocks := vp0010100001101_0
theorem coverp0010100001101 : Covers (-1292761639/1000000 : ℚ) vp0010100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100001100_0 : Blocks := edgeBlocks% "full/vectors/0010100001100-V-0000.bin"
noncomputable def vp0010100001100 : Blocks := vp0010100001100_0
theorem coverp0010100001100 : Covers (-1291761639/1000000 : ℚ) vp0010100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000110_0 : Blocks := edgeBlocks% "full/vectors/001010000110-V-0000.bin"
noncomputable def vp001010000110 : Blocks := vp001010000110_0
private theorem bp0010100001100 : Branch 0 (-1291761639/2000000 : ℚ) vp001010000110 := by
  apply branch_left_normalized (c:=vp0010100001100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1291761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1291761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001100
private noncomputable def ep0010100001101_0 : Blocks := edgeBlocks% "full/vectors/0010100001101-E-0000.bin"
noncomputable def ep0010100001101 : Blocks := ep0010100001101_0
private theorem idp0010100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000110.list =
    C ((2:ℤ)^82) * horner X vp0010100001101.list + horner X ep0010100001101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100001101 : Branch 1 (-1291761639/2000000 : ℚ) vp001010000110 := by
  apply branch_checked idp0010100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1291761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1292761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001101
theorem coverp001010000110 : Covers (-1291761639/2000000 : ℚ) vp001010000110 := join_branches bp0010100001100 bp0010100001101
private noncomputable def vp00101000011_0 : Blocks := edgeBlocks% "full/vectors/00101000011-V-0000.bin"
private noncomputable def vp00101000011_1 : Blocks := edgeBlocks% "full/vectors/00101000011-V-0001.bin"
noncomputable def vp00101000011 : Blocks := (Blocks.join vp00101000011_0 vp00101000011_1)
private theorem bp001010000110 : Branch 0 (-1291761639/4000000 : ℚ) vp00101000011 := by
  apply branch_left_normalized (c:=vp001010000110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1291761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1291761639/2000000 : ℚ) by norm_num]
  exact coverp001010000110
private noncomputable def ep001010000111_0 : Blocks := edgeBlocks% "full/vectors/001010000111-E-0000.bin"
private noncomputable def ep001010000111_1 : Blocks := edgeBlocks% "full/vectors/001010000111-E-0001.bin"
noncomputable def ep001010000111 : Blocks := (Blocks.join ep001010000111_0 ep001010000111_1)
private theorem idp001010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000011.list =
    C ((2:ℤ)^143) * horner X vp001010000111.list + horner X ep001010000111.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010000111 : Branch 1 (-1291761639/4000000 : ℚ) vp00101000011 := by
  apply branch_checked idp001010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1291761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1293761639/2000000 : ℚ) by norm_num]
  exact coverp001010000111
theorem coverp00101000011 : Covers (-1291761639/4000000 : ℚ) vp00101000011 := join_branches bp001010000110 bp001010000111
private noncomputable def vp0010100001011_0 : Blocks := edgeBlocks% "full/vectors/0010100001011-V-0000.bin"
noncomputable def vp0010100001011 : Blocks := vp0010100001011_0
theorem coverp0010100001011 : Covers (-1290761639/1000000 : ℚ) vp0010100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100001010_0 : Blocks := edgeBlocks% "full/vectors/0010100001010-V-0000.bin"
noncomputable def vp0010100001010 : Blocks := vp0010100001010_0
theorem coverp0010100001010 : Covers (-1289761639/1000000 : ℚ) vp0010100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000101_0 : Blocks := edgeBlocks% "full/vectors/001010000101-V-0000.bin"
noncomputable def vp001010000101 : Blocks := vp001010000101_0
private theorem bp0010100001010 : Branch 0 (-1289761639/2000000 : ℚ) vp001010000101 := by
  apply branch_left_normalized (c:=vp0010100001010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1289761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1289761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001010
private noncomputable def ep0010100001011_0 : Blocks := edgeBlocks% "full/vectors/0010100001011-E-0000.bin"
noncomputable def ep0010100001011 : Blocks := ep0010100001011_0
private theorem idp0010100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000101.list =
    C ((2:ℤ)^82) * horner X vp0010100001011.list + horner X ep0010100001011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100001011 : Branch 1 (-1289761639/2000000 : ℚ) vp001010000101 := by
  apply branch_checked idp0010100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1289761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1290761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001011
theorem coverp001010000101 : Covers (-1289761639/2000000 : ℚ) vp001010000101 := join_branches bp0010100001010 bp0010100001011
private noncomputable def vp0010100001001_0 : Blocks := edgeBlocks% "full/vectors/0010100001001-V-0000.bin"
noncomputable def vp0010100001001 : Blocks := vp0010100001001_0
theorem coverp0010100001001 : Covers (-1288761639/1000000 : ℚ) vp0010100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100001000_0 : Blocks := edgeBlocks% "full/vectors/0010100001000-V-0000.bin"
noncomputable def vp0010100001000 : Blocks := vp0010100001000_0
theorem coverp0010100001000 : Covers (-1287761639/1000000 : ℚ) vp0010100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000100_0 : Blocks := edgeBlocks% "full/vectors/001010000100-V-0000.bin"
noncomputable def vp001010000100 : Blocks := vp001010000100_0
private theorem bp0010100001000 : Branch 0 (-1287761639/2000000 : ℚ) vp001010000100 := by
  apply branch_left_normalized (c:=vp0010100001000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1287761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1287761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001000
private noncomputable def ep0010100001001_0 : Blocks := edgeBlocks% "full/vectors/0010100001001-E-0000.bin"
noncomputable def ep0010100001001 : Blocks := ep0010100001001_0
private theorem idp0010100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000100.list =
    C ((2:ℤ)^81) * horner X vp0010100001001.list + horner X ep0010100001001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100001001 : Branch 1 (-1287761639/2000000 : ℚ) vp001010000100 := by
  apply branch_checked idp0010100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1287761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1288761639/1000000 : ℚ) by norm_num]
  exact coverp0010100001001
theorem coverp001010000100 : Covers (-1287761639/2000000 : ℚ) vp001010000100 := join_branches bp0010100001000 bp0010100001001
private noncomputable def vp00101000010_0 : Blocks := edgeBlocks% "full/vectors/00101000010-V-0000.bin"
private noncomputable def vp00101000010_1 : Blocks := edgeBlocks% "full/vectors/00101000010-V-0001.bin"
noncomputable def vp00101000010 : Blocks := (Blocks.join vp00101000010_0 vp00101000010_1)
private theorem bp001010000100 : Branch 0 (-1287761639/4000000 : ℚ) vp00101000010 := by
  apply branch_left_normalized (c:=vp001010000100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1287761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1287761639/2000000 : ℚ) by norm_num]
  exact coverp001010000100
private noncomputable def ep001010000101_0 : Blocks := edgeBlocks% "full/vectors/001010000101-E-0000.bin"
private noncomputable def ep001010000101_1 : Blocks := edgeBlocks% "full/vectors/001010000101-E-0001.bin"
noncomputable def ep001010000101 : Blocks := (Blocks.join ep001010000101_0 ep001010000101_1)
private theorem idp001010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000010.list =
    C ((2:ℤ)^143) * horner X vp001010000101.list + horner X ep001010000101.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010000101 : Branch 1 (-1287761639/4000000 : ℚ) vp00101000010 := by
  apply branch_checked idp001010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1287761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1289761639/2000000 : ℚ) by norm_num]
  exact coverp001010000101
theorem coverp00101000010 : Covers (-1287761639/4000000 : ℚ) vp00101000010 := join_branches bp001010000100 bp001010000101
private noncomputable def vp0010100001_0 : Blocks := edgeBlocks% "full/vectors/0010100001-V-0000.bin"
private noncomputable def vp0010100001_1 : Blocks := edgeBlocks% "full/vectors/0010100001-V-0001.bin"
noncomputable def vp0010100001 : Blocks := (Blocks.join vp0010100001_0 vp0010100001_1)
private theorem bp00101000010 : Branch 0 (-1287761639/8000000 : ℚ) vp0010100001 := by
  apply branch_left_normalized (c:=vp00101000010) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-1287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1287761639/4000000 : ℚ) by norm_num]
  exact coverp00101000010
private noncomputable def ep00101000011_0 : Blocks := edgeBlocks% "full/vectors/00101000011-E-0000.bin"
private noncomputable def ep00101000011_1 : Blocks := edgeBlocks% "full/vectors/00101000011-E-0001.bin"
noncomputable def ep00101000011 : Blocks := (Blocks.join ep00101000011_0 ep00101000011_1)
private theorem idp00101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100001.list =
    C ((2:ℤ)^265) * horner X vp00101000011.list + horner X ep00101000011.list := by
  exact edge_identity (B := (2:ℤ)^459) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101000011 : Branch 1 (-1287761639/8000000 : ℚ) vp0010100001 := by
  apply branch_checked idp00101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1291761639/4000000 : ℚ) by norm_num]
  exact coverp00101000011
theorem coverp0010100001 : Covers (-1287761639/8000000 : ℚ) vp0010100001 := join_branches bp00101000010 bp00101000011
private noncomputable def vp0010100000111_0 : Blocks := edgeBlocks% "full/vectors/0010100000111-V-0000.bin"
noncomputable def vp0010100000111 : Blocks := vp0010100000111_0
theorem coverp0010100000111 : Covers (-1286761639/1000000 : ℚ) vp0010100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100000110_0 : Blocks := edgeBlocks% "full/vectors/0010100000110-V-0000.bin"
noncomputable def vp0010100000110 : Blocks := vp0010100000110_0
theorem coverp0010100000110 : Covers (-1285761639/1000000 : ℚ) vp0010100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000011_0 : Blocks := edgeBlocks% "full/vectors/001010000011-V-0000.bin"
noncomputable def vp001010000011 : Blocks := vp001010000011_0
private theorem bp0010100000110 : Branch 0 (-1285761639/2000000 : ℚ) vp001010000011 := by
  apply branch_left_normalized (c:=vp0010100000110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1285761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1285761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000110
private noncomputable def ep0010100000111_0 : Blocks := edgeBlocks% "full/vectors/0010100000111-E-0000.bin"
noncomputable def ep0010100000111 : Blocks := ep0010100000111_0
private theorem idp0010100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000011.list =
    C ((2:ℤ)^82) * horner X vp0010100000111.list + horner X ep0010100000111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100000111 : Branch 1 (-1285761639/2000000 : ℚ) vp001010000011 := by
  apply branch_checked idp0010100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1285761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1286761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000111
theorem coverp001010000011 : Covers (-1285761639/2000000 : ℚ) vp001010000011 := join_branches bp0010100000110 bp0010100000111
private noncomputable def vp0010100000101_0 : Blocks := edgeBlocks% "full/vectors/0010100000101-V-0000.bin"
noncomputable def vp0010100000101 : Blocks := vp0010100000101_0
theorem coverp0010100000101 : Covers (-1284761639/1000000 : ℚ) vp0010100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100000100_0 : Blocks := edgeBlocks% "full/vectors/0010100000100-V-0000.bin"
noncomputable def vp0010100000100 : Blocks := vp0010100000100_0
theorem coverp0010100000100 : Covers (-1283761639/1000000 : ℚ) vp0010100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000010_0 : Blocks := edgeBlocks% "full/vectors/001010000010-V-0000.bin"
noncomputable def vp001010000010 : Blocks := vp001010000010_0
private theorem bp0010100000100 : Branch 0 (-1283761639/2000000 : ℚ) vp001010000010 := by
  apply branch_left_normalized (c:=vp0010100000100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1283761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1283761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000100
private noncomputable def ep0010100000101_0 : Blocks := edgeBlocks% "full/vectors/0010100000101-E-0000.bin"
noncomputable def ep0010100000101 : Blocks := ep0010100000101_0
private theorem idp0010100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000010.list =
    C ((2:ℤ)^82) * horner X vp0010100000101.list + horner X ep0010100000101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100000101 : Branch 1 (-1283761639/2000000 : ℚ) vp001010000010 := by
  apply branch_checked idp0010100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1283761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1284761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000101
theorem coverp001010000010 : Covers (-1283761639/2000000 : ℚ) vp001010000010 := join_branches bp0010100000100 bp0010100000101
private noncomputable def vp00101000001_0 : Blocks := edgeBlocks% "full/vectors/00101000001-V-0000.bin"
private noncomputable def vp00101000001_1 : Blocks := edgeBlocks% "full/vectors/00101000001-V-0001.bin"
noncomputable def vp00101000001 : Blocks := (Blocks.join vp00101000001_0 vp00101000001_1)
private theorem bp001010000010 : Branch 0 (-1283761639/4000000 : ℚ) vp00101000001 := by
  apply branch_left_normalized (c:=vp001010000010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1283761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1283761639/2000000 : ℚ) by norm_num]
  exact coverp001010000010
private noncomputable def ep001010000011_0 : Blocks := edgeBlocks% "full/vectors/001010000011-E-0000.bin"
private noncomputable def ep001010000011_1 : Blocks := edgeBlocks% "full/vectors/001010000011-E-0001.bin"
noncomputable def ep001010000011 : Blocks := (Blocks.join ep001010000011_0 ep001010000011_1)
private theorem idp001010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000001.list =
    C ((2:ℤ)^143) * horner X vp001010000011.list + horner X ep001010000011.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010000011 : Branch 1 (-1283761639/4000000 : ℚ) vp00101000001 := by
  apply branch_checked idp001010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1283761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1285761639/2000000 : ℚ) by norm_num]
  exact coverp001010000011
theorem coverp00101000001 : Covers (-1283761639/4000000 : ℚ) vp00101000001 := join_branches bp001010000010 bp001010000011
private noncomputable def vp0010100000011_0 : Blocks := edgeBlocks% "full/vectors/0010100000011-V-0000.bin"
noncomputable def vp0010100000011 : Blocks := vp0010100000011_0
theorem coverp0010100000011 : Covers (-1282761639/1000000 : ℚ) vp0010100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100000010_0 : Blocks := edgeBlocks% "full/vectors/0010100000010-V-0000.bin"
noncomputable def vp0010100000010 : Blocks := vp0010100000010_0
theorem coverp0010100000010 : Covers (-1281761639/1000000 : ℚ) vp0010100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000001_0 : Blocks := edgeBlocks% "full/vectors/001010000001-V-0000.bin"
noncomputable def vp001010000001 : Blocks := vp001010000001_0
private theorem bp0010100000010 : Branch 0 (-1281761639/2000000 : ℚ) vp001010000001 := by
  apply branch_left_normalized (c:=vp0010100000010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1281761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1281761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000010
private noncomputable def ep0010100000011_0 : Blocks := edgeBlocks% "full/vectors/0010100000011-E-0000.bin"
noncomputable def ep0010100000011 : Blocks := ep0010100000011_0
private theorem idp0010100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000001.list =
    C ((2:ℤ)^82) * horner X vp0010100000011.list + horner X ep0010100000011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100000011 : Branch 1 (-1281761639/2000000 : ℚ) vp001010000001 := by
  apply branch_checked idp0010100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1281761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1282761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000011
theorem coverp001010000001 : Covers (-1281761639/2000000 : ℚ) vp001010000001 := join_branches bp0010100000010 bp0010100000011
private noncomputable def vp0010100000001_0 : Blocks := edgeBlocks% "full/vectors/0010100000001-V-0000.bin"
noncomputable def vp0010100000001 : Blocks := vp0010100000001_0
theorem coverp0010100000001 : Covers (-1280761639/1000000 : ℚ) vp0010100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010100000000_0 : Blocks := edgeBlocks% "full/vectors/0010100000000-V-0000.bin"
noncomputable def vp0010100000000 : Blocks := vp0010100000000_0
theorem coverp0010100000000 : Covers (-1279761639/1000000 : ℚ) vp0010100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010000000_0 : Blocks := edgeBlocks% "full/vectors/001010000000-V-0000.bin"
noncomputable def vp001010000000 : Blocks := vp001010000000_0
private theorem bp0010100000000 : Branch 0 (-1279761639/2000000 : ℚ) vp001010000000 := by
  apply branch_left_normalized (c:=vp0010100000000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1279761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000000
private noncomputable def ep0010100000001_0 : Blocks := edgeBlocks% "full/vectors/0010100000001-E-0000.bin"
noncomputable def ep0010100000001 : Blocks := ep0010100000001_0
private theorem idp0010100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000000.list =
    C ((2:ℤ)^82) * horner X vp0010100000001.list + horner X ep0010100000001.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100000001 : Branch 1 (-1279761639/2000000 : ℚ) vp001010000000 := by
  apply branch_checked idp0010100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1280761639/1000000 : ℚ) by norm_num]
  exact coverp0010100000001
theorem coverp001010000000 : Covers (-1279761639/2000000 : ℚ) vp001010000000 := join_branches bp0010100000000 bp0010100000001
private noncomputable def vp00101000000_0 : Blocks := edgeBlocks% "full/vectors/00101000000-V-0000.bin"
private noncomputable def vp00101000000_1 : Blocks := edgeBlocks% "full/vectors/00101000000-V-0001.bin"
noncomputable def vp00101000000 : Blocks := (Blocks.join vp00101000000_0 vp00101000000_1)
private theorem bp001010000000 : Branch 0 (-1279761639/4000000 : ℚ) vp00101000000 := by
  apply branch_left_normalized (c:=vp001010000000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1279761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/2000000 : ℚ) by norm_num]
  exact coverp001010000000
private noncomputable def ep001010000001_0 : Blocks := edgeBlocks% "full/vectors/001010000001-E-0000.bin"
private noncomputable def ep001010000001_1 : Blocks := edgeBlocks% "full/vectors/001010000001-E-0001.bin"
noncomputable def ep001010000001 : Blocks := (Blocks.join ep001010000001_0 ep001010000001_1)
private theorem idp001010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000000.list =
    C ((2:ℤ)^143) * horner X vp001010000001.list + horner X ep001010000001.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010000001 : Branch 1 (-1279761639/4000000 : ℚ) vp00101000000 := by
  apply branch_checked idp001010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1281761639/2000000 : ℚ) by norm_num]
  exact coverp001010000001
theorem coverp00101000000 : Covers (-1279761639/4000000 : ℚ) vp00101000000 := join_branches bp001010000000 bp001010000001
private noncomputable def vp0010100000_0 : Blocks := edgeBlocks% "full/vectors/0010100000-V-0000.bin"
private noncomputable def vp0010100000_1 : Blocks := edgeBlocks% "full/vectors/0010100000-V-0001.bin"
noncomputable def vp0010100000 : Blocks := (Blocks.join vp0010100000_0 vp0010100000_1)
private theorem bp00101000000 : Branch 0 (-1279761639/8000000 : ℚ) vp0010100000 := by
  apply branch_left_normalized (c:=vp00101000000) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-1279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/4000000 : ℚ) by norm_num]
  exact coverp00101000000
private noncomputable def ep00101000001_0 : Blocks := edgeBlocks% "full/vectors/00101000001-E-0000.bin"
private noncomputable def ep00101000001_1 : Blocks := edgeBlocks% "full/vectors/00101000001-E-0001.bin"
noncomputable def ep00101000001 : Blocks := (Blocks.join ep00101000001_0 ep00101000001_1)
private theorem idp00101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100000.list =
    C ((2:ℤ)^265) * horner X vp00101000001.list + horner X ep00101000001.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101000001 : Branch 1 (-1279761639/8000000 : ℚ) vp0010100000 := by
  apply branch_checked idp00101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1283761639/4000000 : ℚ) by norm_num]
  exact coverp00101000001
theorem coverp0010100000 : Covers (-1279761639/8000000 : ℚ) vp0010100000 := join_branches bp00101000000 bp00101000001
private noncomputable def vp001010000_0 : Blocks := edgeBlocks% "full/vectors/001010000-V-0000.bin"
private noncomputable def vp001010000_1 : Blocks := edgeBlocks% "full/vectors/001010000-V-0001.bin"
private noncomputable def vp001010000_2 : Blocks := edgeBlocks% "full/vectors/001010000-V-0002.bin"
private noncomputable def vp001010000_3 : Blocks := edgeBlocks% "full/vectors/001010000-V-0003.bin"
noncomputable def vp001010000 : Blocks := (Blocks.join (Blocks.join vp001010000_0 vp001010000_1) (Blocks.join vp001010000_2 vp001010000_3))
private theorem bp0010100000 : Branch 0 (-1279761639/16000000 : ℚ) vp001010000 := by
  apply branch_left_normalized (c:=vp0010100000) (k:=0) (m:=241) (by decide +kernel)
  rw [show 2*(-1279761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/8000000 : ℚ) by norm_num]
  exact coverp0010100000
private noncomputable def ep0010100001_0 : Blocks := edgeBlocks% "full/vectors/0010100001-E-0000.bin"
private noncomputable def ep0010100001_1 : Blocks := edgeBlocks% "full/vectors/0010100001-E-0001.bin"
private noncomputable def ep0010100001_2 : Blocks := edgeBlocks% "full/vectors/0010100001-E-0002.bin"
private noncomputable def ep0010100001_3 : Blocks := edgeBlocks% "full/vectors/0010100001-E-0003.bin"
noncomputable def ep0010100001 : Blocks := (Blocks.join (Blocks.join ep0010100001_0 ep0010100001_1) (Blocks.join ep0010100001_2 ep0010100001_3))
private theorem idp0010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010000.list =
    C ((2:ℤ)^507) * horner X vp0010100001.list + horner X ep0010100001.list := by
  exact edge_identity (B := (2:ℤ)^795) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010100001 : Branch 1 (-1279761639/16000000 : ℚ) vp001010000 := by
  apply branch_checked idp0010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1287761639/8000000 : ℚ) by norm_num]
  exact coverp0010100001
theorem coverp001010000 : Covers (-1279761639/16000000 : ℚ) vp001010000 := join_branches bp0010100000 bp0010100001
private noncomputable def vp00101000_0 : Blocks := edgeBlocks% "full/vectors/00101000-V-0000.bin"
private noncomputable def vp00101000_1 : Blocks := edgeBlocks% "full/vectors/00101000-V-0001.bin"
private noncomputable def vp00101000_2 : Blocks := edgeBlocks% "full/vectors/00101000-V-0002.bin"
private noncomputable def vp00101000_3 : Blocks := edgeBlocks% "full/vectors/00101000-V-0003.bin"
private noncomputable def vp00101000_4 : Blocks := edgeBlocks% "full/vectors/00101000-V-0004.bin"
private noncomputable def vp00101000_5 : Blocks := edgeBlocks% "full/vectors/00101000-V-0005.bin"
private noncomputable def vp00101000_6 : Blocks := edgeBlocks% "full/vectors/00101000-V-0006.bin"
noncomputable def vp00101000 : Blocks := (Blocks.join (Blocks.join vp00101000_0 (Blocks.join vp00101000_1 vp00101000_2)) (Blocks.join (Blocks.join vp00101000_3 vp00101000_4) (Blocks.join vp00101000_5 vp00101000_6)))
private theorem bp001010000 : Branch 0 (-1279761639/32000000 : ℚ) vp00101000 := by
  apply branch_left_normalized (c:=vp001010000) (k:=0) (m:=460) (by decide +kernel)
  rw [show 2*(-1279761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/16000000 : ℚ) by norm_num]
  exact coverp001010000
private noncomputable def ep001010001_0 : Blocks := edgeBlocks% "full/vectors/001010001-E-0000.bin"
private noncomputable def ep001010001_1 : Blocks := edgeBlocks% "full/vectors/001010001-E-0001.bin"
private noncomputable def ep001010001_2 : Blocks := edgeBlocks% "full/vectors/001010001-E-0002.bin"
private noncomputable def ep001010001_3 : Blocks := edgeBlocks% "full/vectors/001010001-E-0003.bin"
private noncomputable def ep001010001_4 : Blocks := edgeBlocks% "full/vectors/001010001-E-0004.bin"
private noncomputable def ep001010001_5 : Blocks := edgeBlocks% "full/vectors/001010001-E-0005.bin"
private noncomputable def ep001010001_6 : Blocks := edgeBlocks% "full/vectors/001010001-E-0006.bin"
noncomputable def ep001010001 : Blocks := (Blocks.join (Blocks.join ep001010001_0 (Blocks.join ep001010001_1 ep001010001_2)) (Blocks.join (Blocks.join ep001010001_3 ep001010001_4) (Blocks.join ep001010001_5 ep001010001_6)))
private theorem idp001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101000.list =
    C ((2:ℤ)^984) * horner X vp001010001.list + horner X ep001010001.list := by
  exact edge_identity (B := (2:ℤ)^1458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010001 : Branch 1 (-1279761639/32000000 : ℚ) vp00101000 := by
  apply branch_checked idp001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1295761639/16000000 : ℚ) by norm_num]
  exact coverp001010001
theorem coverp00101000 : Covers (-1279761639/32000000 : ℚ) vp00101000 := join_branches bp001010000 bp001010001
private noncomputable def vp0010100_0 : Blocks := edgeBlocks% "full/vectors/0010100-V-0000.bin"
private noncomputable def vp0010100_1 : Blocks := edgeBlocks% "full/vectors/0010100-V-0001.bin"
private noncomputable def vp0010100_2 : Blocks := edgeBlocks% "full/vectors/0010100-V-0002.bin"
private noncomputable def vp0010100_3 : Blocks := edgeBlocks% "full/vectors/0010100-V-0003.bin"
private noncomputable def vp0010100_4 : Blocks := edgeBlocks% "full/vectors/0010100-V-0004.bin"
private noncomputable def vp0010100_5 : Blocks := edgeBlocks% "full/vectors/0010100-V-0005.bin"
private noncomputable def vp0010100_6 : Blocks := edgeBlocks% "full/vectors/0010100-V-0006.bin"
private noncomputable def vp0010100_7 : Blocks := edgeBlocks% "full/vectors/0010100-V-0007.bin"
private noncomputable def vp0010100_8 : Blocks := edgeBlocks% "full/vectors/0010100-V-0008.bin"
private noncomputable def vp0010100_9 : Blocks := edgeBlocks% "full/vectors/0010100-V-0009.bin"
private noncomputable def vp0010100_10 : Blocks := edgeBlocks% "full/vectors/0010100-V-0010.bin"
private noncomputable def vp0010100_11 : Blocks := edgeBlocks% "full/vectors/0010100-V-0011.bin"
private noncomputable def vp0010100_12 : Blocks := edgeBlocks% "full/vectors/0010100-V-0012.bin"
private noncomputable def vp0010100_13 : Blocks := edgeBlocks% "full/vectors/0010100-V-0013.bin"
noncomputable def vp0010100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010100_0 (Blocks.join vp0010100_1 vp0010100_2)) (Blocks.join (Blocks.join vp0010100_3 vp0010100_4) (Blocks.join vp0010100_5 vp0010100_6))) (Blocks.join (Blocks.join vp0010100_7 (Blocks.join vp0010100_8 vp0010100_9)) (Blocks.join (Blocks.join vp0010100_10 vp0010100_11) (Blocks.join vp0010100_12 vp0010100_13))))
private theorem bp00101000 : Branch 0 (-1279761639/64000000 : ℚ) vp0010100 := by
  apply branch_left_normalized (c:=vp00101000) (k:=0) (m:=891) (by decide +kernel)
  rw [show 2*(-1279761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/32000000 : ℚ) by norm_num]
  exact coverp00101000
private noncomputable def ep00101001_0 : Blocks := edgeBlocks% "full/vectors/00101001-E-0000.bin"
private noncomputable def ep00101001_1 : Blocks := edgeBlocks% "full/vectors/00101001-E-0001.bin"
private noncomputable def ep00101001_2 : Blocks := edgeBlocks% "full/vectors/00101001-E-0002.bin"
private noncomputable def ep00101001_3 : Blocks := edgeBlocks% "full/vectors/00101001-E-0003.bin"
private noncomputable def ep00101001_4 : Blocks := edgeBlocks% "full/vectors/00101001-E-0004.bin"
private noncomputable def ep00101001_5 : Blocks := edgeBlocks% "full/vectors/00101001-E-0005.bin"
private noncomputable def ep00101001_6 : Blocks := edgeBlocks% "full/vectors/00101001-E-0006.bin"
private noncomputable def ep00101001_7 : Blocks := edgeBlocks% "full/vectors/00101001-E-0007.bin"
private noncomputable def ep00101001_8 : Blocks := edgeBlocks% "full/vectors/00101001-E-0008.bin"
private noncomputable def ep00101001_9 : Blocks := edgeBlocks% "full/vectors/00101001-E-0009.bin"
private noncomputable def ep00101001_10 : Blocks := edgeBlocks% "full/vectors/00101001-E-0010.bin"
private noncomputable def ep00101001_11 : Blocks := edgeBlocks% "full/vectors/00101001-E-0011.bin"
private noncomputable def ep00101001_12 : Blocks := edgeBlocks% "full/vectors/00101001-E-0012.bin"
private noncomputable def ep00101001_13 : Blocks := edgeBlocks% "full/vectors/00101001-E-0013.bin"
noncomputable def ep00101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00101001_0 (Blocks.join ep00101001_1 ep00101001_2)) (Blocks.join (Blocks.join ep00101001_3 ep00101001_4) (Blocks.join ep00101001_5 ep00101001_6))) (Blocks.join (Blocks.join ep00101001_7 (Blocks.join ep00101001_8 ep00101001_9)) (Blocks.join (Blocks.join ep00101001_10 ep00101001_11) (Blocks.join ep00101001_12 ep00101001_13))))
private theorem idp00101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010100.list =
    C ((2:ℤ)^1920) * horner X vp00101001.list + horner X ep00101001.list := by
  exact edge_identity (B := (2:ℤ)^2762) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101001 : Branch 1 (-1279761639/64000000 : ℚ) vp0010100 := by
  apply branch_checked idp00101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1311761639/32000000 : ℚ) by norm_num]
  exact coverp00101001
theorem coverp0010100 : Covers (-1279761639/64000000 : ℚ) vp0010100 := join_branches bp00101000 bp00101001
private noncomputable def vp001010_0 : Blocks := edgeBlocks% "full/vectors/001010-V-0000.bin"
private noncomputable def vp001010_1 : Blocks := edgeBlocks% "full/vectors/001010-V-0001.bin"
private noncomputable def vp001010_2 : Blocks := edgeBlocks% "full/vectors/001010-V-0002.bin"
private noncomputable def vp001010_3 : Blocks := edgeBlocks% "full/vectors/001010-V-0003.bin"
private noncomputable def vp001010_4 : Blocks := edgeBlocks% "full/vectors/001010-V-0004.bin"
private noncomputable def vp001010_5 : Blocks := edgeBlocks% "full/vectors/001010-V-0005.bin"
private noncomputable def vp001010_6 : Blocks := edgeBlocks% "full/vectors/001010-V-0006.bin"
private noncomputable def vp001010_7 : Blocks := edgeBlocks% "full/vectors/001010-V-0007.bin"
private noncomputable def vp001010_8 : Blocks := edgeBlocks% "full/vectors/001010-V-0008.bin"
private noncomputable def vp001010_9 : Blocks := edgeBlocks% "full/vectors/001010-V-0009.bin"
private noncomputable def vp001010_10 : Blocks := edgeBlocks% "full/vectors/001010-V-0010.bin"
private noncomputable def vp001010_11 : Blocks := edgeBlocks% "full/vectors/001010-V-0011.bin"
private noncomputable def vp001010_12 : Blocks := edgeBlocks% "full/vectors/001010-V-0012.bin"
private noncomputable def vp001010_13 : Blocks := edgeBlocks% "full/vectors/001010-V-0013.bin"
private noncomputable def vp001010_14 : Blocks := edgeBlocks% "full/vectors/001010-V-0014.bin"
private noncomputable def vp001010_15 : Blocks := edgeBlocks% "full/vectors/001010-V-0015.bin"
private noncomputable def vp001010_16 : Blocks := edgeBlocks% "full/vectors/001010-V-0016.bin"
private noncomputable def vp001010_17 : Blocks := edgeBlocks% "full/vectors/001010-V-0017.bin"
private noncomputable def vp001010_18 : Blocks := edgeBlocks% "full/vectors/001010-V-0018.bin"
private noncomputable def vp001010_19 : Blocks := edgeBlocks% "full/vectors/001010-V-0019.bin"
private noncomputable def vp001010_20 : Blocks := edgeBlocks% "full/vectors/001010-V-0020.bin"
private noncomputable def vp001010_21 : Blocks := edgeBlocks% "full/vectors/001010-V-0021.bin"
private noncomputable def vp001010_22 : Blocks := edgeBlocks% "full/vectors/001010-V-0022.bin"
private noncomputable def vp001010_23 : Blocks := edgeBlocks% "full/vectors/001010-V-0023.bin"
private noncomputable def vp001010_24 : Blocks := edgeBlocks% "full/vectors/001010-V-0024.bin"
private noncomputable def vp001010_25 : Blocks := edgeBlocks% "full/vectors/001010-V-0025.bin"
private noncomputable def vp001010_26 : Blocks := edgeBlocks% "full/vectors/001010-V-0026.bin"
noncomputable def vp001010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001010_0 (Blocks.join vp001010_1 vp001010_2)) (Blocks.join vp001010_3 (Blocks.join vp001010_4 vp001010_5))) (Blocks.join (Blocks.join vp001010_6 (Blocks.join vp001010_7 vp001010_8)) (Blocks.join (Blocks.join vp001010_9 vp001010_10) (Blocks.join vp001010_11 vp001010_12)))) (Blocks.join (Blocks.join (Blocks.join vp001010_13 (Blocks.join vp001010_14 vp001010_15)) (Blocks.join (Blocks.join vp001010_16 vp001010_17) (Blocks.join vp001010_18 vp001010_19))) (Blocks.join (Blocks.join vp001010_20 (Blocks.join vp001010_21 vp001010_22)) (Blocks.join (Blocks.join vp001010_23 vp001010_24) (Blocks.join vp001010_25 vp001010_26)))))
private theorem bp0010100 : Branch 0 (-1279761639/128000000 : ℚ) vp001010 := by
  apply branch_left_normalized (c:=vp0010100) (k:=0) (m:=1735) (by decide +kernel)
  rw [show 2*(-1279761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/64000000 : ℚ) by norm_num]
  exact coverp0010100
private noncomputable def ep0010101_0 : Blocks := edgeBlocks% "full/vectors/0010101-E-0000.bin"
private noncomputable def ep0010101_1 : Blocks := edgeBlocks% "full/vectors/0010101-E-0001.bin"
private noncomputable def ep0010101_2 : Blocks := edgeBlocks% "full/vectors/0010101-E-0002.bin"
private noncomputable def ep0010101_3 : Blocks := edgeBlocks% "full/vectors/0010101-E-0003.bin"
private noncomputable def ep0010101_4 : Blocks := edgeBlocks% "full/vectors/0010101-E-0004.bin"
private noncomputable def ep0010101_5 : Blocks := edgeBlocks% "full/vectors/0010101-E-0005.bin"
private noncomputable def ep0010101_6 : Blocks := edgeBlocks% "full/vectors/0010101-E-0006.bin"
private noncomputable def ep0010101_7 : Blocks := edgeBlocks% "full/vectors/0010101-E-0007.bin"
private noncomputable def ep0010101_8 : Blocks := edgeBlocks% "full/vectors/0010101-E-0008.bin"
private noncomputable def ep0010101_9 : Blocks := edgeBlocks% "full/vectors/0010101-E-0009.bin"
private noncomputable def ep0010101_10 : Blocks := edgeBlocks% "full/vectors/0010101-E-0010.bin"
private noncomputable def ep0010101_11 : Blocks := edgeBlocks% "full/vectors/0010101-E-0011.bin"
private noncomputable def ep0010101_12 : Blocks := edgeBlocks% "full/vectors/0010101-E-0012.bin"
private noncomputable def ep0010101_13 : Blocks := edgeBlocks% "full/vectors/0010101-E-0013.bin"
private noncomputable def ep0010101_14 : Blocks := edgeBlocks% "full/vectors/0010101-E-0014.bin"
private noncomputable def ep0010101_15 : Blocks := edgeBlocks% "full/vectors/0010101-E-0015.bin"
private noncomputable def ep0010101_16 : Blocks := edgeBlocks% "full/vectors/0010101-E-0016.bin"
private noncomputable def ep0010101_17 : Blocks := edgeBlocks% "full/vectors/0010101-E-0017.bin"
private noncomputable def ep0010101_18 : Blocks := edgeBlocks% "full/vectors/0010101-E-0018.bin"
private noncomputable def ep0010101_19 : Blocks := edgeBlocks% "full/vectors/0010101-E-0019.bin"
private noncomputable def ep0010101_20 : Blocks := edgeBlocks% "full/vectors/0010101-E-0020.bin"
private noncomputable def ep0010101_21 : Blocks := edgeBlocks% "full/vectors/0010101-E-0021.bin"
private noncomputable def ep0010101_22 : Blocks := edgeBlocks% "full/vectors/0010101-E-0022.bin"
private noncomputable def ep0010101_23 : Blocks := edgeBlocks% "full/vectors/0010101-E-0023.bin"
private noncomputable def ep0010101_24 : Blocks := edgeBlocks% "full/vectors/0010101-E-0024.bin"
private noncomputable def ep0010101_25 : Blocks := edgeBlocks% "full/vectors/0010101-E-0025.bin"
private noncomputable def ep0010101_26 : Blocks := edgeBlocks% "full/vectors/0010101-E-0026.bin"
noncomputable def ep0010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0010101_0 (Blocks.join ep0010101_1 ep0010101_2)) (Blocks.join ep0010101_3 (Blocks.join ep0010101_4 ep0010101_5))) (Blocks.join (Blocks.join ep0010101_6 (Blocks.join ep0010101_7 ep0010101_8)) (Blocks.join (Blocks.join ep0010101_9 ep0010101_10) (Blocks.join ep0010101_11 ep0010101_12)))) (Blocks.join (Blocks.join (Blocks.join ep0010101_13 (Blocks.join ep0010101_14 ep0010101_15)) (Blocks.join (Blocks.join ep0010101_16 ep0010101_17) (Blocks.join ep0010101_18 ep0010101_19))) (Blocks.join (Blocks.join ep0010101_20 (Blocks.join ep0010101_21 ep0010101_22)) (Blocks.join (Blocks.join ep0010101_23 ep0010101_24) (Blocks.join ep0010101_25 ep0010101_26)))))
private def ptsp0010101 : List ℤ := [((2:ℤ)^3576+0),((2:ℤ)^3576+1)]
private theorem boundp0010101 : 2^vp001010.size*absSum vp001010.list + ((2:ℤ)^3727*absSum vp0010101.list+absSum ep0010101.list) < (2:ℤ)^5288 := by decide +kernel
private theorem pointp0010101_0 : fastHom 1 ((2:ℤ)^3576+0) vp001010 = ((2:ℤ)^3727)*vp0010101.subst ((2:ℤ)^3576+0)+ep0010101.subst ((2:ℤ)^3576+0) := by decide +kernel
private theorem pointp0010101_1 : fastHom 1 ((2:ℤ)^3576+1) vp001010 = ((2:ℤ)^3727)*vp0010101.subst ((2:ℤ)^3576+1)+ep0010101.subst ((2:ℤ)^3576+1) := by decide +kernel
private theorem checkp0010101 (x:ℤ) (hx:x ∈ ptsp0010101) : fastHom 1 x vp001010 = ((2:ℤ)^3727)*vp0010101.subst x+ep0010101.subst x := by
  simp only [ptsp0010101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0010101_0
  · exact pointp0010101_1
private theorem idp0010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010.list =
    C ((2:ℤ)^3727) * horner X vp0010101.list + horner X ep0010101.list := by
  apply edge_identity (B := (2:ℤ)^5288) (by decide) (by positivity) (by positivity) boundp0010101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0010101 (by decide +kernel)
  · have h : ptsp0010101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0010101.trans_le (by decide +kernel)
  · exact checkp0010101
private theorem bp0010101 : Branch 1 (-1279761639/128000000 : ℚ) vp001010 := by
  apply branch_checked idp0010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1343761639/64000000 : ℚ) by norm_num]
  exact coverp0010101
theorem coverp001010 : Covers (-1279761639/128000000 : ℚ) vp001010 := join_branches bp0010100 bp0010101
end NextProof.EdgeFull

