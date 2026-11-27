import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010011111111_0 : Blocks := edgeBlocks% "full/vectors/0010011111111-V-0000.bin"
noncomputable def vp0010011111111 : Blocks := vp0010011111111_0
theorem coverp0010011111111 : Covers (-1278761639/1000000 : ℚ) vp0010011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011111110_0 : Blocks := edgeBlocks% "full/vectors/0010011111110-V-0000.bin"
noncomputable def vp0010011111110 : Blocks := vp0010011111110_0
theorem coverp0010011111110 : Covers (-1277761639/1000000 : ℚ) vp0010011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111111_0 : Blocks := edgeBlocks% "full/vectors/001001111111-V-0000.bin"
noncomputable def vp001001111111 : Blocks := vp001001111111_0
private theorem bp0010011111110 : Branch 0 (-1277761639/2000000 : ℚ) vp001001111111 := by
  apply branch_left_normalized (c:=vp0010011111110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1277761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1277761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111110
private noncomputable def ep0010011111111_0 : Blocks := edgeBlocks% "full/vectors/0010011111111-E-0000.bin"
noncomputable def ep0010011111111 : Blocks := ep0010011111111_0
private theorem idp0010011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111111.list =
    C ((2:ℤ)^79) * horner X vp0010011111111.list + horner X ep0010011111111.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011111111 : Branch 1 (-1277761639/2000000 : ℚ) vp001001111111 := by
  apply branch_checked idp0010011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1277761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1278761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111111
theorem coverp001001111111 : Covers (-1277761639/2000000 : ℚ) vp001001111111 := join_branches bp0010011111110 bp0010011111111
private noncomputable def vp0010011111101_0 : Blocks := edgeBlocks% "full/vectors/0010011111101-V-0000.bin"
noncomputable def vp0010011111101 : Blocks := vp0010011111101_0
theorem coverp0010011111101 : Covers (-1276761639/1000000 : ℚ) vp0010011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011111100_0 : Blocks := edgeBlocks% "full/vectors/0010011111100-V-0000.bin"
noncomputable def vp0010011111100 : Blocks := vp0010011111100_0
theorem coverp0010011111100 : Covers (-1275761639/1000000 : ℚ) vp0010011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111110_0 : Blocks := edgeBlocks% "full/vectors/001001111110-V-0000.bin"
noncomputable def vp001001111110 : Blocks := vp001001111110_0
private theorem bp0010011111100 : Branch 0 (-1275761639/2000000 : ℚ) vp001001111110 := by
  apply branch_left_normalized (c:=vp0010011111100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1275761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1275761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111100
private noncomputable def ep0010011111101_0 : Blocks := edgeBlocks% "full/vectors/0010011111101-E-0000.bin"
noncomputable def ep0010011111101 : Blocks := ep0010011111101_0
private theorem idp0010011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111110.list =
    C ((2:ℤ)^80) * horner X vp0010011111101.list + horner X ep0010011111101.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011111101 : Branch 1 (-1275761639/2000000 : ℚ) vp001001111110 := by
  apply branch_checked idp0010011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1275761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1276761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111101
theorem coverp001001111110 : Covers (-1275761639/2000000 : ℚ) vp001001111110 := join_branches bp0010011111100 bp0010011111101
private noncomputable def vp00100111111_0 : Blocks := edgeBlocks% "full/vectors/00100111111-V-0000.bin"
private noncomputable def vp00100111111_1 : Blocks := edgeBlocks% "full/vectors/00100111111-V-0001.bin"
noncomputable def vp00100111111 : Blocks := (Blocks.join vp00100111111_0 vp00100111111_1)
private theorem bp001001111110 : Branch 0 (-1275761639/4000000 : ℚ) vp00100111111 := by
  apply branch_left_normalized (c:=vp001001111110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1275761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1275761639/2000000 : ℚ) by norm_num]
  exact coverp001001111110
private noncomputable def ep001001111111_0 : Blocks := edgeBlocks% "full/vectors/001001111111-E-0000.bin"
private noncomputable def ep001001111111_1 : Blocks := edgeBlocks% "full/vectors/001001111111-E-0001.bin"
noncomputable def ep001001111111 : Blocks := (Blocks.join ep001001111111_0 ep001001111111_1)
private theorem idp001001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111111.list =
    C ((2:ℤ)^142) * horner X vp001001111111.list + horner X ep001001111111.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001111111 : Branch 1 (-1275761639/4000000 : ℚ) vp00100111111 := by
  apply branch_checked idp001001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1275761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1277761639/2000000 : ℚ) by norm_num]
  exact coverp001001111111
theorem coverp00100111111 : Covers (-1275761639/4000000 : ℚ) vp00100111111 := join_branches bp001001111110 bp001001111111
private noncomputable def vp0010011111011_0 : Blocks := edgeBlocks% "full/vectors/0010011111011-V-0000.bin"
noncomputable def vp0010011111011 : Blocks := vp0010011111011_0
theorem coverp0010011111011 : Covers (-1274761639/1000000 : ℚ) vp0010011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011111010_0 : Blocks := edgeBlocks% "full/vectors/0010011111010-V-0000.bin"
noncomputable def vp0010011111010 : Blocks := vp0010011111010_0
theorem coverp0010011111010 : Covers (-1273761639/1000000 : ℚ) vp0010011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111101_0 : Blocks := edgeBlocks% "full/vectors/001001111101-V-0000.bin"
noncomputable def vp001001111101 : Blocks := vp001001111101_0
private theorem bp0010011111010 : Branch 0 (-1273761639/2000000 : ℚ) vp001001111101 := by
  apply branch_left_normalized (c:=vp0010011111010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1273761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1273761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111010
private noncomputable def ep0010011111011_0 : Blocks := edgeBlocks% "full/vectors/0010011111011-E-0000.bin"
noncomputable def ep0010011111011 : Blocks := ep0010011111011_0
private theorem idp0010011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111101.list =
    C ((2:ℤ)^80) * horner X vp0010011111011.list + horner X ep0010011111011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011111011 : Branch 1 (-1273761639/2000000 : ℚ) vp001001111101 := by
  apply branch_checked idp0010011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1273761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1274761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111011
theorem coverp001001111101 : Covers (-1273761639/2000000 : ℚ) vp001001111101 := join_branches bp0010011111010 bp0010011111011
private noncomputable def vp0010011111001_0 : Blocks := edgeBlocks% "full/vectors/0010011111001-V-0000.bin"
noncomputable def vp0010011111001 : Blocks := vp0010011111001_0
theorem coverp0010011111001 : Covers (-1272761639/1000000 : ℚ) vp0010011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011111000_0 : Blocks := edgeBlocks% "full/vectors/0010011111000-V-0000.bin"
noncomputable def vp0010011111000 : Blocks := vp0010011111000_0
theorem coverp0010011111000 : Covers (-1271761639/1000000 : ℚ) vp0010011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111100_0 : Blocks := edgeBlocks% "full/vectors/001001111100-V-0000.bin"
noncomputable def vp001001111100 : Blocks := vp001001111100_0
private theorem bp0010011111000 : Branch 0 (-1271761639/2000000 : ℚ) vp001001111100 := by
  apply branch_left_normalized (c:=vp0010011111000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1271761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1271761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111000
private noncomputable def ep0010011111001_0 : Blocks := edgeBlocks% "full/vectors/0010011111001-E-0000.bin"
noncomputable def ep0010011111001 : Blocks := ep0010011111001_0
private theorem idp0010011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111100.list =
    C ((2:ℤ)^80) * horner X vp0010011111001.list + horner X ep0010011111001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011111001 : Branch 1 (-1271761639/2000000 : ℚ) vp001001111100 := by
  apply branch_checked idp0010011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1271761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1272761639/1000000 : ℚ) by norm_num]
  exact coverp0010011111001
theorem coverp001001111100 : Covers (-1271761639/2000000 : ℚ) vp001001111100 := join_branches bp0010011111000 bp0010011111001
private noncomputable def vp00100111110_0 : Blocks := edgeBlocks% "full/vectors/00100111110-V-0000.bin"
private noncomputable def vp00100111110_1 : Blocks := edgeBlocks% "full/vectors/00100111110-V-0001.bin"
noncomputable def vp00100111110 : Blocks := (Blocks.join vp00100111110_0 vp00100111110_1)
private theorem bp001001111100 : Branch 0 (-1271761639/4000000 : ℚ) vp00100111110 := by
  apply branch_left_normalized (c:=vp001001111100) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1271761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1271761639/2000000 : ℚ) by norm_num]
  exact coverp001001111100
private noncomputable def ep001001111101_0 : Blocks := edgeBlocks% "full/vectors/001001111101-E-0000.bin"
private noncomputable def ep001001111101_1 : Blocks := edgeBlocks% "full/vectors/001001111101-E-0001.bin"
noncomputable def ep001001111101 : Blocks := (Blocks.join ep001001111101_0 ep001001111101_1)
private theorem idp001001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111110.list =
    C ((2:ℤ)^142) * horner X vp001001111101.list + horner X ep001001111101.list := by
  exact edge_identity (B := (2:ℤ)^287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001111101 : Branch 1 (-1271761639/4000000 : ℚ) vp00100111110 := by
  apply branch_checked idp001001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1271761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1273761639/2000000 : ℚ) by norm_num]
  exact coverp001001111101
theorem coverp00100111110 : Covers (-1271761639/4000000 : ℚ) vp00100111110 := join_branches bp001001111100 bp001001111101
private noncomputable def vp0010011111_0 : Blocks := edgeBlocks% "full/vectors/0010011111-V-0000.bin"
private noncomputable def vp0010011111_1 : Blocks := edgeBlocks% "full/vectors/0010011111-V-0001.bin"
noncomputable def vp0010011111 : Blocks := (Blocks.join vp0010011111_0 vp0010011111_1)
private theorem bp00100111110 : Branch 0 (-1271761639/8000000 : ℚ) vp0010011111 := by
  apply branch_left_normalized (c:=vp00100111110) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-1271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1271761639/4000000 : ℚ) by norm_num]
  exact coverp00100111110
private noncomputable def ep00100111111_0 : Blocks := edgeBlocks% "full/vectors/00100111111-E-0000.bin"
private noncomputable def ep00100111111_1 : Blocks := edgeBlocks% "full/vectors/00100111111-E-0001.bin"
noncomputable def ep00100111111 : Blocks := (Blocks.join ep00100111111_0 ep00100111111_1)
private theorem idp00100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011111.list =
    C ((2:ℤ)^263) * horner X vp00100111111.list + horner X ep00100111111.list := by
  exact edge_identity (B := (2:ℤ)^456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100111111 : Branch 1 (-1271761639/8000000 : ℚ) vp0010011111 := by
  apply branch_checked idp00100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1275761639/4000000 : ℚ) by norm_num]
  exact coverp00100111111
theorem coverp0010011111 : Covers (-1271761639/8000000 : ℚ) vp0010011111 := join_branches bp00100111110 bp00100111111
private noncomputable def vp0010011110111_0 : Blocks := edgeBlocks% "full/vectors/0010011110111-V-0000.bin"
noncomputable def vp0010011110111 : Blocks := vp0010011110111_0
theorem coverp0010011110111 : Covers (-1270761639/1000000 : ℚ) vp0010011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011110110_0 : Blocks := edgeBlocks% "full/vectors/0010011110110-V-0000.bin"
noncomputable def vp0010011110110 : Blocks := vp0010011110110_0
theorem coverp0010011110110 : Covers (-1269761639/1000000 : ℚ) vp0010011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111011_0 : Blocks := edgeBlocks% "full/vectors/001001111011-V-0000.bin"
noncomputable def vp001001111011 : Blocks := vp001001111011_0
private theorem bp0010011110110 : Branch 0 (-1269761639/2000000 : ℚ) vp001001111011 := by
  apply branch_left_normalized (c:=vp0010011110110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1269761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1269761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110110
private noncomputable def ep0010011110111_0 : Blocks := edgeBlocks% "full/vectors/0010011110111-E-0000.bin"
noncomputable def ep0010011110111 : Blocks := ep0010011110111_0
private theorem idp0010011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111011.list =
    C ((2:ℤ)^83) * horner X vp0010011110111.list + horner X ep0010011110111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011110111 : Branch 1 (-1269761639/2000000 : ℚ) vp001001111011 := by
  apply branch_checked idp0010011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1269761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1270761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110111
theorem coverp001001111011 : Covers (-1269761639/2000000 : ℚ) vp001001111011 := join_branches bp0010011110110 bp0010011110111
private noncomputable def vp0010011110101_0 : Blocks := edgeBlocks% "full/vectors/0010011110101-V-0000.bin"
noncomputable def vp0010011110101 : Blocks := vp0010011110101_0
theorem coverp0010011110101 : Covers (-1268761639/1000000 : ℚ) vp0010011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011110100_0 : Blocks := edgeBlocks% "full/vectors/0010011110100-V-0000.bin"
noncomputable def vp0010011110100 : Blocks := vp0010011110100_0
theorem coverp0010011110100 : Covers (-1267761639/1000000 : ℚ) vp0010011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111010_0 : Blocks := edgeBlocks% "full/vectors/001001111010-V-0000.bin"
noncomputable def vp001001111010 : Blocks := vp001001111010_0
private theorem bp0010011110100 : Branch 0 (-1267761639/2000000 : ℚ) vp001001111010 := by
  apply branch_left_normalized (c:=vp0010011110100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1267761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1267761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110100
private noncomputable def ep0010011110101_0 : Blocks := edgeBlocks% "full/vectors/0010011110101-E-0000.bin"
noncomputable def ep0010011110101 : Blocks := ep0010011110101_0
private theorem idp0010011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111010.list =
    C ((2:ℤ)^79) * horner X vp0010011110101.list + horner X ep0010011110101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011110101 : Branch 1 (-1267761639/2000000 : ℚ) vp001001111010 := by
  apply branch_checked idp0010011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1267761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1268761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110101
theorem coverp001001111010 : Covers (-1267761639/2000000 : ℚ) vp001001111010 := join_branches bp0010011110100 bp0010011110101
private noncomputable def vp00100111101_0 : Blocks := edgeBlocks% "full/vectors/00100111101-V-0000.bin"
private noncomputable def vp00100111101_1 : Blocks := edgeBlocks% "full/vectors/00100111101-V-0001.bin"
noncomputable def vp00100111101 : Blocks := (Blocks.join vp00100111101_0 vp00100111101_1)
private theorem bp001001111010 : Branch 0 (-1267761639/4000000 : ℚ) vp00100111101 := by
  apply branch_left_normalized (c:=vp001001111010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1267761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1267761639/2000000 : ℚ) by norm_num]
  exact coverp001001111010
private noncomputable def ep001001111011_0 : Blocks := edgeBlocks% "full/vectors/001001111011-E-0000.bin"
private noncomputable def ep001001111011_1 : Blocks := edgeBlocks% "full/vectors/001001111011-E-0001.bin"
noncomputable def ep001001111011 : Blocks := (Blocks.join ep001001111011_0 ep001001111011_1)
private theorem idp001001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111101.list =
    C ((2:ℤ)^142) * horner X vp001001111011.list + horner X ep001001111011.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001111011 : Branch 1 (-1267761639/4000000 : ℚ) vp00100111101 := by
  apply branch_checked idp001001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1267761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1269761639/2000000 : ℚ) by norm_num]
  exact coverp001001111011
theorem coverp00100111101 : Covers (-1267761639/4000000 : ℚ) vp00100111101 := join_branches bp001001111010 bp001001111011
private noncomputable def vp0010011110011_0 : Blocks := edgeBlocks% "full/vectors/0010011110011-V-0000.bin"
noncomputable def vp0010011110011 : Blocks := vp0010011110011_0
theorem coverp0010011110011 : Covers (-1266761639/1000000 : ℚ) vp0010011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011110010_0 : Blocks := edgeBlocks% "full/vectors/0010011110010-V-0000.bin"
noncomputable def vp0010011110010 : Blocks := vp0010011110010_0
theorem coverp0010011110010 : Covers (-1265761639/1000000 : ℚ) vp0010011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111001_0 : Blocks := edgeBlocks% "full/vectors/001001111001-V-0000.bin"
noncomputable def vp001001111001 : Blocks := vp001001111001_0
private theorem bp0010011110010 : Branch 0 (-1265761639/2000000 : ℚ) vp001001111001 := by
  apply branch_left_normalized (c:=vp0010011110010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1265761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1265761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110010
private noncomputable def ep0010011110011_0 : Blocks := edgeBlocks% "full/vectors/0010011110011-E-0000.bin"
noncomputable def ep0010011110011 : Blocks := ep0010011110011_0
private theorem idp0010011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111001.list =
    C ((2:ℤ)^78) * horner X vp0010011110011.list + horner X ep0010011110011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011110011 : Branch 1 (-1265761639/2000000 : ℚ) vp001001111001 := by
  apply branch_checked idp0010011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1265761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1266761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110011
theorem coverp001001111001 : Covers (-1265761639/2000000 : ℚ) vp001001111001 := join_branches bp0010011110010 bp0010011110011
private noncomputable def vp0010011110001_0 : Blocks := edgeBlocks% "full/vectors/0010011110001-V-0000.bin"
noncomputable def vp0010011110001 : Blocks := vp0010011110001_0
theorem coverp0010011110001 : Covers (-1264761639/1000000 : ℚ) vp0010011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011110000_0 : Blocks := edgeBlocks% "full/vectors/0010011110000-V-0000.bin"
noncomputable def vp0010011110000 : Blocks := vp0010011110000_0
theorem coverp0010011110000 : Covers (-1263761639/1000000 : ℚ) vp0010011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001111000_0 : Blocks := edgeBlocks% "full/vectors/001001111000-V-0000.bin"
noncomputable def vp001001111000 : Blocks := vp001001111000_0
private theorem bp0010011110000 : Branch 0 (-1263761639/2000000 : ℚ) vp001001111000 := by
  apply branch_left_normalized (c:=vp0010011110000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1263761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1263761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110000
private noncomputable def ep0010011110001_0 : Blocks := edgeBlocks% "full/vectors/0010011110001-E-0000.bin"
noncomputable def ep0010011110001 : Blocks := ep0010011110001_0
private theorem idp0010011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111000.list =
    C ((2:ℤ)^78) * horner X vp0010011110001.list + horner X ep0010011110001.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011110001 : Branch 1 (-1263761639/2000000 : ℚ) vp001001111000 := by
  apply branch_checked idp0010011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1263761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1264761639/1000000 : ℚ) by norm_num]
  exact coverp0010011110001
theorem coverp001001111000 : Covers (-1263761639/2000000 : ℚ) vp001001111000 := join_branches bp0010011110000 bp0010011110001
private noncomputable def vp00100111100_0 : Blocks := edgeBlocks% "full/vectors/00100111100-V-0000.bin"
private noncomputable def vp00100111100_1 : Blocks := edgeBlocks% "full/vectors/00100111100-V-0001.bin"
noncomputable def vp00100111100 : Blocks := (Blocks.join vp00100111100_0 vp00100111100_1)
private theorem bp001001111000 : Branch 0 (-1263761639/4000000 : ℚ) vp00100111100 := by
  apply branch_left_normalized (c:=vp001001111000) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1263761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1263761639/2000000 : ℚ) by norm_num]
  exact coverp001001111000
private noncomputable def ep001001111001_0 : Blocks := edgeBlocks% "full/vectors/001001111001-E-0000.bin"
private noncomputable def ep001001111001_1 : Blocks := edgeBlocks% "full/vectors/001001111001-E-0001.bin"
noncomputable def ep001001111001 : Blocks := (Blocks.join ep001001111001_0 ep001001111001_1)
private theorem idp001001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111100.list =
    C ((2:ℤ)^139) * horner X vp001001111001.list + horner X ep001001111001.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001111001 : Branch 1 (-1263761639/4000000 : ℚ) vp00100111100 := by
  apply branch_checked idp001001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1263761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1265761639/2000000 : ℚ) by norm_num]
  exact coverp001001111001
theorem coverp00100111100 : Covers (-1263761639/4000000 : ℚ) vp00100111100 := join_branches bp001001111000 bp001001111001
private noncomputable def vp0010011110_0 : Blocks := edgeBlocks% "full/vectors/0010011110-V-0000.bin"
private noncomputable def vp0010011110_1 : Blocks := edgeBlocks% "full/vectors/0010011110-V-0001.bin"
noncomputable def vp0010011110 : Blocks := (Blocks.join vp0010011110_0 vp0010011110_1)
private theorem bp00100111100 : Branch 0 (-1263761639/8000000 : ℚ) vp0010011110 := by
  apply branch_left_normalized (c:=vp00100111100) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-1263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1263761639/4000000 : ℚ) by norm_num]
  exact coverp00100111100
private noncomputable def ep00100111101_0 : Blocks := edgeBlocks% "full/vectors/00100111101-E-0000.bin"
private noncomputable def ep00100111101_1 : Blocks := edgeBlocks% "full/vectors/00100111101-E-0001.bin"
noncomputable def ep00100111101 : Blocks := (Blocks.join ep00100111101_0 ep00100111101_1)
private theorem idp00100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011110.list =
    C ((2:ℤ)^257) * horner X vp00100111101.list + horner X ep00100111101.list := by
  exact edge_identity (B := (2:ℤ)^450) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100111101 : Branch 1 (-1263761639/8000000 : ℚ) vp0010011110 := by
  apply branch_checked idp00100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1267761639/4000000 : ℚ) by norm_num]
  exact coverp00100111101
theorem coverp0010011110 : Covers (-1263761639/8000000 : ℚ) vp0010011110 := join_branches bp00100111100 bp00100111101
private noncomputable def vp001001111_0 : Blocks := edgeBlocks% "full/vectors/001001111-V-0000.bin"
private noncomputable def vp001001111_1 : Blocks := edgeBlocks% "full/vectors/001001111-V-0001.bin"
private noncomputable def vp001001111_2 : Blocks := edgeBlocks% "full/vectors/001001111-V-0002.bin"
private noncomputable def vp001001111_3 : Blocks := edgeBlocks% "full/vectors/001001111-V-0003.bin"
noncomputable def vp001001111 : Blocks := (Blocks.join (Blocks.join vp001001111_0 vp001001111_1) (Blocks.join vp001001111_2 vp001001111_3))
private theorem bp0010011110 : Branch 0 (-1263761639/16000000 : ℚ) vp001001111 := by
  apply branch_left_normalized (c:=vp0010011110) (k:=0) (m:=238) (by decide +kernel)
  rw [show 2*(-1263761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1263761639/8000000 : ℚ) by norm_num]
  exact coverp0010011110
private noncomputable def ep0010011111_0 : Blocks := edgeBlocks% "full/vectors/0010011111-E-0000.bin"
private noncomputable def ep0010011111_1 : Blocks := edgeBlocks% "full/vectors/0010011111-E-0001.bin"
private noncomputable def ep0010011111_2 : Blocks := edgeBlocks% "full/vectors/0010011111-E-0002.bin"
private noncomputable def ep0010011111_3 : Blocks := edgeBlocks% "full/vectors/0010011111-E-0003.bin"
noncomputable def ep0010011111 : Blocks := (Blocks.join (Blocks.join ep0010011111_0 ep0010011111_1) (Blocks.join ep0010011111_2 ep0010011111_3))
private theorem idp0010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001111.list =
    C ((2:ℤ)^500) * horner X vp0010011111.list + horner X ep0010011111.list := by
  exact edge_identity (B := (2:ℤ)^786) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011111 : Branch 1 (-1263761639/16000000 : ℚ) vp001001111 := by
  apply branch_checked idp0010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1263761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1271761639/8000000 : ℚ) by norm_num]
  exact coverp0010011111
theorem coverp001001111 : Covers (-1263761639/16000000 : ℚ) vp001001111 := join_branches bp0010011110 bp0010011111
private noncomputable def vp001001110111_0 : Blocks := edgeBlocks% "full/vectors/001001110111-V-0000.bin"
noncomputable def vp001001110111 : Blocks := vp001001110111_0
theorem coverp001001110111 : Covers (-1261761639/2000000 : ℚ) vp001001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp001001110110_0 : Blocks := edgeBlocks% "full/vectors/001001110110-V-0000.bin"
noncomputable def vp001001110110 : Blocks := vp001001110110_0
theorem coverp001001110110 : Covers (-1259761639/2000000 : ℚ) vp001001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00100111011_0 : Blocks := edgeBlocks% "full/vectors/00100111011-V-0000.bin"
noncomputable def vp00100111011 : Blocks := vp00100111011_0
private theorem bp001001110110 : Branch 0 (-1259761639/4000000 : ℚ) vp00100111011 := by
  apply branch_left_normalized (c:=vp001001110110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1259761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1259761639/2000000 : ℚ) by norm_num]
  exact coverp001001110110
private noncomputable def ep001001110111_0 : Blocks := edgeBlocks% "full/vectors/001001110111-E-0000.bin"
noncomputable def ep001001110111 : Blocks := ep001001110111_0
private theorem idp001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111011.list =
    C ((2:ℤ)^138) * horner X vp001001110111.list + horner X ep001001110111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001110111 : Branch 1 (-1259761639/4000000 : ℚ) vp00100111011 := by
  apply branch_checked idp001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1259761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1261761639/2000000 : ℚ) by norm_num]
  exact coverp001001110111
theorem coverp00100111011 : Covers (-1259761639/4000000 : ℚ) vp00100111011 := join_branches bp001001110110 bp001001110111
private noncomputable def vp001001110101_0 : Blocks := edgeBlocks% "full/vectors/001001110101-V-0000.bin"
noncomputable def vp001001110101 : Blocks := vp001001110101_0
theorem coverp001001110101 : Covers (-1257761639/2000000 : ℚ) vp001001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001001110100_0 : Blocks := edgeBlocks% "full/vectors/001001110100-V-0000.bin"
noncomputable def vp001001110100 : Blocks := vp001001110100_0
theorem coverp001001110100 : Covers (-1255761639/2000000 : ℚ) vp001001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00100111010_0 : Blocks := edgeBlocks% "full/vectors/00100111010-V-0000.bin"
noncomputable def vp00100111010 : Blocks := vp00100111010_0
private theorem bp001001110100 : Branch 0 (-1255761639/4000000 : ℚ) vp00100111010 := by
  apply branch_left_normalized (c:=vp001001110100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1255761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1255761639/2000000 : ℚ) by norm_num]
  exact coverp001001110100
private noncomputable def ep001001110101_0 : Blocks := edgeBlocks% "full/vectors/001001110101-E-0000.bin"
noncomputable def ep001001110101 : Blocks := ep001001110101_0
private theorem idp001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111010.list =
    C ((2:ℤ)^138) * horner X vp001001110101.list + horner X ep001001110101.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001110101 : Branch 1 (-1255761639/4000000 : ℚ) vp00100111010 := by
  apply branch_checked idp001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1255761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1257761639/2000000 : ℚ) by norm_num]
  exact coverp001001110101
theorem coverp00100111010 : Covers (-1255761639/4000000 : ℚ) vp00100111010 := join_branches bp001001110100 bp001001110101
private noncomputable def vp0010011101_0 : Blocks := edgeBlocks% "full/vectors/0010011101-V-0000.bin"
private noncomputable def vp0010011101_1 : Blocks := edgeBlocks% "full/vectors/0010011101-V-0001.bin"
noncomputable def vp0010011101 : Blocks := (Blocks.join vp0010011101_0 vp0010011101_1)
private theorem bp00100111010 : Branch 0 (-1255761639/8000000 : ℚ) vp0010011101 := by
  apply branch_left_normalized (c:=vp00100111010) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1255761639/4000000 : ℚ) by norm_num]
  exact coverp00100111010
private noncomputable def ep00100111011_0 : Blocks := edgeBlocks% "full/vectors/00100111011-E-0000.bin"
private noncomputable def ep00100111011_1 : Blocks := edgeBlocks% "full/vectors/00100111011-E-0001.bin"
noncomputable def ep00100111011 : Blocks := (Blocks.join ep00100111011_0 ep00100111011_1)
private theorem idp00100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011101.list =
    C ((2:ℤ)^260) * horner X vp00100111011.list + horner X ep00100111011.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100111011 : Branch 1 (-1255761639/8000000 : ℚ) vp0010011101 := by
  apply branch_checked idp00100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1259761639/4000000 : ℚ) by norm_num]
  exact coverp00100111011
theorem coverp0010011101 : Covers (-1255761639/8000000 : ℚ) vp0010011101 := join_branches bp00100111010 bp00100111011
private noncomputable def vp001001110011_0 : Blocks := edgeBlocks% "full/vectors/001001110011-V-0000.bin"
noncomputable def vp001001110011 : Blocks := vp001001110011_0
theorem coverp001001110011 : Covers (-1253761639/2000000 : ℚ) vp001001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp001001110010_0 : Blocks := edgeBlocks% "full/vectors/001001110010-V-0000.bin"
noncomputable def vp001001110010 : Blocks := vp001001110010_0
theorem coverp001001110010 : Covers (-1251761639/2000000 : ℚ) vp001001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00100111001_0 : Blocks := edgeBlocks% "full/vectors/00100111001-V-0000.bin"
noncomputable def vp00100111001 : Blocks := vp00100111001_0
private theorem bp001001110010 : Branch 0 (-1251761639/4000000 : ℚ) vp00100111001 := by
  apply branch_left_normalized (c:=vp001001110010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1251761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1251761639/2000000 : ℚ) by norm_num]
  exact coverp001001110010
private noncomputable def ep001001110011_0 : Blocks := edgeBlocks% "full/vectors/001001110011-E-0000.bin"
noncomputable def ep001001110011 : Blocks := ep001001110011_0
private theorem idp001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111001.list =
    C ((2:ℤ)^139) * horner X vp001001110011.list + horner X ep001001110011.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001110011 : Branch 1 (-1251761639/4000000 : ℚ) vp00100111001 := by
  apply branch_checked idp001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1251761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1253761639/2000000 : ℚ) by norm_num]
  exact coverp001001110011
theorem coverp00100111001 : Covers (-1251761639/4000000 : ℚ) vp00100111001 := join_branches bp001001110010 bp001001110011
private noncomputable def vp001001110001_0 : Blocks := edgeBlocks% "full/vectors/001001110001-V-0000.bin"
noncomputable def vp001001110001 : Blocks := vp001001110001_0
theorem coverp001001110001 : Covers (-1249761639/2000000 : ℚ) vp001001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp001001110000_0 : Blocks := edgeBlocks% "full/vectors/001001110000-V-0000.bin"
noncomputable def vp001001110000 : Blocks := vp001001110000_0
theorem coverp001001110000 : Covers (-1247761639/2000000 : ℚ) vp001001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00100111000_0 : Blocks := edgeBlocks% "full/vectors/00100111000-V-0000.bin"
noncomputable def vp00100111000 : Blocks := vp00100111000_0
private theorem bp001001110000 : Branch 0 (-1247761639/4000000 : ℚ) vp00100111000 := by
  apply branch_left_normalized (c:=vp001001110000) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1247761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1247761639/2000000 : ℚ) by norm_num]
  exact coverp001001110000
private noncomputable def ep001001110001_0 : Blocks := edgeBlocks% "full/vectors/001001110001-E-0000.bin"
noncomputable def ep001001110001 : Blocks := ep001001110001_0
private theorem idp001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111000.list =
    C ((2:ℤ)^138) * horner X vp001001110001.list + horner X ep001001110001.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001110001 : Branch 1 (-1247761639/4000000 : ℚ) vp00100111000 := by
  apply branch_checked idp001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1247761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1249761639/2000000 : ℚ) by norm_num]
  exact coverp001001110001
theorem coverp00100111000 : Covers (-1247761639/4000000 : ℚ) vp00100111000 := join_branches bp001001110000 bp001001110001
private noncomputable def vp0010011100_0 : Blocks := edgeBlocks% "full/vectors/0010011100-V-0000.bin"
private noncomputable def vp0010011100_1 : Blocks := edgeBlocks% "full/vectors/0010011100-V-0001.bin"
noncomputable def vp0010011100 : Blocks := (Blocks.join vp0010011100_0 vp0010011100_1)
private theorem bp00100111000 : Branch 0 (-1247761639/8000000 : ℚ) vp0010011100 := by
  apply branch_left_normalized (c:=vp00100111000) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1247761639/4000000 : ℚ) by norm_num]
  exact coverp00100111000
private noncomputable def ep00100111001_0 : Blocks := edgeBlocks% "full/vectors/00100111001-E-0000.bin"
private noncomputable def ep00100111001_1 : Blocks := edgeBlocks% "full/vectors/00100111001-E-0001.bin"
noncomputable def ep00100111001 : Blocks := (Blocks.join ep00100111001_0 ep00100111001_1)
private theorem idp00100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011100.list =
    C ((2:ℤ)^262) * horner X vp00100111001.list + horner X ep00100111001.list := by
  exact edge_identity (B := (2:ℤ)^447) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100111001 : Branch 1 (-1247761639/8000000 : ℚ) vp0010011100 := by
  apply branch_checked idp00100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1251761639/4000000 : ℚ) by norm_num]
  exact coverp00100111001
theorem coverp0010011100 : Covers (-1247761639/8000000 : ℚ) vp0010011100 := join_branches bp00100111000 bp00100111001
private noncomputable def vp001001110_0 : Blocks := edgeBlocks% "full/vectors/001001110-V-0000.bin"
private noncomputable def vp001001110_1 : Blocks := edgeBlocks% "full/vectors/001001110-V-0001.bin"
private noncomputable def vp001001110_2 : Blocks := edgeBlocks% "full/vectors/001001110-V-0002.bin"
private noncomputable def vp001001110_3 : Blocks := edgeBlocks% "full/vectors/001001110-V-0003.bin"
noncomputable def vp001001110 : Blocks := (Blocks.join (Blocks.join vp001001110_0 vp001001110_1) (Blocks.join vp001001110_2 vp001001110_3))
private theorem bp0010011100 : Branch 0 (-1247761639/16000000 : ℚ) vp001001110 := by
  apply branch_left_normalized (c:=vp0010011100) (k:=0) (m:=238) (by decide +kernel)
  rw [show 2*(-1247761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1247761639/8000000 : ℚ) by norm_num]
  exact coverp0010011100
private noncomputable def ep0010011101_0 : Blocks := edgeBlocks% "full/vectors/0010011101-E-0000.bin"
private noncomputable def ep0010011101_1 : Blocks := edgeBlocks% "full/vectors/0010011101-E-0001.bin"
private noncomputable def ep0010011101_2 : Blocks := edgeBlocks% "full/vectors/0010011101-E-0002.bin"
private noncomputable def ep0010011101_3 : Blocks := edgeBlocks% "full/vectors/0010011101-E-0003.bin"
noncomputable def ep0010011101 : Blocks := (Blocks.join (Blocks.join ep0010011101_0 ep0010011101_1) (Blocks.join ep0010011101_2 ep0010011101_3))
private theorem idp0010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001110.list =
    C ((2:ℤ)^505) * horner X vp0010011101.list + horner X ep0010011101.list := by
  exact edge_identity (B := (2:ℤ)^785) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011101 : Branch 1 (-1247761639/16000000 : ℚ) vp001001110 := by
  apply branch_checked idp0010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1247761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1255761639/8000000 : ℚ) by norm_num]
  exact coverp0010011101
theorem coverp001001110 : Covers (-1247761639/16000000 : ℚ) vp001001110 := join_branches bp0010011100 bp0010011101
private noncomputable def vp00100111_0 : Blocks := edgeBlocks% "full/vectors/00100111-V-0000.bin"
private noncomputable def vp00100111_1 : Blocks := edgeBlocks% "full/vectors/00100111-V-0001.bin"
private noncomputable def vp00100111_2 : Blocks := edgeBlocks% "full/vectors/00100111-V-0002.bin"
private noncomputable def vp00100111_3 : Blocks := edgeBlocks% "full/vectors/00100111-V-0003.bin"
private noncomputable def vp00100111_4 : Blocks := edgeBlocks% "full/vectors/00100111-V-0004.bin"
private noncomputable def vp00100111_5 : Blocks := edgeBlocks% "full/vectors/00100111-V-0005.bin"
private noncomputable def vp00100111_6 : Blocks := edgeBlocks% "full/vectors/00100111-V-0006.bin"
noncomputable def vp00100111 : Blocks := (Blocks.join (Blocks.join vp00100111_0 (Blocks.join vp00100111_1 vp00100111_2)) (Blocks.join (Blocks.join vp00100111_3 vp00100111_4) (Blocks.join vp00100111_5 vp00100111_6)))
private theorem bp001001110 : Branch 0 (-1247761639/32000000 : ℚ) vp00100111 := by
  apply branch_left_normalized (c:=vp001001110) (k:=0) (m:=458) (by decide +kernel)
  rw [show 2*(-1247761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1247761639/16000000 : ℚ) by norm_num]
  exact coverp001001110
private noncomputable def ep001001111_0 : Blocks := edgeBlocks% "full/vectors/001001111-E-0000.bin"
private noncomputable def ep001001111_1 : Blocks := edgeBlocks% "full/vectors/001001111-E-0001.bin"
private noncomputable def ep001001111_2 : Blocks := edgeBlocks% "full/vectors/001001111-E-0002.bin"
private noncomputable def ep001001111_3 : Blocks := edgeBlocks% "full/vectors/001001111-E-0003.bin"
private noncomputable def ep001001111_4 : Blocks := edgeBlocks% "full/vectors/001001111-E-0004.bin"
private noncomputable def ep001001111_5 : Blocks := edgeBlocks% "full/vectors/001001111-E-0005.bin"
private noncomputable def ep001001111_6 : Blocks := edgeBlocks% "full/vectors/001001111-E-0006.bin"
noncomputable def ep001001111 : Blocks := (Blocks.join (Blocks.join ep001001111_0 (Blocks.join ep001001111_1 ep001001111_2)) (Blocks.join (Blocks.join ep001001111_3 ep001001111_4) (Blocks.join ep001001111_5 ep001001111_6)))
private theorem idp001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100111.list =
    C ((2:ℤ)^984) * horner X vp001001111.list + horner X ep001001111.list := by
  exact edge_identity (B := (2:ℤ)^1456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001111 : Branch 1 (-1247761639/32000000 : ℚ) vp00100111 := by
  apply branch_checked idp001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1247761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1263761639/16000000 : ℚ) by norm_num]
  exact coverp001001111
theorem coverp00100111 : Covers (-1247761639/32000000 : ℚ) vp00100111 := join_branches bp001001110 bp001001111
private noncomputable def vp001001101111_0 : Blocks := edgeBlocks% "full/vectors/001001101111-V-0000.bin"
noncomputable def vp001001101111 : Blocks := vp001001101111_0
theorem coverp001001101111 : Covers (-1245761639/2000000 : ℚ) vp001001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001001101110_0 : Blocks := edgeBlocks% "full/vectors/001001101110-V-0000.bin"
noncomputable def vp001001101110 : Blocks := vp001001101110_0
theorem coverp001001101110 : Covers (-1243761639/2000000 : ℚ) vp001001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00100110111_0 : Blocks := edgeBlocks% "full/vectors/00100110111-V-0000.bin"
noncomputable def vp00100110111 : Blocks := vp00100110111_0
private theorem bp001001101110 : Branch 0 (-1243761639/4000000 : ℚ) vp00100110111 := by
  apply branch_left_normalized (c:=vp001001101110) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1243761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1243761639/2000000 : ℚ) by norm_num]
  exact coverp001001101110
private noncomputable def ep001001101111_0 : Blocks := edgeBlocks% "full/vectors/001001101111-E-0000.bin"
noncomputable def ep001001101111 : Blocks := ep001001101111_0
private theorem idp001001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110111.list =
    C ((2:ℤ)^140) * horner X vp001001101111.list + horner X ep001001101111.list := by
  exact edge_identity (B := (2:ℤ)^278) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001101111 : Branch 1 (-1243761639/4000000 : ℚ) vp00100110111 := by
  apply branch_checked idp001001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1243761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1245761639/2000000 : ℚ) by norm_num]
  exact coverp001001101111
theorem coverp00100110111 : Covers (-1243761639/4000000 : ℚ) vp00100110111 := join_branches bp001001101110 bp001001101111
private noncomputable def vp001001101101_0 : Blocks := edgeBlocks% "full/vectors/001001101101-V-0000.bin"
noncomputable def vp001001101101 : Blocks := vp001001101101_0
theorem coverp001001101101 : Covers (-1241761639/2000000 : ℚ) vp001001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001001101100_0 : Blocks := edgeBlocks% "full/vectors/001001101100-V-0000.bin"
noncomputable def vp001001101100 : Blocks := vp001001101100_0
theorem coverp001001101100 : Covers (-1239761639/2000000 : ℚ) vp001001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00100110110_0 : Blocks := edgeBlocks% "full/vectors/00100110110-V-0000.bin"
private noncomputable def vp00100110110_1 : Blocks := edgeBlocks% "full/vectors/00100110110-V-0001.bin"
noncomputable def vp00100110110 : Blocks := (Blocks.join vp00100110110_0 vp00100110110_1)
private theorem bp001001101100 : Branch 0 (-1239761639/4000000 : ℚ) vp00100110110 := by
  apply branch_left_normalized (c:=vp001001101100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1239761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1239761639/2000000 : ℚ) by norm_num]
  exact coverp001001101100
private noncomputable def ep001001101101_0 : Blocks := edgeBlocks% "full/vectors/001001101101-E-0000.bin"
private noncomputable def ep001001101101_1 : Blocks := edgeBlocks% "full/vectors/001001101101-E-0001.bin"
noncomputable def ep001001101101 : Blocks := (Blocks.join ep001001101101_0 ep001001101101_1)
private theorem idp001001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110110.list =
    C ((2:ℤ)^143) * horner X vp001001101101.list + horner X ep001001101101.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001101101 : Branch 1 (-1239761639/4000000 : ℚ) vp00100110110 := by
  apply branch_checked idp001001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1239761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1241761639/2000000 : ℚ) by norm_num]
  exact coverp001001101101
theorem coverp00100110110 : Covers (-1239761639/4000000 : ℚ) vp00100110110 := join_branches bp001001101100 bp001001101101
private noncomputable def vp0010011011_0 : Blocks := edgeBlocks% "full/vectors/0010011011-V-0000.bin"
private noncomputable def vp0010011011_1 : Blocks := edgeBlocks% "full/vectors/0010011011-V-0001.bin"
noncomputable def vp0010011011 : Blocks := (Blocks.join vp0010011011_0 vp0010011011_1)
private theorem bp00100110110 : Branch 0 (-1239761639/8000000 : ℚ) vp0010011011 := by
  apply branch_left_normalized (c:=vp00100110110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-1239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1239761639/4000000 : ℚ) by norm_num]
  exact coverp00100110110
private noncomputable def ep00100110111_0 : Blocks := edgeBlocks% "full/vectors/00100110111-E-0000.bin"
private noncomputable def ep00100110111_1 : Blocks := edgeBlocks% "full/vectors/00100110111-E-0001.bin"
noncomputable def ep00100110111 : Blocks := (Blocks.join ep00100110111_0 ep00100110111_1)
private theorem idp00100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011011.list =
    C ((2:ℤ)^267) * horner X vp00100110111.list + horner X ep00100110111.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100110111 : Branch 1 (-1239761639/8000000 : ℚ) vp0010011011 := by
  apply branch_checked idp00100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1243761639/4000000 : ℚ) by norm_num]
  exact coverp00100110111
theorem coverp0010011011 : Covers (-1239761639/8000000 : ℚ) vp0010011011 := join_branches bp00100110110 bp00100110111
private noncomputable def vp001001101011_0 : Blocks := edgeBlocks% "full/vectors/001001101011-V-0000.bin"
noncomputable def vp001001101011 : Blocks := vp001001101011_0
theorem coverp001001101011 : Covers (-1237761639/2000000 : ℚ) vp001001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011010101_0 : Blocks := edgeBlocks% "full/vectors/0010011010101-V-0000.bin"
noncomputable def vp0010011010101 : Blocks := vp0010011010101_0
theorem coverp0010011010101 : Covers (-1236761639/1000000 : ℚ) vp0010011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011010100_0 : Blocks := edgeBlocks% "full/vectors/0010011010100-V-0000.bin"
noncomputable def vp0010011010100 : Blocks := vp0010011010100_0
theorem coverp0010011010100 : Covers (-1235761639/1000000 : ℚ) vp0010011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001101010_0 : Blocks := edgeBlocks% "full/vectors/001001101010-V-0000.bin"
noncomputable def vp001001101010 : Blocks := vp001001101010_0
private theorem bp0010011010100 : Branch 0 (-1235761639/2000000 : ℚ) vp001001101010 := by
  apply branch_left_normalized (c:=vp0010011010100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1235761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1235761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010100
private noncomputable def ep0010011010101_0 : Blocks := edgeBlocks% "full/vectors/0010011010101-E-0000.bin"
noncomputable def ep0010011010101 : Blocks := ep0010011010101_0
private theorem idp0010011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001101010.list =
    C ((2:ℤ)^85) * horner X vp0010011010101.list + horner X ep0010011010101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011010101 : Branch 1 (-1235761639/2000000 : ℚ) vp001001101010 := by
  apply branch_checked idp0010011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1235761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1236761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010101
theorem coverp001001101010 : Covers (-1235761639/2000000 : ℚ) vp001001101010 := join_branches bp0010011010100 bp0010011010101
private noncomputable def vp00100110101_0 : Blocks := edgeBlocks% "full/vectors/00100110101-V-0000.bin"
private noncomputable def vp00100110101_1 : Blocks := edgeBlocks% "full/vectors/00100110101-V-0001.bin"
noncomputable def vp00100110101 : Blocks := (Blocks.join vp00100110101_0 vp00100110101_1)
private theorem bp001001101010 : Branch 0 (-1235761639/4000000 : ℚ) vp00100110101 := by
  apply branch_left_normalized (c:=vp001001101010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1235761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1235761639/2000000 : ℚ) by norm_num]
  exact coverp001001101010
private noncomputable def ep001001101011_0 : Blocks := edgeBlocks% "full/vectors/001001101011-E-0000.bin"
private noncomputable def ep001001101011_1 : Blocks := edgeBlocks% "full/vectors/001001101011-E-0001.bin"
noncomputable def ep001001101011 : Blocks := (Blocks.join ep001001101011_0 ep001001101011_1)
private theorem idp001001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110101.list =
    C ((2:ℤ)^150) * horner X vp001001101011.list + horner X ep001001101011.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001101011 : Branch 1 (-1235761639/4000000 : ℚ) vp00100110101 := by
  apply branch_checked idp001001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1235761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1237761639/2000000 : ℚ) by norm_num]
  exact coverp001001101011
theorem coverp00100110101 : Covers (-1235761639/4000000 : ℚ) vp00100110101 := join_branches bp001001101010 bp001001101011
private noncomputable def vp0010011010011_0 : Blocks := edgeBlocks% "full/vectors/0010011010011-V-0000.bin"
noncomputable def vp0010011010011 : Blocks := vp0010011010011_0
theorem coverp0010011010011 : Covers (-1234761639/1000000 : ℚ) vp0010011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011010010_0 : Blocks := edgeBlocks% "full/vectors/0010011010010-V-0000.bin"
noncomputable def vp0010011010010 : Blocks := vp0010011010010_0
theorem coverp0010011010010 : Covers (-1233761639/1000000 : ℚ) vp0010011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001101001_0 : Blocks := edgeBlocks% "full/vectors/001001101001-V-0000.bin"
noncomputable def vp001001101001 : Blocks := vp001001101001_0
private theorem bp0010011010010 : Branch 0 (-1233761639/2000000 : ℚ) vp001001101001 := by
  apply branch_left_normalized (c:=vp0010011010010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1233761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1233761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010010
private noncomputable def ep0010011010011_0 : Blocks := edgeBlocks% "full/vectors/0010011010011-E-0000.bin"
noncomputable def ep0010011010011 : Blocks := ep0010011010011_0
private theorem idp0010011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001101001.list =
    C ((2:ℤ)^80) * horner X vp0010011010011.list + horner X ep0010011010011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011010011 : Branch 1 (-1233761639/2000000 : ℚ) vp001001101001 := by
  apply branch_checked idp0010011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1233761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1234761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010011
theorem coverp001001101001 : Covers (-1233761639/2000000 : ℚ) vp001001101001 := join_branches bp0010011010010 bp0010011010011
private noncomputable def vp0010011010001_0 : Blocks := edgeBlocks% "full/vectors/0010011010001-V-0000.bin"
noncomputable def vp0010011010001 : Blocks := vp0010011010001_0
theorem coverp0010011010001 : Covers (-1232761639/1000000 : ℚ) vp0010011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011010000_0 : Blocks := edgeBlocks% "full/vectors/0010011010000-V-0000.bin"
noncomputable def vp0010011010000 : Blocks := vp0010011010000_0
theorem coverp0010011010000 : Covers (-1231761639/1000000 : ℚ) vp0010011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001101000_0 : Blocks := edgeBlocks% "full/vectors/001001101000-V-0000.bin"
noncomputable def vp001001101000 : Blocks := vp001001101000_0
private theorem bp0010011010000 : Branch 0 (-1231761639/2000000 : ℚ) vp001001101000 := by
  apply branch_left_normalized (c:=vp0010011010000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1231761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1231761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010000
private noncomputable def ep0010011010001_0 : Blocks := edgeBlocks% "full/vectors/0010011010001-E-0000.bin"
noncomputable def ep0010011010001 : Blocks := ep0010011010001_0
private theorem idp0010011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001101000.list =
    C ((2:ℤ)^80) * horner X vp0010011010001.list + horner X ep0010011010001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011010001 : Branch 1 (-1231761639/2000000 : ℚ) vp001001101000 := by
  apply branch_checked idp0010011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1231761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1232761639/1000000 : ℚ) by norm_num]
  exact coverp0010011010001
theorem coverp001001101000 : Covers (-1231761639/2000000 : ℚ) vp001001101000 := join_branches bp0010011010000 bp0010011010001
private noncomputable def vp00100110100_0 : Blocks := edgeBlocks% "full/vectors/00100110100-V-0000.bin"
private noncomputable def vp00100110100_1 : Blocks := edgeBlocks% "full/vectors/00100110100-V-0001.bin"
noncomputable def vp00100110100 : Blocks := (Blocks.join vp00100110100_0 vp00100110100_1)
private theorem bp001001101000 : Branch 0 (-1231761639/4000000 : ℚ) vp00100110100 := by
  apply branch_left_normalized (c:=vp001001101000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1231761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1231761639/2000000 : ℚ) by norm_num]
  exact coverp001001101000
private noncomputable def ep001001101001_0 : Blocks := edgeBlocks% "full/vectors/001001101001-E-0000.bin"
private noncomputable def ep001001101001_1 : Blocks := edgeBlocks% "full/vectors/001001101001-E-0001.bin"
noncomputable def ep001001101001 : Blocks := (Blocks.join ep001001101001_0 ep001001101001_1)
private theorem idp001001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110100.list =
    C ((2:ℤ)^142) * horner X vp001001101001.list + horner X ep001001101001.list := by
  exact edge_identity (B := (2:ℤ)^287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001101001 : Branch 1 (-1231761639/4000000 : ℚ) vp00100110100 := by
  apply branch_checked idp001001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1231761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1233761639/2000000 : ℚ) by norm_num]
  exact coverp001001101001
theorem coverp00100110100 : Covers (-1231761639/4000000 : ℚ) vp00100110100 := join_branches bp001001101000 bp001001101001
private noncomputable def vp0010011010_0 : Blocks := edgeBlocks% "full/vectors/0010011010-V-0000.bin"
private noncomputable def vp0010011010_1 : Blocks := edgeBlocks% "full/vectors/0010011010-V-0001.bin"
noncomputable def vp0010011010 : Blocks := (Blocks.join vp0010011010_0 vp0010011010_1)
private theorem bp00100110100 : Branch 0 (-1231761639/8000000 : ℚ) vp0010011010 := by
  apply branch_left_normalized (c:=vp00100110100) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-1231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1231761639/4000000 : ℚ) by norm_num]
  exact coverp00100110100
private noncomputable def ep00100110101_0 : Blocks := edgeBlocks% "full/vectors/00100110101-E-0000.bin"
private noncomputable def ep00100110101_1 : Blocks := edgeBlocks% "full/vectors/00100110101-E-0001.bin"
noncomputable def ep00100110101 : Blocks := (Blocks.join ep00100110101_0 ep00100110101_1)
private theorem idp00100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011010.list =
    C ((2:ℤ)^262) * horner X vp00100110101.list + horner X ep00100110101.list := by
  exact edge_identity (B := (2:ℤ)^459) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100110101 : Branch 1 (-1231761639/8000000 : ℚ) vp0010011010 := by
  apply branch_checked idp00100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1235761639/4000000 : ℚ) by norm_num]
  exact coverp00100110101
theorem coverp0010011010 : Covers (-1231761639/8000000 : ℚ) vp0010011010 := join_branches bp00100110100 bp00100110101
private noncomputable def vp001001101_0 : Blocks := edgeBlocks% "full/vectors/001001101-V-0000.bin"
private noncomputable def vp001001101_1 : Blocks := edgeBlocks% "full/vectors/001001101-V-0001.bin"
private noncomputable def vp001001101_2 : Blocks := edgeBlocks% "full/vectors/001001101-V-0002.bin"
private noncomputable def vp001001101_3 : Blocks := edgeBlocks% "full/vectors/001001101-V-0003.bin"
noncomputable def vp001001101 : Blocks := (Blocks.join (Blocks.join vp001001101_0 vp001001101_1) (Blocks.join vp001001101_2 vp001001101_3))
private theorem bp0010011010 : Branch 0 (-1231761639/16000000 : ℚ) vp001001101 := by
  apply branch_left_normalized (c:=vp0010011010) (k:=0) (m:=243) (by decide +kernel)
  rw [show 2*(-1231761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1231761639/8000000 : ℚ) by norm_num]
  exact coverp0010011010
private noncomputable def ep0010011011_0 : Blocks := edgeBlocks% "full/vectors/0010011011-E-0000.bin"
private noncomputable def ep0010011011_1 : Blocks := edgeBlocks% "full/vectors/0010011011-E-0001.bin"
private noncomputable def ep0010011011_2 : Blocks := edgeBlocks% "full/vectors/0010011011-E-0002.bin"
private noncomputable def ep0010011011_3 : Blocks := edgeBlocks% "full/vectors/0010011011-E-0003.bin"
noncomputable def ep0010011011 : Blocks := (Blocks.join (Blocks.join ep0010011011_0 ep0010011011_1) (Blocks.join ep0010011011_2 ep0010011011_3))
private theorem idp0010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001101.list =
    C ((2:ℤ)^514) * horner X vp0010011011.list + horner X ep0010011011.list := by
  exact edge_identity (B := (2:ℤ)^799) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011011 : Branch 1 (-1231761639/16000000 : ℚ) vp001001101 := by
  apply branch_checked idp0010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1231761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1239761639/8000000 : ℚ) by norm_num]
  exact coverp0010011011
theorem coverp001001101 : Covers (-1231761639/16000000 : ℚ) vp001001101 := join_branches bp0010011010 bp0010011011
private noncomputable def vp0010011001111_0 : Blocks := edgeBlocks% "full/vectors/0010011001111-V-0000.bin"
noncomputable def vp0010011001111 : Blocks := vp0010011001111_0
theorem coverp0010011001111 : Covers (-1230761639/1000000 : ℚ) vp0010011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011001110_0 : Blocks := edgeBlocks% "full/vectors/0010011001110-V-0000.bin"
noncomputable def vp0010011001110 : Blocks := vp0010011001110_0
theorem coverp0010011001110 : Covers (-1229761639/1000000 : ℚ) vp0010011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100111_0 : Blocks := edgeBlocks% "full/vectors/001001100111-V-0000.bin"
noncomputable def vp001001100111 : Blocks := vp001001100111_0
private theorem bp0010011001110 : Branch 0 (-1229761639/2000000 : ℚ) vp001001100111 := by
  apply branch_left_normalized (c:=vp0010011001110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1229761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1229761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001110
private noncomputable def ep0010011001111_0 : Blocks := edgeBlocks% "full/vectors/0010011001111-E-0000.bin"
noncomputable def ep0010011001111 : Blocks := ep0010011001111_0
private theorem idp0010011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100111.list =
    C ((2:ℤ)^81) * horner X vp0010011001111.list + horner X ep0010011001111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011001111 : Branch 1 (-1229761639/2000000 : ℚ) vp001001100111 := by
  apply branch_checked idp0010011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1229761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1230761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001111
theorem coverp001001100111 : Covers (-1229761639/2000000 : ℚ) vp001001100111 := join_branches bp0010011001110 bp0010011001111
private noncomputable def vp0010011001101_0 : Blocks := edgeBlocks% "full/vectors/0010011001101-V-0000.bin"
noncomputable def vp0010011001101 : Blocks := vp0010011001101_0
theorem coverp0010011001101 : Covers (-1228761639/1000000 : ℚ) vp0010011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011001100_0 : Blocks := edgeBlocks% "full/vectors/0010011001100-V-0000.bin"
noncomputable def vp0010011001100 : Blocks := vp0010011001100_0
theorem coverp0010011001100 : Covers (-1227761639/1000000 : ℚ) vp0010011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100110_0 : Blocks := edgeBlocks% "full/vectors/001001100110-V-0000.bin"
noncomputable def vp001001100110 : Blocks := vp001001100110_0
private theorem bp0010011001100 : Branch 0 (-1227761639/2000000 : ℚ) vp001001100110 := by
  apply branch_left_normalized (c:=vp0010011001100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1227761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1227761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001100
private noncomputable def ep0010011001101_0 : Blocks := edgeBlocks% "full/vectors/0010011001101-E-0000.bin"
noncomputable def ep0010011001101 : Blocks := ep0010011001101_0
private theorem idp0010011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100110.list =
    C ((2:ℤ)^83) * horner X vp0010011001101.list + horner X ep0010011001101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011001101 : Branch 1 (-1227761639/2000000 : ℚ) vp001001100110 := by
  apply branch_checked idp0010011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1227761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1228761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001101
theorem coverp001001100110 : Covers (-1227761639/2000000 : ℚ) vp001001100110 := join_branches bp0010011001100 bp0010011001101
private noncomputable def vp00100110011_0 : Blocks := edgeBlocks% "full/vectors/00100110011-V-0000.bin"
private noncomputable def vp00100110011_1 : Blocks := edgeBlocks% "full/vectors/00100110011-V-0001.bin"
noncomputable def vp00100110011 : Blocks := (Blocks.join vp00100110011_0 vp00100110011_1)
private theorem bp001001100110 : Branch 0 (-1227761639/4000000 : ℚ) vp00100110011 := by
  apply branch_left_normalized (c:=vp001001100110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-1227761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1227761639/2000000 : ℚ) by norm_num]
  exact coverp001001100110
private noncomputable def ep001001100111_0 : Blocks := edgeBlocks% "full/vectors/001001100111-E-0000.bin"
private noncomputable def ep001001100111_1 : Blocks := edgeBlocks% "full/vectors/001001100111-E-0001.bin"
noncomputable def ep001001100111 : Blocks := (Blocks.join ep001001100111_0 ep001001100111_1)
private theorem idp001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110011.list =
    C ((2:ℤ)^146) * horner X vp001001100111.list + horner X ep001001100111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001100111 : Branch 1 (-1227761639/4000000 : ℚ) vp00100110011 := by
  apply branch_checked idp001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1227761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1229761639/2000000 : ℚ) by norm_num]
  exact coverp001001100111
theorem coverp00100110011 : Covers (-1227761639/4000000 : ℚ) vp00100110011 := join_branches bp001001100110 bp001001100111
private noncomputable def vp0010011001011_0 : Blocks := edgeBlocks% "full/vectors/0010011001011-V-0000.bin"
noncomputable def vp0010011001011 : Blocks := vp0010011001011_0
theorem coverp0010011001011 : Covers (-1226761639/1000000 : ℚ) vp0010011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011001010_0 : Blocks := edgeBlocks% "full/vectors/0010011001010-V-0000.bin"
noncomputable def vp0010011001010 : Blocks := vp0010011001010_0
theorem coverp0010011001010 : Covers (-1225761639/1000000 : ℚ) vp0010011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100101_0 : Blocks := edgeBlocks% "full/vectors/001001100101-V-0000.bin"
noncomputable def vp001001100101 : Blocks := vp001001100101_0
private theorem bp0010011001010 : Branch 0 (-1225761639/2000000 : ℚ) vp001001100101 := by
  apply branch_left_normalized (c:=vp0010011001010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1225761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1225761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001010
private noncomputable def ep0010011001011_0 : Blocks := edgeBlocks% "full/vectors/0010011001011-E-0000.bin"
noncomputable def ep0010011001011 : Blocks := ep0010011001011_0
private theorem idp0010011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100101.list =
    C ((2:ℤ)^84) * horner X vp0010011001011.list + horner X ep0010011001011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011001011 : Branch 1 (-1225761639/2000000 : ℚ) vp001001100101 := by
  apply branch_checked idp0010011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1225761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1226761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001011
theorem coverp001001100101 : Covers (-1225761639/2000000 : ℚ) vp001001100101 := join_branches bp0010011001010 bp0010011001011
private noncomputable def vp0010011001001_0 : Blocks := edgeBlocks% "full/vectors/0010011001001-V-0000.bin"
noncomputable def vp0010011001001 : Blocks := vp0010011001001_0
theorem coverp0010011001001 : Covers (-1224761639/1000000 : ℚ) vp0010011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011001000_0 : Blocks := edgeBlocks% "full/vectors/0010011001000-V-0000.bin"
noncomputable def vp0010011001000 : Blocks := vp0010011001000_0
theorem coverp0010011001000 : Covers (-1223761639/1000000 : ℚ) vp0010011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100100_0 : Blocks := edgeBlocks% "full/vectors/001001100100-V-0000.bin"
noncomputable def vp001001100100 : Blocks := vp001001100100_0
private theorem bp0010011001000 : Branch 0 (-1223761639/2000000 : ℚ) vp001001100100 := by
  apply branch_left_normalized (c:=vp0010011001000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1223761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1223761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001000
private noncomputable def ep0010011001001_0 : Blocks := edgeBlocks% "full/vectors/0010011001001-E-0000.bin"
noncomputable def ep0010011001001 : Blocks := ep0010011001001_0
private theorem idp0010011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100100.list =
    C ((2:ℤ)^83) * horner X vp0010011001001.list + horner X ep0010011001001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011001001 : Branch 1 (-1223761639/2000000 : ℚ) vp001001100100 := by
  apply branch_checked idp0010011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1223761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1224761639/1000000 : ℚ) by norm_num]
  exact coverp0010011001001
theorem coverp001001100100 : Covers (-1223761639/2000000 : ℚ) vp001001100100 := join_branches bp0010011001000 bp0010011001001
private noncomputable def vp00100110010_0 : Blocks := edgeBlocks% "full/vectors/00100110010-V-0000.bin"
private noncomputable def vp00100110010_1 : Blocks := edgeBlocks% "full/vectors/00100110010-V-0001.bin"
noncomputable def vp00100110010 : Blocks := (Blocks.join vp00100110010_0 vp00100110010_1)
private theorem bp001001100100 : Branch 0 (-1223761639/4000000 : ℚ) vp00100110010 := by
  apply branch_left_normalized (c:=vp001001100100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1223761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1223761639/2000000 : ℚ) by norm_num]
  exact coverp001001100100
private noncomputable def ep001001100101_0 : Blocks := edgeBlocks% "full/vectors/001001100101-E-0000.bin"
private noncomputable def ep001001100101_1 : Blocks := edgeBlocks% "full/vectors/001001100101-E-0001.bin"
noncomputable def ep001001100101 : Blocks := (Blocks.join ep001001100101_0 ep001001100101_1)
private theorem idp001001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110010.list =
    C ((2:ℤ)^149) * horner X vp001001100101.list + horner X ep001001100101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001100101 : Branch 1 (-1223761639/4000000 : ℚ) vp00100110010 := by
  apply branch_checked idp001001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1223761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1225761639/2000000 : ℚ) by norm_num]
  exact coverp001001100101
theorem coverp00100110010 : Covers (-1223761639/4000000 : ℚ) vp00100110010 := join_branches bp001001100100 bp001001100101
private noncomputable def vp0010011001_0 : Blocks := edgeBlocks% "full/vectors/0010011001-V-0000.bin"
private noncomputable def vp0010011001_1 : Blocks := edgeBlocks% "full/vectors/0010011001-V-0001.bin"
noncomputable def vp0010011001 : Blocks := (Blocks.join vp0010011001_0 vp0010011001_1)
private theorem bp00100110010 : Branch 0 (-1223761639/8000000 : ℚ) vp0010011001 := by
  apply branch_left_normalized (c:=vp00100110010) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-1223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1223761639/4000000 : ℚ) by norm_num]
  exact coverp00100110010
private noncomputable def ep00100110011_0 : Blocks := edgeBlocks% "full/vectors/00100110011-E-0000.bin"
private noncomputable def ep00100110011_1 : Blocks := edgeBlocks% "full/vectors/00100110011-E-0001.bin"
noncomputable def ep00100110011 : Blocks := (Blocks.join ep00100110011_0 ep00100110011_1)
private theorem idp00100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011001.list =
    C ((2:ℤ)^274) * horner X vp00100110011.list + horner X ep00100110011.list := by
  exact edge_identity (B := (2:ℤ)^468) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100110011 : Branch 1 (-1223761639/8000000 : ℚ) vp0010011001 := by
  apply branch_checked idp00100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1227761639/4000000 : ℚ) by norm_num]
  exact coverp00100110011
theorem coverp0010011001 : Covers (-1223761639/8000000 : ℚ) vp0010011001 := join_branches bp00100110010 bp00100110011
private noncomputable def vp0010011000111_0 : Blocks := edgeBlocks% "full/vectors/0010011000111-V-0000.bin"
noncomputable def vp0010011000111 : Blocks := vp0010011000111_0
theorem coverp0010011000111 : Covers (-1222761639/1000000 : ℚ) vp0010011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011000110_0 : Blocks := edgeBlocks% "full/vectors/0010011000110-V-0000.bin"
noncomputable def vp0010011000110 : Blocks := vp0010011000110_0
theorem coverp0010011000110 : Covers (-1221761639/1000000 : ℚ) vp0010011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100011_0 : Blocks := edgeBlocks% "full/vectors/001001100011-V-0000.bin"
noncomputable def vp001001100011 : Blocks := vp001001100011_0
private theorem bp0010011000110 : Branch 0 (-1221761639/2000000 : ℚ) vp001001100011 := by
  apply branch_left_normalized (c:=vp0010011000110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1221761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1221761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000110
private noncomputable def ep0010011000111_0 : Blocks := edgeBlocks% "full/vectors/0010011000111-E-0000.bin"
noncomputable def ep0010011000111 : Blocks := ep0010011000111_0
private theorem idp0010011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100011.list =
    C ((2:ℤ)^82) * horner X vp0010011000111.list + horner X ep0010011000111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011000111 : Branch 1 (-1221761639/2000000 : ℚ) vp001001100011 := by
  apply branch_checked idp0010011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1221761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1222761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000111
theorem coverp001001100011 : Covers (-1221761639/2000000 : ℚ) vp001001100011 := join_branches bp0010011000110 bp0010011000111
private noncomputable def vp0010011000101_0 : Blocks := edgeBlocks% "full/vectors/0010011000101-V-0000.bin"
noncomputable def vp0010011000101 : Blocks := vp0010011000101_0
theorem coverp0010011000101 : Covers (-1220761639/1000000 : ℚ) vp0010011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011000100_0 : Blocks := edgeBlocks% "full/vectors/0010011000100-V-0000.bin"
noncomputable def vp0010011000100 : Blocks := vp0010011000100_0
theorem coverp0010011000100 : Covers (-1219761639/1000000 : ℚ) vp0010011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100010_0 : Blocks := edgeBlocks% "full/vectors/001001100010-V-0000.bin"
noncomputable def vp001001100010 : Blocks := vp001001100010_0
private theorem bp0010011000100 : Branch 0 (-1219761639/2000000 : ℚ) vp001001100010 := by
  apply branch_left_normalized (c:=vp0010011000100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1219761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1219761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000100
private noncomputable def ep0010011000101_0 : Blocks := edgeBlocks% "full/vectors/0010011000101-E-0000.bin"
noncomputable def ep0010011000101 : Blocks := ep0010011000101_0
private theorem idp0010011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100010.list =
    C ((2:ℤ)^83) * horner X vp0010011000101.list + horner X ep0010011000101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011000101 : Branch 1 (-1219761639/2000000 : ℚ) vp001001100010 := by
  apply branch_checked idp0010011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1219761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1220761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000101
theorem coverp001001100010 : Covers (-1219761639/2000000 : ℚ) vp001001100010 := join_branches bp0010011000100 bp0010011000101
private noncomputable def vp00100110001_0 : Blocks := edgeBlocks% "full/vectors/00100110001-V-0000.bin"
private noncomputable def vp00100110001_1 : Blocks := edgeBlocks% "full/vectors/00100110001-V-0001.bin"
noncomputable def vp00100110001 : Blocks := (Blocks.join vp00100110001_0 vp00100110001_1)
private theorem bp001001100010 : Branch 0 (-1219761639/4000000 : ℚ) vp00100110001 := by
  apply branch_left_normalized (c:=vp001001100010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1219761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1219761639/2000000 : ℚ) by norm_num]
  exact coverp001001100010
private noncomputable def ep001001100011_0 : Blocks := edgeBlocks% "full/vectors/001001100011-E-0000.bin"
private noncomputable def ep001001100011_1 : Blocks := edgeBlocks% "full/vectors/001001100011-E-0001.bin"
noncomputable def ep001001100011 : Blocks := (Blocks.join ep001001100011_0 ep001001100011_1)
private theorem idp001001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110001.list =
    C ((2:ℤ)^145) * horner X vp001001100011.list + horner X ep001001100011.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001100011 : Branch 1 (-1219761639/4000000 : ℚ) vp00100110001 := by
  apply branch_checked idp001001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1219761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1221761639/2000000 : ℚ) by norm_num]
  exact coverp001001100011
theorem coverp00100110001 : Covers (-1219761639/4000000 : ℚ) vp00100110001 := join_branches bp001001100010 bp001001100011
private noncomputable def vp0010011000011_0 : Blocks := edgeBlocks% "full/vectors/0010011000011-V-0000.bin"
noncomputable def vp0010011000011 : Blocks := vp0010011000011_0
theorem coverp0010011000011 : Covers (-1218761639/1000000 : ℚ) vp0010011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011000010_0 : Blocks := edgeBlocks% "full/vectors/0010011000010-V-0000.bin"
noncomputable def vp0010011000010 : Blocks := vp0010011000010_0
theorem coverp0010011000010 : Covers (-1217761639/1000000 : ℚ) vp0010011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100001_0 : Blocks := edgeBlocks% "full/vectors/001001100001-V-0000.bin"
noncomputable def vp001001100001 : Blocks := vp001001100001_0
private theorem bp0010011000010 : Branch 0 (-1217761639/2000000 : ℚ) vp001001100001 := by
  apply branch_left_normalized (c:=vp0010011000010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1217761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1217761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000010
private noncomputable def ep0010011000011_0 : Blocks := edgeBlocks% "full/vectors/0010011000011-E-0000.bin"
noncomputable def ep0010011000011 : Blocks := ep0010011000011_0
private theorem idp0010011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100001.list =
    C ((2:ℤ)^83) * horner X vp0010011000011.list + horner X ep0010011000011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011000011 : Branch 1 (-1217761639/2000000 : ℚ) vp001001100001 := by
  apply branch_checked idp0010011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1217761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1218761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000011
theorem coverp001001100001 : Covers (-1217761639/2000000 : ℚ) vp001001100001 := join_branches bp0010011000010 bp0010011000011
private noncomputable def vp0010011000001_0 : Blocks := edgeBlocks% "full/vectors/0010011000001-V-0000.bin"
noncomputable def vp0010011000001 : Blocks := vp0010011000001_0
theorem coverp0010011000001 : Covers (-1216761639/1000000 : ℚ) vp0010011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010011000000_0 : Blocks := edgeBlocks% "full/vectors/0010011000000-V-0000.bin"
noncomputable def vp0010011000000 : Blocks := vp0010011000000_0
theorem coverp0010011000000 : Covers (-1215761639/1000000 : ℚ) vp0010011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001100000_0 : Blocks := edgeBlocks% "full/vectors/001001100000-V-0000.bin"
noncomputable def vp001001100000 : Blocks := vp001001100000_0
private theorem bp0010011000000 : Branch 0 (-1215761639/2000000 : ℚ) vp001001100000 := by
  apply branch_left_normalized (c:=vp0010011000000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1215761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000000
private noncomputable def ep0010011000001_0 : Blocks := edgeBlocks% "full/vectors/0010011000001-E-0000.bin"
noncomputable def ep0010011000001 : Blocks := ep0010011000001_0
private theorem idp0010011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100000.list =
    C ((2:ℤ)^85) * horner X vp0010011000001.list + horner X ep0010011000001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011000001 : Branch 1 (-1215761639/2000000 : ℚ) vp001001100000 := by
  apply branch_checked idp0010011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1216761639/1000000 : ℚ) by norm_num]
  exact coverp0010011000001
theorem coverp001001100000 : Covers (-1215761639/2000000 : ℚ) vp001001100000 := join_branches bp0010011000000 bp0010011000001
private noncomputable def vp00100110000_0 : Blocks := edgeBlocks% "full/vectors/00100110000-V-0000.bin"
private noncomputable def vp00100110000_1 : Blocks := edgeBlocks% "full/vectors/00100110000-V-0001.bin"
noncomputable def vp00100110000 : Blocks := (Blocks.join vp00100110000_0 vp00100110000_1)
private theorem bp001001100000 : Branch 0 (-1215761639/4000000 : ℚ) vp00100110000 := by
  apply branch_left_normalized (c:=vp001001100000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1215761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/2000000 : ℚ) by norm_num]
  exact coverp001001100000
private noncomputable def ep001001100001_0 : Blocks := edgeBlocks% "full/vectors/001001100001-E-0000.bin"
private noncomputable def ep001001100001_1 : Blocks := edgeBlocks% "full/vectors/001001100001-E-0001.bin"
noncomputable def ep001001100001 : Blocks := (Blocks.join ep001001100001_0 ep001001100001_1)
private theorem idp001001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110000.list =
    C ((2:ℤ)^149) * horner X vp001001100001.list + horner X ep001001100001.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001100001 : Branch 1 (-1215761639/4000000 : ℚ) vp00100110000 := by
  apply branch_checked idp001001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1217761639/2000000 : ℚ) by norm_num]
  exact coverp001001100001
theorem coverp00100110000 : Covers (-1215761639/4000000 : ℚ) vp00100110000 := join_branches bp001001100000 bp001001100001
private noncomputable def vp0010011000_0 : Blocks := edgeBlocks% "full/vectors/0010011000-V-0000.bin"
private noncomputable def vp0010011000_1 : Blocks := edgeBlocks% "full/vectors/0010011000-V-0001.bin"
noncomputable def vp0010011000 : Blocks := (Blocks.join vp0010011000_0 vp0010011000_1)
private theorem bp00100110000 : Branch 0 (-1215761639/8000000 : ℚ) vp0010011000 := by
  apply branch_left_normalized (c:=vp00100110000) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-1215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/4000000 : ℚ) by norm_num]
  exact coverp00100110000
private noncomputable def ep00100110001_0 : Blocks := edgeBlocks% "full/vectors/00100110001-E-0000.bin"
private noncomputable def ep00100110001_1 : Blocks := edgeBlocks% "full/vectors/00100110001-E-0001.bin"
noncomputable def ep00100110001 : Blocks := (Blocks.join ep00100110001_0 ep00100110001_1)
private theorem idp00100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011000.list =
    C ((2:ℤ)^273) * horner X vp00100110001.list + horner X ep00100110001.list := by
  exact edge_identity (B := (2:ℤ)^469) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100110001 : Branch 1 (-1215761639/8000000 : ℚ) vp0010011000 := by
  apply branch_checked idp00100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1219761639/4000000 : ℚ) by norm_num]
  exact coverp00100110001
theorem coverp0010011000 : Covers (-1215761639/8000000 : ℚ) vp0010011000 := join_branches bp00100110000 bp00100110001
private noncomputable def vp001001100_0 : Blocks := edgeBlocks% "full/vectors/001001100-V-0000.bin"
private noncomputable def vp001001100_1 : Blocks := edgeBlocks% "full/vectors/001001100-V-0001.bin"
private noncomputable def vp001001100_2 : Blocks := edgeBlocks% "full/vectors/001001100-V-0002.bin"
private noncomputable def vp001001100_3 : Blocks := edgeBlocks% "full/vectors/001001100-V-0003.bin"
noncomputable def vp001001100 : Blocks := (Blocks.join (Blocks.join vp001001100_0 vp001001100_1) (Blocks.join vp001001100_2 vp001001100_3))
private theorem bp0010011000 : Branch 0 (-1215761639/16000000 : ℚ) vp001001100 := by
  apply branch_left_normalized (c:=vp0010011000) (k:=0) (m:=247) (by decide +kernel)
  rw [show 2*(-1215761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/8000000 : ℚ) by norm_num]
  exact coverp0010011000
private noncomputable def ep0010011001_0 : Blocks := edgeBlocks% "full/vectors/0010011001-E-0000.bin"
private noncomputable def ep0010011001_1 : Blocks := edgeBlocks% "full/vectors/0010011001-E-0001.bin"
private noncomputable def ep0010011001_2 : Blocks := edgeBlocks% "full/vectors/0010011001-E-0002.bin"
private noncomputable def ep0010011001_3 : Blocks := edgeBlocks% "full/vectors/0010011001-E-0003.bin"
noncomputable def ep0010011001 : Blocks := (Blocks.join (Blocks.join ep0010011001_0 ep0010011001_1) (Blocks.join ep0010011001_2 ep0010011001_3))
private theorem idp0010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001100.list =
    C ((2:ℤ)^518) * horner X vp0010011001.list + horner X ep0010011001.list := by
  exact edge_identity (B := (2:ℤ)^813) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010011001 : Branch 1 (-1215761639/16000000 : ℚ) vp001001100 := by
  apply branch_checked idp0010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1223761639/8000000 : ℚ) by norm_num]
  exact coverp0010011001
theorem coverp001001100 : Covers (-1215761639/16000000 : ℚ) vp001001100 := join_branches bp0010011000 bp0010011001
private noncomputable def vp00100110_0 : Blocks := edgeBlocks% "full/vectors/00100110-V-0000.bin"
private noncomputable def vp00100110_1 : Blocks := edgeBlocks% "full/vectors/00100110-V-0001.bin"
private noncomputable def vp00100110_2 : Blocks := edgeBlocks% "full/vectors/00100110-V-0002.bin"
private noncomputable def vp00100110_3 : Blocks := edgeBlocks% "full/vectors/00100110-V-0003.bin"
private noncomputable def vp00100110_4 : Blocks := edgeBlocks% "full/vectors/00100110-V-0004.bin"
private noncomputable def vp00100110_5 : Blocks := edgeBlocks% "full/vectors/00100110-V-0005.bin"
private noncomputable def vp00100110_6 : Blocks := edgeBlocks% "full/vectors/00100110-V-0006.bin"
private noncomputable def vp00100110_7 : Blocks := edgeBlocks% "full/vectors/00100110-V-0007.bin"
noncomputable def vp00100110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100110_0 vp00100110_1) (Blocks.join vp00100110_2 vp00100110_3)) (Blocks.join (Blocks.join vp00100110_4 vp00100110_5) (Blocks.join vp00100110_6 vp00100110_7)))
private theorem bp001001100 : Branch 0 (-1215761639/32000000 : ℚ) vp00100110 := by
  apply branch_left_normalized (c:=vp001001100) (k:=0) (m:=471) (by decide +kernel)
  rw [show 2*(-1215761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/16000000 : ℚ) by norm_num]
  exact coverp001001100
private noncomputable def ep001001101_0 : Blocks := edgeBlocks% "full/vectors/001001101-E-0000.bin"
private noncomputable def ep001001101_1 : Blocks := edgeBlocks% "full/vectors/001001101-E-0001.bin"
private noncomputable def ep001001101_2 : Blocks := edgeBlocks% "full/vectors/001001101-E-0002.bin"
private noncomputable def ep001001101_3 : Blocks := edgeBlocks% "full/vectors/001001101-E-0003.bin"
private noncomputable def ep001001101_4 : Blocks := edgeBlocks% "full/vectors/001001101-E-0004.bin"
private noncomputable def ep001001101_5 : Blocks := edgeBlocks% "full/vectors/001001101-E-0005.bin"
private noncomputable def ep001001101_6 : Blocks := edgeBlocks% "full/vectors/001001101-E-0006.bin"
private noncomputable def ep001001101_7 : Blocks := edgeBlocks% "full/vectors/001001101-E-0007.bin"
noncomputable def ep001001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001001101_0 ep001001101_1) (Blocks.join ep001001101_2 ep001001101_3)) (Blocks.join (Blocks.join ep001001101_4 ep001001101_5) (Blocks.join ep001001101_6 ep001001101_7)))
private theorem idp001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100110.list =
    C ((2:ℤ)^1012) * horner X vp001001101.list + horner X ep001001101.list := by
  exact edge_identity (B := (2:ℤ)^1492) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001101 : Branch 1 (-1215761639/32000000 : ℚ) vp00100110 := by
  apply branch_checked idp001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1231761639/16000000 : ℚ) by norm_num]
  exact coverp001001101
theorem coverp00100110 : Covers (-1215761639/32000000 : ℚ) vp00100110 := join_branches bp001001100 bp001001101
private noncomputable def vp0010011_0 : Blocks := edgeBlocks% "full/vectors/0010011-V-0000.bin"
private noncomputable def vp0010011_1 : Blocks := edgeBlocks% "full/vectors/0010011-V-0001.bin"
private noncomputable def vp0010011_2 : Blocks := edgeBlocks% "full/vectors/0010011-V-0002.bin"
private noncomputable def vp0010011_3 : Blocks := edgeBlocks% "full/vectors/0010011-V-0003.bin"
private noncomputable def vp0010011_4 : Blocks := edgeBlocks% "full/vectors/0010011-V-0004.bin"
private noncomputable def vp0010011_5 : Blocks := edgeBlocks% "full/vectors/0010011-V-0005.bin"
private noncomputable def vp0010011_6 : Blocks := edgeBlocks% "full/vectors/0010011-V-0006.bin"
private noncomputable def vp0010011_7 : Blocks := edgeBlocks% "full/vectors/0010011-V-0007.bin"
private noncomputable def vp0010011_8 : Blocks := edgeBlocks% "full/vectors/0010011-V-0008.bin"
private noncomputable def vp0010011_9 : Blocks := edgeBlocks% "full/vectors/0010011-V-0009.bin"
private noncomputable def vp0010011_10 : Blocks := edgeBlocks% "full/vectors/0010011-V-0010.bin"
private noncomputable def vp0010011_11 : Blocks := edgeBlocks% "full/vectors/0010011-V-0011.bin"
private noncomputable def vp0010011_12 : Blocks := edgeBlocks% "full/vectors/0010011-V-0012.bin"
private noncomputable def vp0010011_13 : Blocks := edgeBlocks% "full/vectors/0010011-V-0013.bin"
noncomputable def vp0010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010011_0 (Blocks.join vp0010011_1 vp0010011_2)) (Blocks.join (Blocks.join vp0010011_3 vp0010011_4) (Blocks.join vp0010011_5 vp0010011_6))) (Blocks.join (Blocks.join vp0010011_7 (Blocks.join vp0010011_8 vp0010011_9)) (Blocks.join (Blocks.join vp0010011_10 vp0010011_11) (Blocks.join vp0010011_12 vp0010011_13))))
private theorem bp00100110 : Branch 0 (-1215761639/64000000 : ℚ) vp0010011 := by
  apply branch_left_normalized (c:=vp00100110) (k:=0) (m:=913) (by decide +kernel)
  rw [show 2*(-1215761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1215761639/32000000 : ℚ) by norm_num]
  exact coverp00100110
private noncomputable def ep00100111_0 : Blocks := edgeBlocks% "full/vectors/00100111-E-0000.bin"
private noncomputable def ep00100111_1 : Blocks := edgeBlocks% "full/vectors/00100111-E-0001.bin"
private noncomputable def ep00100111_2 : Blocks := edgeBlocks% "full/vectors/00100111-E-0002.bin"
private noncomputable def ep00100111_3 : Blocks := edgeBlocks% "full/vectors/00100111-E-0003.bin"
private noncomputable def ep00100111_4 : Blocks := edgeBlocks% "full/vectors/00100111-E-0004.bin"
private noncomputable def ep00100111_5 : Blocks := edgeBlocks% "full/vectors/00100111-E-0005.bin"
private noncomputable def ep00100111_6 : Blocks := edgeBlocks% "full/vectors/00100111-E-0006.bin"
private noncomputable def ep00100111_7 : Blocks := edgeBlocks% "full/vectors/00100111-E-0007.bin"
private noncomputable def ep00100111_8 : Blocks := edgeBlocks% "full/vectors/00100111-E-0008.bin"
private noncomputable def ep00100111_9 : Blocks := edgeBlocks% "full/vectors/00100111-E-0009.bin"
private noncomputable def ep00100111_10 : Blocks := edgeBlocks% "full/vectors/00100111-E-0010.bin"
private noncomputable def ep00100111_11 : Blocks := edgeBlocks% "full/vectors/00100111-E-0011.bin"
private noncomputable def ep00100111_12 : Blocks := edgeBlocks% "full/vectors/00100111-E-0012.bin"
private noncomputable def ep00100111_13 : Blocks := edgeBlocks% "full/vectors/00100111-E-0013.bin"
noncomputable def ep00100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00100111_0 (Blocks.join ep00100111_1 ep00100111_2)) (Blocks.join (Blocks.join ep00100111_3 ep00100111_4) (Blocks.join ep00100111_5 ep00100111_6))) (Blocks.join (Blocks.join ep00100111_7 (Blocks.join ep00100111_8 ep00100111_9)) (Blocks.join (Blocks.join ep00100111_10 ep00100111_11) (Blocks.join ep00100111_12 ep00100111_13))))
private theorem idp00100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010011.list =
    C ((2:ℤ)^1975) * horner X vp00100111.list + horner X ep00100111.list := by
  exact edge_identity (B := (2:ℤ)^2830) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100111 : Branch 1 (-1215761639/64000000 : ℚ) vp0010011 := by
  apply branch_checked idp00100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1215761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1247761639/32000000 : ℚ) by norm_num]
  exact coverp00100111
theorem coverp0010011 : Covers (-1215761639/64000000 : ℚ) vp0010011 := join_branches bp00100110 bp00100111
end NextProof.EdgeFull

