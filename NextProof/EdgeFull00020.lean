import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000010111111_0 : Blocks := edgeBlocks% "full/vectors/0000000010111111-V-0000.bin"
noncomputable def vp0000000010111111 : Blocks := vp0000000010111111_0
theorem coverp0000000010111111 : Covers (-23636639/125000 : ℚ) vp0000000010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010111110_0 : Blocks := edgeBlocks% "full/vectors/0000000010111110-V-0000.bin"
noncomputable def vp0000000010111110 : Blocks := vp0000000010111110_0
theorem coverp0000000010111110 : Covers (-23511639/125000 : ℚ) vp0000000010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011111_0 : Blocks := edgeBlocks% "full/vectors/000000001011111-V-0000.bin"
noncomputable def vp000000001011111 : Blocks := vp000000001011111_0
private theorem bp0000000010111110 : Branch 0 (-23511639/250000 : ℚ) vp000000001011111 := by
  apply branch_left_normalized (c:=vp0000000010111110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-23511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-23511639/125000 : ℚ) by norm_num]
  exact coverp0000000010111110
private noncomputable def ep0000000010111111_0 : Blocks := edgeBlocks% "full/vectors/0000000010111111-E-0000.bin"
noncomputable def ep0000000010111111 : Blocks := ep0000000010111111_0
private theorem idp0000000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011111.list =
    C ((2:ℤ)^66) * horner X vp0000000010111111.list + horner X ep0000000010111111.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010111111 : Branch 1 (-23511639/250000 : ℚ) vp000000001011111 := by
  apply branch_checked idp0000000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-23511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-23636639/125000 : ℚ) by norm_num]
  exact coverp0000000010111111
theorem coverp000000001011111 : Covers (-23511639/250000 : ℚ) vp000000001011111 := join_branches bp0000000010111110 bp0000000010111111
private noncomputable def vp0000000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000000010111101-V-0000.bin"
noncomputable def vp0000000010111101 : Blocks := vp0000000010111101_0
theorem coverp0000000010111101 : Covers (-23386639/125000 : ℚ) vp0000000010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010111100_0 : Blocks := edgeBlocks% "full/vectors/0000000010111100-V-0000.bin"
noncomputable def vp0000000010111100 : Blocks := vp0000000010111100_0
theorem coverp0000000010111100 : Covers (-23261639/125000 : ℚ) vp0000000010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011110_0 : Blocks := edgeBlocks% "full/vectors/000000001011110-V-0000.bin"
noncomputable def vp000000001011110 : Blocks := vp000000001011110_0
private theorem bp0000000010111100 : Branch 0 (-23261639/250000 : ℚ) vp000000001011110 := by
  apply branch_left_normalized (c:=vp0000000010111100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-23261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-23261639/125000 : ℚ) by norm_num]
  exact coverp0000000010111100
private noncomputable def ep0000000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000000010111101-E-0000.bin"
noncomputable def ep0000000010111101 : Blocks := ep0000000010111101_0
private theorem idp0000000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011110.list =
    C ((2:ℤ)^65) * horner X vp0000000010111101.list + horner X ep0000000010111101.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010111101 : Branch 1 (-23261639/250000 : ℚ) vp000000001011110 := by
  apply branch_checked idp0000000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-23261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-23386639/125000 : ℚ) by norm_num]
  exact coverp0000000010111101
theorem coverp000000001011110 : Covers (-23261639/250000 : ℚ) vp000000001011110 := join_branches bp0000000010111100 bp0000000010111101
private noncomputable def vp00000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000101111-V-0000.bin"
noncomputable def vp00000000101111 : Blocks := vp00000000101111_0
private theorem bp000000001011110 : Branch 0 (-23261639/500000 : ℚ) vp00000000101111 := by
  apply branch_left_normalized (c:=vp000000001011110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-23261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-23261639/250000 : ℚ) by norm_num]
  exact coverp000000001011110
private noncomputable def ep000000001011111_0 : Blocks := edgeBlocks% "full/vectors/000000001011111-E-0000.bin"
noncomputable def ep000000001011111 : Blocks := ep000000001011111_0
private theorem idp000000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101111.list =
    C ((2:ℤ)^118) * horner X vp000000001011111.list + horner X ep000000001011111.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001011111 : Branch 1 (-23261639/500000 : ℚ) vp00000000101111 := by
  apply branch_checked idp000000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-23261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-23511639/250000 : ℚ) by norm_num]
  exact coverp000000001011111
theorem coverp00000000101111 : Covers (-23261639/500000 : ℚ) vp00000000101111 := join_branches bp000000001011110 bp000000001011111
private noncomputable def vp0000000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000000010111011-V-0000.bin"
noncomputable def vp0000000010111011 : Blocks := vp0000000010111011_0
theorem coverp0000000010111011 : Covers (-23136639/125000 : ℚ) vp0000000010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010111010_0 : Blocks := edgeBlocks% "full/vectors/0000000010111010-V-0000.bin"
noncomputable def vp0000000010111010 : Blocks := vp0000000010111010_0
theorem coverp0000000010111010 : Covers (-23011639/125000 : ℚ) vp0000000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011101_0 : Blocks := edgeBlocks% "full/vectors/000000001011101-V-0000.bin"
noncomputable def vp000000001011101 : Blocks := vp000000001011101_0
private theorem bp0000000010111010 : Branch 0 (-23011639/250000 : ℚ) vp000000001011101 := by
  apply branch_left_normalized (c:=vp0000000010111010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-23011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-23011639/125000 : ℚ) by norm_num]
  exact coverp0000000010111010
private noncomputable def ep0000000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000000010111011-E-0000.bin"
noncomputable def ep0000000010111011 : Blocks := ep0000000010111011_0
private theorem idp0000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011101.list =
    C ((2:ℤ)^66) * horner X vp0000000010111011.list + horner X ep0000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010111011 : Branch 1 (-23011639/250000 : ℚ) vp000000001011101 := by
  apply branch_checked idp0000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-23011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-23136639/125000 : ℚ) by norm_num]
  exact coverp0000000010111011
theorem coverp000000001011101 : Covers (-23011639/250000 : ℚ) vp000000001011101 := join_branches bp0000000010111010 bp0000000010111011
private noncomputable def vp0000000010111001_0 : Blocks := edgeBlocks% "full/vectors/0000000010111001-V-0000.bin"
noncomputable def vp0000000010111001 : Blocks := vp0000000010111001_0
theorem coverp0000000010111001 : Covers (-22886639/125000 : ℚ) vp0000000010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010111000_0 : Blocks := edgeBlocks% "full/vectors/0000000010111000-V-0000.bin"
noncomputable def vp0000000010111000 : Blocks := vp0000000010111000_0
theorem coverp0000000010111000 : Covers (-22761639/125000 : ℚ) vp0000000010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011100_0 : Blocks := edgeBlocks% "full/vectors/000000001011100-V-0000.bin"
noncomputable def vp000000001011100 : Blocks := vp000000001011100_0
private theorem bp0000000010111000 : Branch 0 (-22761639/250000 : ℚ) vp000000001011100 := by
  apply branch_left_normalized (c:=vp0000000010111000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-22761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-22761639/125000 : ℚ) by norm_num]
  exact coverp0000000010111000
private noncomputable def ep0000000010111001_0 : Blocks := edgeBlocks% "full/vectors/0000000010111001-E-0000.bin"
noncomputable def ep0000000010111001 : Blocks := ep0000000010111001_0
private theorem idp0000000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011100.list =
    C ((2:ℤ)^67) * horner X vp0000000010111001.list + horner X ep0000000010111001.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010111001 : Branch 1 (-22761639/250000 : ℚ) vp000000001011100 := by
  apply branch_checked idp0000000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-22761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-22886639/125000 : ℚ) by norm_num]
  exact coverp0000000010111001
theorem coverp000000001011100 : Covers (-22761639/250000 : ℚ) vp000000001011100 := join_branches bp0000000010111000 bp0000000010111001
private noncomputable def vp00000000101110_0 : Blocks := edgeBlocks% "full/vectors/00000000101110-V-0000.bin"
noncomputable def vp00000000101110 : Blocks := vp00000000101110_0
private theorem bp000000001011100 : Branch 0 (-22761639/500000 : ℚ) vp00000000101110 := by
  apply branch_left_normalized (c:=vp000000001011100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-22761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-22761639/250000 : ℚ) by norm_num]
  exact coverp000000001011100
private noncomputable def ep000000001011101_0 : Blocks := edgeBlocks% "full/vectors/000000001011101-E-0000.bin"
noncomputable def ep000000001011101 : Blocks := ep000000001011101_0
private theorem idp000000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101110.list =
    C ((2:ℤ)^119) * horner X vp000000001011101.list + horner X ep000000001011101.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001011101 : Branch 1 (-22761639/500000 : ℚ) vp00000000101110 := by
  apply branch_checked idp000000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-22761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-23011639/250000 : ℚ) by norm_num]
  exact coverp000000001011101
theorem coverp00000000101110 : Covers (-22761639/500000 : ℚ) vp00000000101110 := join_branches bp000000001011100 bp000000001011101
private noncomputable def vp0000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000010111-V-0000.bin"
private noncomputable def vp0000000010111_1 : Blocks := edgeBlocks% "full/vectors/0000000010111-V-0001.bin"
noncomputable def vp0000000010111 : Blocks := (Blocks.join vp0000000010111_0 vp0000000010111_1)
private theorem bp00000000101110 : Branch 0 (-22761639/1000000 : ℚ) vp0000000010111 := by
  apply branch_left_normalized (c:=vp00000000101110) (k:=0) (m:=116) (by decide +kernel)
  rw [show 2*(-22761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-22761639/500000 : ℚ) by norm_num]
  exact coverp00000000101110
private noncomputable def ep00000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000101111-E-0000.bin"
private noncomputable def ep00000000101111_1 : Blocks := edgeBlocks% "full/vectors/00000000101111-E-0001.bin"
noncomputable def ep00000000101111 : Blocks := (Blocks.join ep00000000101111_0 ep00000000101111_1)
private theorem idp00000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010111.list =
    C ((2:ℤ)^222) * horner X vp00000000101111.list + horner X ep00000000101111.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000101111 : Branch 1 (-22761639/1000000 : ℚ) vp0000000010111 := by
  apply branch_checked idp00000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-22761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-23261639/500000 : ℚ) by norm_num]
  exact coverp00000000101111
theorem coverp0000000010111 : Covers (-22761639/1000000 : ℚ) vp0000000010111 := join_branches bp00000000101110 bp00000000101111
private noncomputable def vp0000000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000000010110111-V-0000.bin"
noncomputable def vp0000000010110111 : Blocks := vp0000000010110111_0
theorem coverp0000000010110111 : Covers (-22636639/125000 : ℚ) vp0000000010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010110110_0 : Blocks := edgeBlocks% "full/vectors/0000000010110110-V-0000.bin"
noncomputable def vp0000000010110110 : Blocks := vp0000000010110110_0
theorem coverp0000000010110110 : Covers (-22511639/125000 : ℚ) vp0000000010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011011_0 : Blocks := edgeBlocks% "full/vectors/000000001011011-V-0000.bin"
noncomputable def vp000000001011011 : Blocks := vp000000001011011_0
private theorem bp0000000010110110 : Branch 0 (-22511639/250000 : ℚ) vp000000001011011 := by
  apply branch_left_normalized (c:=vp0000000010110110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-22511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-22511639/125000 : ℚ) by norm_num]
  exact coverp0000000010110110
private noncomputable def ep0000000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000000010110111-E-0000.bin"
noncomputable def ep0000000010110111 : Blocks := ep0000000010110111_0
private theorem idp0000000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011011.list =
    C ((2:ℤ)^67) * horner X vp0000000010110111.list + horner X ep0000000010110111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010110111 : Branch 1 (-22511639/250000 : ℚ) vp000000001011011 := by
  apply branch_checked idp0000000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-22511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-22636639/125000 : ℚ) by norm_num]
  exact coverp0000000010110111
theorem coverp000000001011011 : Covers (-22511639/250000 : ℚ) vp000000001011011 := join_branches bp0000000010110110 bp0000000010110111
private noncomputable def vp0000000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000000010110101-V-0000.bin"
noncomputable def vp0000000010110101 : Blocks := vp0000000010110101_0
theorem coverp0000000010110101 : Covers (-22386639/125000 : ℚ) vp0000000010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010110100_0 : Blocks := edgeBlocks% "full/vectors/0000000010110100-V-0000.bin"
noncomputable def vp0000000010110100 : Blocks := vp0000000010110100_0
theorem coverp0000000010110100 : Covers (-22261639/125000 : ℚ) vp0000000010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011010_0 : Blocks := edgeBlocks% "full/vectors/000000001011010-V-0000.bin"
noncomputable def vp000000001011010 : Blocks := vp000000001011010_0
private theorem bp0000000010110100 : Branch 0 (-22261639/250000 : ℚ) vp000000001011010 := by
  apply branch_left_normalized (c:=vp0000000010110100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-22261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-22261639/125000 : ℚ) by norm_num]
  exact coverp0000000010110100
private noncomputable def ep0000000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000000010110101-E-0000.bin"
noncomputable def ep0000000010110101 : Blocks := ep0000000010110101_0
private theorem idp0000000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011010.list =
    C ((2:ℤ)^66) * horner X vp0000000010110101.list + horner X ep0000000010110101.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010110101 : Branch 1 (-22261639/250000 : ℚ) vp000000001011010 := by
  apply branch_checked idp0000000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-22261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-22386639/125000 : ℚ) by norm_num]
  exact coverp0000000010110101
theorem coverp000000001011010 : Covers (-22261639/250000 : ℚ) vp000000001011010 := join_branches bp0000000010110100 bp0000000010110101
private noncomputable def vp00000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000101101-V-0000.bin"
noncomputable def vp00000000101101 : Blocks := vp00000000101101_0
private theorem bp000000001011010 : Branch 0 (-22261639/500000 : ℚ) vp00000000101101 := by
  apply branch_left_normalized (c:=vp000000001011010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-22261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-22261639/250000 : ℚ) by norm_num]
  exact coverp000000001011010
private noncomputable def ep000000001011011_0 : Blocks := edgeBlocks% "full/vectors/000000001011011-E-0000.bin"
noncomputable def ep000000001011011 : Blocks := ep000000001011011_0
private theorem idp000000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101101.list =
    C ((2:ℤ)^120) * horner X vp000000001011011.list + horner X ep000000001011011.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001011011 : Branch 1 (-22261639/500000 : ℚ) vp00000000101101 := by
  apply branch_checked idp000000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-22261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-22511639/250000 : ℚ) by norm_num]
  exact coverp000000001011011
theorem coverp00000000101101 : Covers (-22261639/500000 : ℚ) vp00000000101101 := join_branches bp000000001011010 bp000000001011011
private noncomputable def vp0000000010110011_0 : Blocks := edgeBlocks% "full/vectors/0000000010110011-V-0000.bin"
noncomputable def vp0000000010110011 : Blocks := vp0000000010110011_0
theorem coverp0000000010110011 : Covers (-22136639/125000 : ℚ) vp0000000010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010110010_0 : Blocks := edgeBlocks% "full/vectors/0000000010110010-V-0000.bin"
noncomputable def vp0000000010110010 : Blocks := vp0000000010110010_0
theorem coverp0000000010110010 : Covers (-22011639/125000 : ℚ) vp0000000010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011001_0 : Blocks := edgeBlocks% "full/vectors/000000001011001-V-0000.bin"
noncomputable def vp000000001011001 : Blocks := vp000000001011001_0
private theorem bp0000000010110010 : Branch 0 (-22011639/250000 : ℚ) vp000000001011001 := by
  apply branch_left_normalized (c:=vp0000000010110010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-22011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-22011639/125000 : ℚ) by norm_num]
  exact coverp0000000010110010
private noncomputable def ep0000000010110011_0 : Blocks := edgeBlocks% "full/vectors/0000000010110011-E-0000.bin"
noncomputable def ep0000000010110011 : Blocks := ep0000000010110011_0
private theorem idp0000000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011001.list =
    C ((2:ℤ)^67) * horner X vp0000000010110011.list + horner X ep0000000010110011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010110011 : Branch 1 (-22011639/250000 : ℚ) vp000000001011001 := by
  apply branch_checked idp0000000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-22011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-22136639/125000 : ℚ) by norm_num]
  exact coverp0000000010110011
theorem coverp000000001011001 : Covers (-22011639/250000 : ℚ) vp000000001011001 := join_branches bp0000000010110010 bp0000000010110011
private noncomputable def vp0000000010110001_0 : Blocks := edgeBlocks% "full/vectors/0000000010110001-V-0000.bin"
noncomputable def vp0000000010110001 : Blocks := vp0000000010110001_0
theorem coverp0000000010110001 : Covers (-21886639/125000 : ℚ) vp0000000010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010110000_0 : Blocks := edgeBlocks% "full/vectors/0000000010110000-V-0000.bin"
noncomputable def vp0000000010110000 : Blocks := vp0000000010110000_0
theorem coverp0000000010110000 : Covers (-21761639/125000 : ℚ) vp0000000010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001011000_0 : Blocks := edgeBlocks% "full/vectors/000000001011000-V-0000.bin"
noncomputable def vp000000001011000 : Blocks := vp000000001011000_0
private theorem bp0000000010110000 : Branch 0 (-21761639/250000 : ℚ) vp000000001011000 := by
  apply branch_left_normalized (c:=vp0000000010110000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-21761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-21761639/125000 : ℚ) by norm_num]
  exact coverp0000000010110000
private noncomputable def ep0000000010110001_0 : Blocks := edgeBlocks% "full/vectors/0000000010110001-E-0000.bin"
noncomputable def ep0000000010110001 : Blocks := ep0000000010110001_0
private theorem idp0000000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011000.list =
    C ((2:ℤ)^68) * horner X vp0000000010110001.list + horner X ep0000000010110001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010110001 : Branch 1 (-21761639/250000 : ℚ) vp000000001011000 := by
  apply branch_checked idp0000000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-21761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-21886639/125000 : ℚ) by norm_num]
  exact coverp0000000010110001
theorem coverp000000001011000 : Covers (-21761639/250000 : ℚ) vp000000001011000 := join_branches bp0000000010110000 bp0000000010110001
private noncomputable def vp00000000101100_0 : Blocks := edgeBlocks% "full/vectors/00000000101100-V-0000.bin"
noncomputable def vp00000000101100 : Blocks := vp00000000101100_0
private theorem bp000000001011000 : Branch 0 (-21761639/500000 : ℚ) vp00000000101100 := by
  apply branch_left_normalized (c:=vp000000001011000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-21761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-21761639/250000 : ℚ) by norm_num]
  exact coverp000000001011000
private noncomputable def ep000000001011001_0 : Blocks := edgeBlocks% "full/vectors/000000001011001-E-0000.bin"
noncomputable def ep000000001011001 : Blocks := ep000000001011001_0
private theorem idp000000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101100.list =
    C ((2:ℤ)^120) * horner X vp000000001011001.list + horner X ep000000001011001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001011001 : Branch 1 (-21761639/500000 : ℚ) vp00000000101100 := by
  apply branch_checked idp000000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-21761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-22011639/250000 : ℚ) by norm_num]
  exact coverp000000001011001
theorem coverp00000000101100 : Covers (-21761639/500000 : ℚ) vp00000000101100 := join_branches bp000000001011000 bp000000001011001
private noncomputable def vp0000000010110_0 : Blocks := edgeBlocks% "full/vectors/0000000010110-V-0000.bin"
private noncomputable def vp0000000010110_1 : Blocks := edgeBlocks% "full/vectors/0000000010110-V-0001.bin"
noncomputable def vp0000000010110 : Blocks := (Blocks.join vp0000000010110_0 vp0000000010110_1)
private theorem bp00000000101100 : Branch 0 (-21761639/1000000 : ℚ) vp0000000010110 := by
  apply branch_left_normalized (c:=vp00000000101100) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-21761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-21761639/500000 : ℚ) by norm_num]
  exact coverp00000000101100
private noncomputable def ep00000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000101101-E-0000.bin"
private noncomputable def ep00000000101101_1 : Blocks := edgeBlocks% "full/vectors/00000000101101-E-0001.bin"
noncomputable def ep00000000101101 : Blocks := (Blocks.join ep00000000101101_0 ep00000000101101_1)
private theorem idp00000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010110.list =
    C ((2:ℤ)^227) * horner X vp00000000101101.list + horner X ep00000000101101.list := by
  exact edge_identity (B := (2:ℤ)^423) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000101101 : Branch 1 (-21761639/1000000 : ℚ) vp0000000010110 := by
  apply branch_checked idp00000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-21761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-22261639/500000 : ℚ) by norm_num]
  exact coverp00000000101101
theorem coverp0000000010110 : Covers (-21761639/1000000 : ℚ) vp0000000010110 := join_branches bp00000000101100 bp00000000101101
private noncomputable def vp000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000001011-V-0000.bin"
private noncomputable def vp000000001011_1 : Blocks := edgeBlocks% "full/vectors/000000001011-V-0001.bin"
private noncomputable def vp000000001011_2 : Blocks := edgeBlocks% "full/vectors/000000001011-V-0002.bin"
private noncomputable def vp000000001011_3 : Blocks := edgeBlocks% "full/vectors/000000001011-V-0003.bin"
noncomputable def vp000000001011 : Blocks := (Blocks.join (Blocks.join vp000000001011_0 vp000000001011_1) (Blocks.join vp000000001011_2 vp000000001011_3))
private theorem bp0000000010110 : Branch 0 (-21761639/2000000 : ℚ) vp000000001011 := by
  apply branch_left_normalized (c:=vp0000000010110) (k:=0) (m:=223) (by decide +kernel)
  rw [show 2*(-21761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-21761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010110
private noncomputable def ep0000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000010111-E-0000.bin"
private noncomputable def ep0000000010111_1 : Blocks := edgeBlocks% "full/vectors/0000000010111-E-0001.bin"
private noncomputable def ep0000000010111_2 : Blocks := edgeBlocks% "full/vectors/0000000010111-E-0002.bin"
private noncomputable def ep0000000010111_3 : Blocks := edgeBlocks% "full/vectors/0000000010111-E-0003.bin"
noncomputable def ep0000000010111 : Blocks := (Blocks.join (Blocks.join ep0000000010111_0 ep0000000010111_1) (Blocks.join ep0000000010111_2 ep0000000010111_3))
private theorem idp0000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001011.list =
    C ((2:ℤ)^437) * horner X vp0000000010111.list + horner X ep0000000010111.list := by
  exact edge_identity (B := (2:ℤ)^742) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010111 : Branch 1 (-21761639/2000000 : ℚ) vp000000001011 := by
  apply branch_checked idp0000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-21761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-22761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010111
theorem coverp000000001011 : Covers (-21761639/2000000 : ℚ) vp000000001011 := join_branches bp0000000010110 bp0000000010111
private noncomputable def vp0000000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000000010101111-V-0000.bin"
noncomputable def vp0000000010101111 : Blocks := vp0000000010101111_0
theorem coverp0000000010101111 : Covers (-21636639/125000 : ℚ) vp0000000010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010101110_0 : Blocks := edgeBlocks% "full/vectors/0000000010101110-V-0000.bin"
noncomputable def vp0000000010101110 : Blocks := vp0000000010101110_0
theorem coverp0000000010101110 : Covers (-21511639/125000 : ℚ) vp0000000010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010111_0 : Blocks := edgeBlocks% "full/vectors/000000001010111-V-0000.bin"
noncomputable def vp000000001010111 : Blocks := vp000000001010111_0
private theorem bp0000000010101110 : Branch 0 (-21511639/250000 : ℚ) vp000000001010111 := by
  apply branch_left_normalized (c:=vp0000000010101110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-21511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-21511639/125000 : ℚ) by norm_num]
  exact coverp0000000010101110
private noncomputable def ep0000000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000000010101111-E-0000.bin"
noncomputable def ep0000000010101111 : Blocks := ep0000000010101111_0
private theorem idp0000000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010111.list =
    C ((2:ℤ)^68) * horner X vp0000000010101111.list + horner X ep0000000010101111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010101111 : Branch 1 (-21511639/250000 : ℚ) vp000000001010111 := by
  apply branch_checked idp0000000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-21511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-21636639/125000 : ℚ) by norm_num]
  exact coverp0000000010101111
theorem coverp000000001010111 : Covers (-21511639/250000 : ℚ) vp000000001010111 := join_branches bp0000000010101110 bp0000000010101111
private noncomputable def vp0000000010101101_0 : Blocks := edgeBlocks% "full/vectors/0000000010101101-V-0000.bin"
noncomputable def vp0000000010101101 : Blocks := vp0000000010101101_0
theorem coverp0000000010101101 : Covers (-21386639/125000 : ℚ) vp0000000010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010101100_0 : Blocks := edgeBlocks% "full/vectors/0000000010101100-V-0000.bin"
noncomputable def vp0000000010101100 : Blocks := vp0000000010101100_0
theorem coverp0000000010101100 : Covers (-21261639/125000 : ℚ) vp0000000010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010110_0 : Blocks := edgeBlocks% "full/vectors/000000001010110-V-0000.bin"
noncomputable def vp000000001010110 : Blocks := vp000000001010110_0
private theorem bp0000000010101100 : Branch 0 (-21261639/250000 : ℚ) vp000000001010110 := by
  apply branch_left_normalized (c:=vp0000000010101100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-21261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-21261639/125000 : ℚ) by norm_num]
  exact coverp0000000010101100
private noncomputable def ep0000000010101101_0 : Blocks := edgeBlocks% "full/vectors/0000000010101101-E-0000.bin"
noncomputable def ep0000000010101101 : Blocks := ep0000000010101101_0
private theorem idp0000000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010110.list =
    C ((2:ℤ)^68) * horner X vp0000000010101101.list + horner X ep0000000010101101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010101101 : Branch 1 (-21261639/250000 : ℚ) vp000000001010110 := by
  apply branch_checked idp0000000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-21261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-21386639/125000 : ℚ) by norm_num]
  exact coverp0000000010101101
theorem coverp000000001010110 : Covers (-21261639/250000 : ℚ) vp000000001010110 := join_branches bp0000000010101100 bp0000000010101101
private noncomputable def vp00000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000101011-V-0000.bin"
noncomputable def vp00000000101011 : Blocks := vp00000000101011_0
private theorem bp000000001010110 : Branch 0 (-21261639/500000 : ℚ) vp00000000101011 := by
  apply branch_left_normalized (c:=vp000000001010110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-21261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-21261639/250000 : ℚ) by norm_num]
  exact coverp000000001010110
private noncomputable def ep000000001010111_0 : Blocks := edgeBlocks% "full/vectors/000000001010111-E-0000.bin"
noncomputable def ep000000001010111 : Blocks := ep000000001010111_0
private theorem idp000000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101011.list =
    C ((2:ℤ)^121) * horner X vp000000001010111.list + horner X ep000000001010111.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001010111 : Branch 1 (-21261639/500000 : ℚ) vp00000000101011 := by
  apply branch_checked idp000000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-21261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-21511639/250000 : ℚ) by norm_num]
  exact coverp000000001010111
theorem coverp00000000101011 : Covers (-21261639/500000 : ℚ) vp00000000101011 := join_branches bp000000001010110 bp000000001010111
private noncomputable def vp0000000010101011_0 : Blocks := edgeBlocks% "full/vectors/0000000010101011-V-0000.bin"
noncomputable def vp0000000010101011 : Blocks := vp0000000010101011_0
theorem coverp0000000010101011 : Covers (-21136639/125000 : ℚ) vp0000000010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010101010_0 : Blocks := edgeBlocks% "full/vectors/0000000010101010-V-0000.bin"
noncomputable def vp0000000010101010 : Blocks := vp0000000010101010_0
theorem coverp0000000010101010 : Covers (-21011639/125000 : ℚ) vp0000000010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010101_0 : Blocks := edgeBlocks% "full/vectors/000000001010101-V-0000.bin"
noncomputable def vp000000001010101 : Blocks := vp000000001010101_0
private theorem bp0000000010101010 : Branch 0 (-21011639/250000 : ℚ) vp000000001010101 := by
  apply branch_left_normalized (c:=vp0000000010101010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-21011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-21011639/125000 : ℚ) by norm_num]
  exact coverp0000000010101010
private noncomputable def ep0000000010101011_0 : Blocks := edgeBlocks% "full/vectors/0000000010101011-E-0000.bin"
noncomputable def ep0000000010101011 : Blocks := ep0000000010101011_0
private theorem idp0000000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010101.list =
    C ((2:ℤ)^69) * horner X vp0000000010101011.list + horner X ep0000000010101011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010101011 : Branch 1 (-21011639/250000 : ℚ) vp000000001010101 := by
  apply branch_checked idp0000000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-21011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-21136639/125000 : ℚ) by norm_num]
  exact coverp0000000010101011
theorem coverp000000001010101 : Covers (-21011639/250000 : ℚ) vp000000001010101 := join_branches bp0000000010101010 bp0000000010101011
private noncomputable def vp0000000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000000010101001-V-0000.bin"
noncomputable def vp0000000010101001 : Blocks := vp0000000010101001_0
theorem coverp0000000010101001 : Covers (-20886639/125000 : ℚ) vp0000000010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010101000_0 : Blocks := edgeBlocks% "full/vectors/0000000010101000-V-0000.bin"
noncomputable def vp0000000010101000 : Blocks := vp0000000010101000_0
theorem coverp0000000010101000 : Covers (-20761639/125000 : ℚ) vp0000000010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010100_0 : Blocks := edgeBlocks% "full/vectors/000000001010100-V-0000.bin"
noncomputable def vp000000001010100 : Blocks := vp000000001010100_0
private theorem bp0000000010101000 : Branch 0 (-20761639/250000 : ℚ) vp000000001010100 := by
  apply branch_left_normalized (c:=vp0000000010101000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-20761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-20761639/125000 : ℚ) by norm_num]
  exact coverp0000000010101000
private noncomputable def ep0000000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000000010101001-E-0000.bin"
noncomputable def ep0000000010101001 : Blocks := ep0000000010101001_0
private theorem idp0000000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010100.list =
    C ((2:ℤ)^68) * horner X vp0000000010101001.list + horner X ep0000000010101001.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010101001 : Branch 1 (-20761639/250000 : ℚ) vp000000001010100 := by
  apply branch_checked idp0000000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-20761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-20886639/125000 : ℚ) by norm_num]
  exact coverp0000000010101001
theorem coverp000000001010100 : Covers (-20761639/250000 : ℚ) vp000000001010100 := join_branches bp0000000010101000 bp0000000010101001
private noncomputable def vp00000000101010_0 : Blocks := edgeBlocks% "full/vectors/00000000101010-V-0000.bin"
noncomputable def vp00000000101010 : Blocks := vp00000000101010_0
private theorem bp000000001010100 : Branch 0 (-20761639/500000 : ℚ) vp00000000101010 := by
  apply branch_left_normalized (c:=vp000000001010100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-20761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-20761639/250000 : ℚ) by norm_num]
  exact coverp000000001010100
private noncomputable def ep000000001010101_0 : Blocks := edgeBlocks% "full/vectors/000000001010101-E-0000.bin"
noncomputable def ep000000001010101 : Blocks := ep000000001010101_0
private theorem idp000000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101010.list =
    C ((2:ℤ)^123) * horner X vp000000001010101.list + horner X ep000000001010101.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001010101 : Branch 1 (-20761639/500000 : ℚ) vp00000000101010 := by
  apply branch_checked idp000000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-20761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-21011639/250000 : ℚ) by norm_num]
  exact coverp000000001010101
theorem coverp00000000101010 : Covers (-20761639/500000 : ℚ) vp00000000101010 := join_branches bp000000001010100 bp000000001010101
private noncomputable def vp0000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000010101-V-0000.bin"
private noncomputable def vp0000000010101_1 : Blocks := edgeBlocks% "full/vectors/0000000010101-V-0001.bin"
noncomputable def vp0000000010101 : Blocks := (Blocks.join vp0000000010101_0 vp0000000010101_1)
private theorem bp00000000101010 : Branch 0 (-20761639/1000000 : ℚ) vp0000000010101 := by
  apply branch_left_normalized (c:=vp00000000101010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-20761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-20761639/500000 : ℚ) by norm_num]
  exact coverp00000000101010
private noncomputable def ep00000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000101011-E-0000.bin"
private noncomputable def ep00000000101011_1 : Blocks := edgeBlocks% "full/vectors/00000000101011-E-0001.bin"
noncomputable def ep00000000101011 : Blocks := (Blocks.join ep00000000101011_0 ep00000000101011_1)
private theorem idp00000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010101.list =
    C ((2:ℤ)^232) * horner X vp00000000101011.list + horner X ep00000000101011.list := by
  exact edge_identity (B := (2:ℤ)^431) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000101011 : Branch 1 (-20761639/1000000 : ℚ) vp0000000010101 := by
  apply branch_checked idp00000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-20761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-21261639/500000 : ℚ) by norm_num]
  exact coverp00000000101011
theorem coverp0000000010101 : Covers (-20761639/1000000 : ℚ) vp0000000010101 := join_branches bp00000000101010 bp00000000101011
private noncomputable def vp0000000010100111_0 : Blocks := edgeBlocks% "full/vectors/0000000010100111-V-0000.bin"
noncomputable def vp0000000010100111 : Blocks := vp0000000010100111_0
theorem coverp0000000010100111 : Covers (-20636639/125000 : ℚ) vp0000000010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010100110_0 : Blocks := edgeBlocks% "full/vectors/0000000010100110-V-0000.bin"
noncomputable def vp0000000010100110 : Blocks := vp0000000010100110_0
theorem coverp0000000010100110 : Covers (-20511639/125000 : ℚ) vp0000000010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010011_0 : Blocks := edgeBlocks% "full/vectors/000000001010011-V-0000.bin"
noncomputable def vp000000001010011 : Blocks := vp000000001010011_0
private theorem bp0000000010100110 : Branch 0 (-20511639/250000 : ℚ) vp000000001010011 := by
  apply branch_left_normalized (c:=vp0000000010100110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-20511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-20511639/125000 : ℚ) by norm_num]
  exact coverp0000000010100110
private noncomputable def ep0000000010100111_0 : Blocks := edgeBlocks% "full/vectors/0000000010100111-E-0000.bin"
noncomputable def ep0000000010100111 : Blocks := ep0000000010100111_0
private theorem idp0000000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010011.list =
    C ((2:ℤ)^70) * horner X vp0000000010100111.list + horner X ep0000000010100111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010100111 : Branch 1 (-20511639/250000 : ℚ) vp000000001010011 := by
  apply branch_checked idp0000000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-20511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-20636639/125000 : ℚ) by norm_num]
  exact coverp0000000010100111
theorem coverp000000001010011 : Covers (-20511639/250000 : ℚ) vp000000001010011 := join_branches bp0000000010100110 bp0000000010100111
private noncomputable def vp0000000010100101_0 : Blocks := edgeBlocks% "full/vectors/0000000010100101-V-0000.bin"
noncomputable def vp0000000010100101 : Blocks := vp0000000010100101_0
theorem coverp0000000010100101 : Covers (-20386639/125000 : ℚ) vp0000000010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010100100_0 : Blocks := edgeBlocks% "full/vectors/0000000010100100-V-0000.bin"
noncomputable def vp0000000010100100 : Blocks := vp0000000010100100_0
theorem coverp0000000010100100 : Covers (-20261639/125000 : ℚ) vp0000000010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010010_0 : Blocks := edgeBlocks% "full/vectors/000000001010010-V-0000.bin"
noncomputable def vp000000001010010 : Blocks := vp000000001010010_0
private theorem bp0000000010100100 : Branch 0 (-20261639/250000 : ℚ) vp000000001010010 := by
  apply branch_left_normalized (c:=vp0000000010100100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-20261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-20261639/125000 : ℚ) by norm_num]
  exact coverp0000000010100100
private noncomputable def ep0000000010100101_0 : Blocks := edgeBlocks% "full/vectors/0000000010100101-E-0000.bin"
noncomputable def ep0000000010100101 : Blocks := ep0000000010100101_0
private theorem idp0000000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010010.list =
    C ((2:ℤ)^70) * horner X vp0000000010100101.list + horner X ep0000000010100101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010100101 : Branch 1 (-20261639/250000 : ℚ) vp000000001010010 := by
  apply branch_checked idp0000000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-20261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-20386639/125000 : ℚ) by norm_num]
  exact coverp0000000010100101
theorem coverp000000001010010 : Covers (-20261639/250000 : ℚ) vp000000001010010 := join_branches bp0000000010100100 bp0000000010100101
private noncomputable def vp00000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000101001-V-0000.bin"
noncomputable def vp00000000101001 : Blocks := vp00000000101001_0
private theorem bp000000001010010 : Branch 0 (-20261639/500000 : ℚ) vp00000000101001 := by
  apply branch_left_normalized (c:=vp000000001010010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-20261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-20261639/250000 : ℚ) by norm_num]
  exact coverp000000001010010
private noncomputable def ep000000001010011_0 : Blocks := edgeBlocks% "full/vectors/000000001010011-E-0000.bin"
noncomputable def ep000000001010011 : Blocks := ep000000001010011_0
private theorem idp000000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101001.list =
    C ((2:ℤ)^126) * horner X vp000000001010011.list + horner X ep000000001010011.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001010011 : Branch 1 (-20261639/500000 : ℚ) vp00000000101001 := by
  apply branch_checked idp000000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-20261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-20511639/250000 : ℚ) by norm_num]
  exact coverp000000001010011
theorem coverp00000000101001 : Covers (-20261639/500000 : ℚ) vp00000000101001 := join_branches bp000000001010010 bp000000001010011
private noncomputable def vp0000000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000000010100011-V-0000.bin"
noncomputable def vp0000000010100011 : Blocks := vp0000000010100011_0
theorem coverp0000000010100011 : Covers (-20136639/125000 : ℚ) vp0000000010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010100010_0 : Blocks := edgeBlocks% "full/vectors/0000000010100010-V-0000.bin"
noncomputable def vp0000000010100010 : Blocks := vp0000000010100010_0
theorem coverp0000000010100010 : Covers (-20011639/125000 : ℚ) vp0000000010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010001_0 : Blocks := edgeBlocks% "full/vectors/000000001010001-V-0000.bin"
noncomputable def vp000000001010001 : Blocks := vp000000001010001_0
private theorem bp0000000010100010 : Branch 0 (-20011639/250000 : ℚ) vp000000001010001 := by
  apply branch_left_normalized (c:=vp0000000010100010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-20011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-20011639/125000 : ℚ) by norm_num]
  exact coverp0000000010100010
private noncomputable def ep0000000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000000010100011-E-0000.bin"
noncomputable def ep0000000010100011 : Blocks := ep0000000010100011_0
private theorem idp0000000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010001.list =
    C ((2:ℤ)^71) * horner X vp0000000010100011.list + horner X ep0000000010100011.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010100011 : Branch 1 (-20011639/250000 : ℚ) vp000000001010001 := by
  apply branch_checked idp0000000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-20011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-20136639/125000 : ℚ) by norm_num]
  exact coverp0000000010100011
theorem coverp000000001010001 : Covers (-20011639/250000 : ℚ) vp000000001010001 := join_branches bp0000000010100010 bp0000000010100011
private noncomputable def vp0000000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000010100001-V-0000.bin"
noncomputable def vp0000000010100001 : Blocks := vp0000000010100001_0
theorem coverp0000000010100001 : Covers (-19886639/125000 : ℚ) vp0000000010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010100000_0 : Blocks := edgeBlocks% "full/vectors/0000000010100000-V-0000.bin"
noncomputable def vp0000000010100000 : Blocks := vp0000000010100000_0
theorem coverp0000000010100000 : Covers (-19761639/125000 : ℚ) vp0000000010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001010000_0 : Blocks := edgeBlocks% "full/vectors/000000001010000-V-0000.bin"
noncomputable def vp000000001010000 : Blocks := vp000000001010000_0
private theorem bp0000000010100000 : Branch 0 (-19761639/250000 : ℚ) vp000000001010000 := by
  apply branch_left_normalized (c:=vp0000000010100000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-19761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-19761639/125000 : ℚ) by norm_num]
  exact coverp0000000010100000
private noncomputable def ep0000000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000010100001-E-0000.bin"
noncomputable def ep0000000010100001 : Blocks := ep0000000010100001_0
private theorem idp0000000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010000.list =
    C ((2:ℤ)^71) * horner X vp0000000010100001.list + horner X ep0000000010100001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010100001 : Branch 1 (-19761639/250000 : ℚ) vp000000001010000 := by
  apply branch_checked idp0000000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-19761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-19886639/125000 : ℚ) by norm_num]
  exact coverp0000000010100001
theorem coverp000000001010000 : Covers (-19761639/250000 : ℚ) vp000000001010000 := join_branches bp0000000010100000 bp0000000010100001
private noncomputable def vp00000000101000_0 : Blocks := edgeBlocks% "full/vectors/00000000101000-V-0000.bin"
noncomputable def vp00000000101000 : Blocks := vp00000000101000_0
private theorem bp000000001010000 : Branch 0 (-19761639/500000 : ℚ) vp00000000101000 := by
  apply branch_left_normalized (c:=vp000000001010000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-19761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-19761639/250000 : ℚ) by norm_num]
  exact coverp000000001010000
private noncomputable def ep000000001010001_0 : Blocks := edgeBlocks% "full/vectors/000000001010001-E-0000.bin"
noncomputable def ep000000001010001 : Blocks := ep000000001010001_0
private theorem idp000000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101000.list =
    C ((2:ℤ)^128) * horner X vp000000001010001.list + horner X ep000000001010001.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001010001 : Branch 1 (-19761639/500000 : ℚ) vp00000000101000 := by
  apply branch_checked idp000000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-19761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-20011639/250000 : ℚ) by norm_num]
  exact coverp000000001010001
theorem coverp00000000101000 : Covers (-19761639/500000 : ℚ) vp00000000101000 := join_branches bp000000001010000 bp000000001010001
private noncomputable def vp0000000010100_0 : Blocks := edgeBlocks% "full/vectors/0000000010100-V-0000.bin"
private noncomputable def vp0000000010100_1 : Blocks := edgeBlocks% "full/vectors/0000000010100-V-0001.bin"
noncomputable def vp0000000010100 : Blocks := (Blocks.join vp0000000010100_0 vp0000000010100_1)
private theorem bp00000000101000 : Branch 0 (-19761639/1000000 : ℚ) vp0000000010100 := by
  apply branch_left_normalized (c:=vp00000000101000) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-19761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-19761639/500000 : ℚ) by norm_num]
  exact coverp00000000101000
private noncomputable def ep00000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000101001-E-0000.bin"
private noncomputable def ep00000000101001_1 : Blocks := edgeBlocks% "full/vectors/00000000101001-E-0001.bin"
noncomputable def ep00000000101001 : Blocks := (Blocks.join ep00000000101001_0 ep00000000101001_1)
private theorem idp00000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010100.list =
    C ((2:ℤ)^239) * horner X vp00000000101001.list + horner X ep00000000101001.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000101001 : Branch 1 (-19761639/1000000 : ℚ) vp0000000010100 := by
  apply branch_checked idp00000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-19761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-20261639/500000 : ℚ) by norm_num]
  exact coverp00000000101001
theorem coverp0000000010100 : Covers (-19761639/1000000 : ℚ) vp0000000010100 := join_branches bp00000000101000 bp00000000101001
private noncomputable def vp000000001010_0 : Blocks := edgeBlocks% "full/vectors/000000001010-V-0000.bin"
private noncomputable def vp000000001010_1 : Blocks := edgeBlocks% "full/vectors/000000001010-V-0001.bin"
private noncomputable def vp000000001010_2 : Blocks := edgeBlocks% "full/vectors/000000001010-V-0002.bin"
private noncomputable def vp000000001010_3 : Blocks := edgeBlocks% "full/vectors/000000001010-V-0003.bin"
noncomputable def vp000000001010 : Blocks := (Blocks.join (Blocks.join vp000000001010_0 vp000000001010_1) (Blocks.join vp000000001010_2 vp000000001010_3))
private theorem bp0000000010100 : Branch 0 (-19761639/2000000 : ℚ) vp000000001010 := by
  apply branch_left_normalized (c:=vp0000000010100) (k:=0) (m:=234) (by decide +kernel)
  rw [show 2*(-19761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-19761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010100
private noncomputable def ep0000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000010101-E-0000.bin"
private noncomputable def ep0000000010101_1 : Blocks := edgeBlocks% "full/vectors/0000000010101-E-0001.bin"
private noncomputable def ep0000000010101_2 : Blocks := edgeBlocks% "full/vectors/0000000010101-E-0002.bin"
private noncomputable def ep0000000010101_3 : Blocks := edgeBlocks% "full/vectors/0000000010101-E-0003.bin"
noncomputable def ep0000000010101 : Blocks := (Blocks.join (Blocks.join ep0000000010101_0 ep0000000010101_1) (Blocks.join ep0000000010101_2 ep0000000010101_3))
private theorem idp0000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001010.list =
    C ((2:ℤ)^461) * horner X vp0000000010101.list + horner X ep0000000010101.list := by
  exact edge_identity (B := (2:ℤ)^777) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010101 : Branch 1 (-19761639/2000000 : ℚ) vp000000001010 := by
  apply branch_checked idp0000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-19761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-20761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010101
theorem coverp000000001010 : Covers (-19761639/2000000 : ℚ) vp000000001010 := join_branches bp0000000010100 bp0000000010101
private noncomputable def vp00000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0000.bin"
private noncomputable def vp00000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0001.bin"
private noncomputable def vp00000000101_2 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0002.bin"
private noncomputable def vp00000000101_3 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0003.bin"
private noncomputable def vp00000000101_4 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0004.bin"
private noncomputable def vp00000000101_5 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0005.bin"
private noncomputable def vp00000000101_6 : Blocks := edgeBlocks% "full/vectors/00000000101-V-0006.bin"
noncomputable def vp00000000101 : Blocks := (Blocks.join (Blocks.join vp00000000101_0 (Blocks.join vp00000000101_1 vp00000000101_2)) (Blocks.join (Blocks.join vp00000000101_3 vp00000000101_4) (Blocks.join vp00000000101_5 vp00000000101_6)))
private theorem bp000000001010 : Branch 0 (-19761639/4000000 : ℚ) vp00000000101 := by
  apply branch_left_normalized (c:=vp000000001010) (k:=0) (m:=452) (by decide +kernel)
  rw [show 2*(-19761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-19761639/2000000 : ℚ) by norm_num]
  exact coverp000000001010
private noncomputable def ep000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0000.bin"
private noncomputable def ep000000001011_1 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0001.bin"
private noncomputable def ep000000001011_2 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0002.bin"
private noncomputable def ep000000001011_3 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0003.bin"
private noncomputable def ep000000001011_4 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0004.bin"
private noncomputable def ep000000001011_5 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0005.bin"
private noncomputable def ep000000001011_6 : Blocks := edgeBlocks% "full/vectors/000000001011-E-0006.bin"
noncomputable def ep000000001011 : Blocks := (Blocks.join (Blocks.join ep000000001011_0 (Blocks.join ep000000001011_1 ep000000001011_2)) (Blocks.join (Blocks.join ep000000001011_3 ep000000001011_4) (Blocks.join ep000000001011_5 ep000000001011_6)))
private theorem idp000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000101.list =
    C ((2:ℤ)^898) * horner X vp000000001011.list + horner X ep000000001011.list := by
  exact edge_identity (B := (2:ℤ)^1439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001011 : Branch 1 (-19761639/4000000 : ℚ) vp00000000101 := by
  apply branch_checked idp000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-19761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-21761639/2000000 : ℚ) by norm_num]
  exact coverp000000001011
theorem coverp00000000101 : Covers (-19761639/4000000 : ℚ) vp00000000101 := join_branches bp000000001010 bp000000001011
end NextProof.EdgeFull

