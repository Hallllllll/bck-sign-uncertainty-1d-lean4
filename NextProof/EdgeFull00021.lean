import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00020

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000010011111_0 : Blocks := edgeBlocks% "full/vectors/0000000010011111-V-0000.bin"
noncomputable def vp0000000010011111 : Blocks := vp0000000010011111_0
theorem coverp0000000010011111 : Covers (-19636639/125000 : ℚ) vp0000000010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010011110_0 : Blocks := edgeBlocks% "full/vectors/0000000010011110-V-0000.bin"
noncomputable def vp0000000010011110 : Blocks := vp0000000010011110_0
theorem coverp0000000010011110 : Covers (-19511639/125000 : ℚ) vp0000000010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001111_0 : Blocks := edgeBlocks% "full/vectors/000000001001111-V-0000.bin"
noncomputable def vp000000001001111 : Blocks := vp000000001001111_0
private theorem bp0000000010011110 : Branch 0 (-19511639/250000 : ℚ) vp000000001001111 := by
  apply branch_left_normalized (c:=vp0000000010011110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-19511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-19511639/125000 : ℚ) by norm_num]
  exact coverp0000000010011110
private noncomputable def ep0000000010011111_0 : Blocks := edgeBlocks% "full/vectors/0000000010011111-E-0000.bin"
noncomputable def ep0000000010011111 : Blocks := ep0000000010011111_0
private theorem idp0000000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001111.list =
    C ((2:ℤ)^72) * horner X vp0000000010011111.list + horner X ep0000000010011111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010011111 : Branch 1 (-19511639/250000 : ℚ) vp000000001001111 := by
  apply branch_checked idp0000000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-19511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-19636639/125000 : ℚ) by norm_num]
  exact coverp0000000010011111
theorem coverp000000001001111 : Covers (-19511639/250000 : ℚ) vp000000001001111 := join_branches bp0000000010011110 bp0000000010011111
private noncomputable def vp0000000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000000010011101-V-0000.bin"
noncomputable def vp0000000010011101 : Blocks := vp0000000010011101_0
theorem coverp0000000010011101 : Covers (-19386639/125000 : ℚ) vp0000000010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010011100_0 : Blocks := edgeBlocks% "full/vectors/0000000010011100-V-0000.bin"
noncomputable def vp0000000010011100 : Blocks := vp0000000010011100_0
theorem coverp0000000010011100 : Covers (-19261639/125000 : ℚ) vp0000000010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001110_0 : Blocks := edgeBlocks% "full/vectors/000000001001110-V-0000.bin"
noncomputable def vp000000001001110 : Blocks := vp000000001001110_0
private theorem bp0000000010011100 : Branch 0 (-19261639/250000 : ℚ) vp000000001001110 := by
  apply branch_left_normalized (c:=vp0000000010011100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-19261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-19261639/125000 : ℚ) by norm_num]
  exact coverp0000000010011100
private noncomputable def ep0000000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000000010011101-E-0000.bin"
noncomputable def ep0000000010011101 : Blocks := ep0000000010011101_0
private theorem idp0000000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001110.list =
    C ((2:ℤ)^72) * horner X vp0000000010011101.list + horner X ep0000000010011101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010011101 : Branch 1 (-19261639/250000 : ℚ) vp000000001001110 := by
  apply branch_checked idp0000000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-19261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-19386639/125000 : ℚ) by norm_num]
  exact coverp0000000010011101
theorem coverp000000001001110 : Covers (-19261639/250000 : ℚ) vp000000001001110 := join_branches bp0000000010011100 bp0000000010011101
private noncomputable def vp00000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000100111-V-0000.bin"
noncomputable def vp00000000100111 : Blocks := vp00000000100111_0
private theorem bp000000001001110 : Branch 0 (-19261639/500000 : ℚ) vp00000000100111 := by
  apply branch_left_normalized (c:=vp000000001001110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-19261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-19261639/250000 : ℚ) by norm_num]
  exact coverp000000001001110
private noncomputable def ep000000001001111_0 : Blocks := edgeBlocks% "full/vectors/000000001001111-E-0000.bin"
noncomputable def ep000000001001111 : Blocks := ep000000001001111_0
private theorem idp000000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100111.list =
    C ((2:ℤ)^131) * horner X vp000000001001111.list + horner X ep000000001001111.list := by
  exact edge_identity (B := (2:ℤ)^279) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001111 : Branch 1 (-19261639/500000 : ℚ) vp00000000100111 := by
  apply branch_checked idp000000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-19261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-19511639/250000 : ℚ) by norm_num]
  exact coverp000000001001111
theorem coverp00000000100111 : Covers (-19261639/500000 : ℚ) vp00000000100111 := join_branches bp000000001001110 bp000000001001111
private noncomputable def vp0000000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000000010011011-V-0000.bin"
noncomputable def vp0000000010011011 : Blocks := vp0000000010011011_0
theorem coverp0000000010011011 : Covers (-19136639/125000 : ℚ) vp0000000010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010011010_0 : Blocks := edgeBlocks% "full/vectors/0000000010011010-V-0000.bin"
noncomputable def vp0000000010011010 : Blocks := vp0000000010011010_0
theorem coverp0000000010011010 : Covers (-19011639/125000 : ℚ) vp0000000010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001101_0 : Blocks := edgeBlocks% "full/vectors/000000001001101-V-0000.bin"
noncomputable def vp000000001001101 : Blocks := vp000000001001101_0
private theorem bp0000000010011010 : Branch 0 (-19011639/250000 : ℚ) vp000000001001101 := by
  apply branch_left_normalized (c:=vp0000000010011010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-19011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-19011639/125000 : ℚ) by norm_num]
  exact coverp0000000010011010
private noncomputable def ep0000000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000000010011011-E-0000.bin"
noncomputable def ep0000000010011011 : Blocks := ep0000000010011011_0
private theorem idp0000000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001101.list =
    C ((2:ℤ)^73) * horner X vp0000000010011011.list + horner X ep0000000010011011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010011011 : Branch 1 (-19011639/250000 : ℚ) vp000000001001101 := by
  apply branch_checked idp0000000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-19011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-19136639/125000 : ℚ) by norm_num]
  exact coverp0000000010011011
theorem coverp000000001001101 : Covers (-19011639/250000 : ℚ) vp000000001001101 := join_branches bp0000000010011010 bp0000000010011011
private noncomputable def vp0000000010011001_0 : Blocks := edgeBlocks% "full/vectors/0000000010011001-V-0000.bin"
noncomputable def vp0000000010011001 : Blocks := vp0000000010011001_0
theorem coverp0000000010011001 : Covers (-18886639/125000 : ℚ) vp0000000010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010011000_0 : Blocks := edgeBlocks% "full/vectors/0000000010011000-V-0000.bin"
noncomputable def vp0000000010011000 : Blocks := vp0000000010011000_0
theorem coverp0000000010011000 : Covers (-18761639/125000 : ℚ) vp0000000010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001100_0 : Blocks := edgeBlocks% "full/vectors/000000001001100-V-0000.bin"
noncomputable def vp000000001001100 : Blocks := vp000000001001100_0
private theorem bp0000000010011000 : Branch 0 (-18761639/250000 : ℚ) vp000000001001100 := by
  apply branch_left_normalized (c:=vp0000000010011000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-18761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-18761639/125000 : ℚ) by norm_num]
  exact coverp0000000010011000
private noncomputable def ep0000000010011001_0 : Blocks := edgeBlocks% "full/vectors/0000000010011001-E-0000.bin"
noncomputable def ep0000000010011001 : Blocks := ep0000000010011001_0
private theorem idp0000000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001100.list =
    C ((2:ℤ)^74) * horner X vp0000000010011001.list + horner X ep0000000010011001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010011001 : Branch 1 (-18761639/250000 : ℚ) vp000000001001100 := by
  apply branch_checked idp0000000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-18761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-18886639/125000 : ℚ) by norm_num]
  exact coverp0000000010011001
theorem coverp000000001001100 : Covers (-18761639/250000 : ℚ) vp000000001001100 := join_branches bp0000000010011000 bp0000000010011001
private noncomputable def vp00000000100110_0 : Blocks := edgeBlocks% "full/vectors/00000000100110-V-0000.bin"
private noncomputable def vp00000000100110_1 : Blocks := edgeBlocks% "full/vectors/00000000100110-V-0001.bin"
noncomputable def vp00000000100110 : Blocks := (Blocks.join vp00000000100110_0 vp00000000100110_1)
private theorem bp000000001001100 : Branch 0 (-18761639/500000 : ℚ) vp00000000100110 := by
  apply branch_left_normalized (c:=vp000000001001100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-18761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-18761639/250000 : ℚ) by norm_num]
  exact coverp000000001001100
private noncomputable def ep000000001001101_0 : Blocks := edgeBlocks% "full/vectors/000000001001101-E-0000.bin"
private noncomputable def ep000000001001101_1 : Blocks := edgeBlocks% "full/vectors/000000001001101-E-0001.bin"
noncomputable def ep000000001001101 : Blocks := (Blocks.join ep000000001001101_0 ep000000001001101_1)
private theorem idp000000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100110.list =
    C ((2:ℤ)^134) * horner X vp000000001001101.list + horner X ep000000001001101.list := by
  exact edge_identity (B := (2:ℤ)^285) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001101 : Branch 1 (-18761639/500000 : ℚ) vp00000000100110 := by
  apply branch_checked idp000000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-18761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-19011639/250000 : ℚ) by norm_num]
  exact coverp000000001001101
theorem coverp00000000100110 : Covers (-18761639/500000 : ℚ) vp00000000100110 := join_branches bp000000001001100 bp000000001001101
private noncomputable def vp0000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000010011-V-0000.bin"
private noncomputable def vp0000000010011_1 : Blocks := edgeBlocks% "full/vectors/0000000010011-V-0001.bin"
noncomputable def vp0000000010011 : Blocks := (Blocks.join vp0000000010011_0 vp0000000010011_1)
private theorem bp00000000100110 : Branch 0 (-18761639/1000000 : ℚ) vp0000000010011 := by
  apply branch_left_normalized (c:=vp00000000100110) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-18761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-18761639/500000 : ℚ) by norm_num]
  exact coverp00000000100110
private noncomputable def ep00000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000100111-E-0000.bin"
private noncomputable def ep00000000100111_1 : Blocks := edgeBlocks% "full/vectors/00000000100111-E-0001.bin"
noncomputable def ep00000000100111 : Blocks := (Blocks.join ep00000000100111_0 ep00000000100111_1)
private theorem idp00000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010011.list =
    C ((2:ℤ)^248) * horner X vp00000000100111.list + horner X ep00000000100111.list := by
  exact edge_identity (B := (2:ℤ)^456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100111 : Branch 1 (-18761639/1000000 : ℚ) vp0000000010011 := by
  apply branch_checked idp00000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-18761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-19261639/500000 : ℚ) by norm_num]
  exact coverp00000000100111
theorem coverp0000000010011 : Covers (-18761639/1000000 : ℚ) vp0000000010011 := join_branches bp00000000100110 bp00000000100111
private noncomputable def vp0000000010010111_0 : Blocks := edgeBlocks% "full/vectors/0000000010010111-V-0000.bin"
noncomputable def vp0000000010010111 : Blocks := vp0000000010010111_0
theorem coverp0000000010010111 : Covers (-18636639/125000 : ℚ) vp0000000010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010110_0 : Blocks := edgeBlocks% "full/vectors/0000000010010110-V-0000.bin"
noncomputable def vp0000000010010110 : Blocks := vp0000000010010110_0
theorem coverp0000000010010110 : Covers (-18511639/125000 : ℚ) vp0000000010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001011_0 : Blocks := edgeBlocks% "full/vectors/000000001001011-V-0000.bin"
noncomputable def vp000000001001011 : Blocks := vp000000001001011_0
private theorem bp0000000010010110 : Branch 0 (-18511639/250000 : ℚ) vp000000001001011 := by
  apply branch_left_normalized (c:=vp0000000010010110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-18511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-18511639/125000 : ℚ) by norm_num]
  exact coverp0000000010010110
private noncomputable def ep0000000010010111_0 : Blocks := edgeBlocks% "full/vectors/0000000010010111-E-0000.bin"
noncomputable def ep0000000010010111 : Blocks := ep0000000010010111_0
private theorem idp0000000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001011.list =
    C ((2:ℤ)^76) * horner X vp0000000010010111.list + horner X ep0000000010010111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010111 : Branch 1 (-18511639/250000 : ℚ) vp000000001001011 := by
  apply branch_checked idp0000000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-18511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-18636639/125000 : ℚ) by norm_num]
  exact coverp0000000010010111
theorem coverp000000001001011 : Covers (-18511639/250000 : ℚ) vp000000001001011 := join_branches bp0000000010010110 bp0000000010010111
private noncomputable def vp0000000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000000010010101-V-0000.bin"
noncomputable def vp0000000010010101 : Blocks := vp0000000010010101_0
theorem coverp0000000010010101 : Covers (-18386639/125000 : ℚ) vp0000000010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100101001_0 : Blocks := edgeBlocks% "full/vectors/00000000100101001-V-0000.bin"
noncomputable def vp00000000100101001 : Blocks := vp00000000100101001_0
theorem coverp00000000100101001 : Covers (-18324139/62500 : ℚ) vp00000000100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001010001_0 : Blocks := edgeBlocks% "full/vectors/000000001001010001-V-0000.bin"
noncomputable def vp000000001001010001 : Blocks := vp000000001001010001_0
theorem coverp000000001001010001 : Covers (-18292889/31250 : ℚ) vp000000001001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000010010100001-V-0000.bin"
noncomputable def vp0000000010010100001 : Blocks := vp0000000010010100001_0
theorem coverp0000000010010100001 : Covers (-18277264/15625 : ℚ) vp0000000010010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100101000001_0 : Blocks := edgeBlocks% "full/vectors/00000000100101000001-V-0000.bin"
noncomputable def vp00000000100101000001 : Blocks := vp00000000100101000001_0
theorem coverp00000000100101000001 : Covers (-36538903/15625 : ℚ) vp00000000100101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100101000000_0 : Blocks := edgeBlocks% "full/vectors/00000000100101000000-V-0000.bin"
noncomputable def vp00000000100101000000 : Blocks := vp00000000100101000000_0
theorem coverp00000000100101000000 : Covers (-36523278/15625 : ℚ) vp00000000100101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010100000_0 : Blocks := edgeBlocks% "full/vectors/0000000010010100000-V-0000.bin"
noncomputable def vp0000000010010100000 : Blocks := vp0000000010010100000_0
private theorem bp00000000100101000000 : Branch 0 (-18261639/15625 : ℚ) vp0000000010010100000 := by
  apply branch_left_normalized (c:=vp00000000100101000000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-18261639/15625 : ℚ) - ((0:ℤ):ℚ) = (-36523278/15625 : ℚ) by norm_num]
  exact coverp00000000100101000000
private noncomputable def ep00000000100101000001_0 : Blocks := edgeBlocks% "full/vectors/00000000100101000001-E-0000.bin"
noncomputable def ep00000000100101000001 : Blocks := ep00000000100101000001_0
private theorem idp00000000100101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010100000.list =
    C ((2:ℤ)^17) * horner X vp00000000100101000001.list + horner X ep00000000100101000001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100101000001 : Branch 1 (-18261639/15625 : ℚ) vp0000000010010100000 := by
  apply branch_checked idp00000000100101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/15625 : ℚ) - ((1:ℤ):ℚ) = (-36538903/15625 : ℚ) by norm_num]
  exact coverp00000000100101000001
theorem coverp0000000010010100000 : Covers (-18261639/15625 : ℚ) vp0000000010010100000 := join_branches bp00000000100101000000 bp00000000100101000001
private noncomputable def vp000000001001010000_0 : Blocks := edgeBlocks% "full/vectors/000000001001010000-V-0000.bin"
noncomputable def vp000000001001010000 : Blocks := vp000000001001010000_0
private theorem bp0000000010010100000 : Branch 0 (-18261639/31250 : ℚ) vp000000001001010000 := by
  apply branch_left_normalized (c:=vp0000000010010100000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-18261639/31250 : ℚ) - ((0:ℤ):ℚ) = (-18261639/15625 : ℚ) by norm_num]
  exact coverp0000000010010100000
private noncomputable def ep0000000010010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000010010100001-E-0000.bin"
noncomputable def ep0000000010010100001 : Blocks := ep0000000010010100001_0
private theorem idp0000000010010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001010000.list =
    C ((2:ℤ)^23) * horner X vp0000000010010100001.list + horner X ep0000000010010100001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010100001 : Branch 1 (-18261639/31250 : ℚ) vp000000001001010000 := by
  apply branch_checked idp0000000010010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/31250 : ℚ) - ((1:ℤ):ℚ) = (-18277264/15625 : ℚ) by norm_num]
  exact coverp0000000010010100001
theorem coverp000000001001010000 : Covers (-18261639/31250 : ℚ) vp000000001001010000 := join_branches bp0000000010010100000 bp0000000010010100001
private noncomputable def vp00000000100101000_0 : Blocks := edgeBlocks% "full/vectors/00000000100101000-V-0000.bin"
noncomputable def vp00000000100101000 : Blocks := vp00000000100101000_0
private theorem bp000000001001010000 : Branch 0 (-18261639/62500 : ℚ) vp00000000100101000 := by
  apply branch_left_normalized (c:=vp000000001001010000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-18261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-18261639/31250 : ℚ) by norm_num]
  exact coverp000000001001010000
private noncomputable def ep000000001001010001_0 : Blocks := edgeBlocks% "full/vectors/000000001001010001-E-0000.bin"
noncomputable def ep000000001001010001 : Blocks := ep000000001001010001_0
private theorem idp000000001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100101000.list =
    C ((2:ℤ)^35) * horner X vp000000001001010001.list + horner X ep000000001001010001.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001010001 : Branch 1 (-18261639/62500 : ℚ) vp00000000100101000 := by
  apply branch_checked idp000000001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-18292889/31250 : ℚ) by norm_num]
  exact coverp000000001001010001
theorem coverp00000000100101000 : Covers (-18261639/62500 : ℚ) vp00000000100101000 := join_branches bp000000001001010000 bp000000001001010001
private noncomputable def vp0000000010010100_0 : Blocks := edgeBlocks% "full/vectors/0000000010010100-V-0000.bin"
noncomputable def vp0000000010010100 : Blocks := vp0000000010010100_0
private theorem bp00000000100101000 : Branch 0 (-18261639/125000 : ℚ) vp0000000010010100 := by
  apply branch_left_normalized (c:=vp00000000100101000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-18261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-18261639/62500 : ℚ) by norm_num]
  exact coverp00000000100101000
private noncomputable def ep00000000100101001_0 : Blocks := edgeBlocks% "full/vectors/00000000100101001-E-0000.bin"
noncomputable def ep00000000100101001 : Blocks := ep00000000100101001_0
private theorem idp00000000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010100.list =
    C ((2:ℤ)^54) * horner X vp00000000100101001.list + horner X ep00000000100101001.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100101001 : Branch 1 (-18261639/125000 : ℚ) vp0000000010010100 := by
  apply branch_checked idp00000000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-18324139/62500 : ℚ) by norm_num]
  exact coverp00000000100101001
theorem coverp0000000010010100 : Covers (-18261639/125000 : ℚ) vp0000000010010100 := join_branches bp00000000100101000 bp00000000100101001
private noncomputable def vp000000001001010_0 : Blocks := edgeBlocks% "full/vectors/000000001001010-V-0000.bin"
noncomputable def vp000000001001010 : Blocks := vp000000001001010_0
private theorem bp0000000010010100 : Branch 0 (-18261639/250000 : ℚ) vp000000001001010 := by
  apply branch_left_normalized (c:=vp0000000010010100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-18261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-18261639/125000 : ℚ) by norm_num]
  exact coverp0000000010010100
private noncomputable def ep0000000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000000010010101-E-0000.bin"
noncomputable def ep0000000010010101 : Blocks := ep0000000010010101_0
private theorem idp0000000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001010.list =
    C ((2:ℤ)^87) * horner X vp0000000010010101.list + horner X ep0000000010010101.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010101 : Branch 1 (-18261639/250000 : ℚ) vp000000001001010 := by
  apply branch_checked idp0000000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-18386639/125000 : ℚ) by norm_num]
  exact coverp0000000010010101
theorem coverp000000001001010 : Covers (-18261639/250000 : ℚ) vp000000001001010 := join_branches bp0000000010010100 bp0000000010010101
private noncomputable def vp00000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000100101-V-0000.bin"
private noncomputable def vp00000000100101_1 : Blocks := edgeBlocks% "full/vectors/00000000100101-V-0001.bin"
noncomputable def vp00000000100101 : Blocks := (Blocks.join vp00000000100101_0 vp00000000100101_1)
private theorem bp000000001001010 : Branch 0 (-18261639/500000 : ℚ) vp00000000100101 := by
  apply branch_left_normalized (c:=vp000000001001010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-18261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-18261639/250000 : ℚ) by norm_num]
  exact coverp000000001001010
private noncomputable def ep000000001001011_0 : Blocks := edgeBlocks% "full/vectors/000000001001011-E-0000.bin"
private noncomputable def ep000000001001011_1 : Blocks := edgeBlocks% "full/vectors/000000001001011-E-0001.bin"
noncomputable def ep000000001001011 : Blocks := (Blocks.join ep000000001001011_0 ep000000001001011_1)
private theorem idp000000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100101.list =
    C ((2:ℤ)^148) * horner X vp000000001001011.list + horner X ep000000001001011.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001011 : Branch 1 (-18261639/500000 : ℚ) vp00000000100101 := by
  apply branch_checked idp000000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-18261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-18511639/250000 : ℚ) by norm_num]
  exact coverp000000001001011
theorem coverp00000000100101 : Covers (-18261639/500000 : ℚ) vp00000000100101 := join_branches bp000000001001010 bp000000001001011
private noncomputable def vp0000000010010011111_0 : Blocks := edgeBlocks% "full/vectors/0000000010010011111-V-0000.bin"
noncomputable def vp0000000010010011111 : Blocks := vp0000000010010011111_0
theorem coverp0000000010010011111 : Covers (-18246014/15625 : ℚ) vp0000000010010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010011110_0 : Blocks := edgeBlocks% "full/vectors/0000000010010011110-V-0000.bin"
noncomputable def vp0000000010010011110 : Blocks := vp0000000010010011110_0
theorem coverp0000000010010011110 : Covers (-18230389/15625 : ℚ) vp0000000010010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001001111_0 : Blocks := edgeBlocks% "full/vectors/000000001001001111-V-0000.bin"
noncomputable def vp000000001001001111 : Blocks := vp000000001001001111_0
private theorem bp0000000010010011110 : Branch 0 (-18230389/31250 : ℚ) vp000000001001001111 := by
  apply branch_left_normalized (c:=vp0000000010010011110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-18230389/31250 : ℚ) - ((0:ℤ):ℚ) = (-18230389/15625 : ℚ) by norm_num]
  exact coverp0000000010010011110
private noncomputable def ep0000000010010011111_0 : Blocks := edgeBlocks% "full/vectors/0000000010010011111-E-0000.bin"
noncomputable def ep0000000010010011111 : Blocks := ep0000000010010011111_0
private theorem idp0000000010010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001001111.list =
    C ((2:ℤ)^22) * horner X vp0000000010010011111.list + horner X ep0000000010010011111.list := by
  exact edge_identity (B := (2:ℤ)^134) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010011111 : Branch 1 (-18230389/31250 : ℚ) vp000000001001001111 := by
  apply branch_checked idp0000000010010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-18230389/31250 : ℚ) - ((1:ℤ):ℚ) = (-18246014/15625 : ℚ) by norm_num]
  exact coverp0000000010010011111
theorem coverp000000001001001111 : Covers (-18230389/31250 : ℚ) vp000000001001001111 := join_branches bp0000000010010011110 bp0000000010010011111
private noncomputable def vp000000001001001110_0 : Blocks := edgeBlocks% "full/vectors/000000001001001110-V-0000.bin"
noncomputable def vp000000001001001110 : Blocks := vp000000001001001110_0
theorem coverp000000001001001110 : Covers (-18199139/31250 : ℚ) vp000000001001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100100111_0 : Blocks := edgeBlocks% "full/vectors/00000000100100111-V-0000.bin"
noncomputable def vp00000000100100111 : Blocks := vp00000000100100111_0
private theorem bp000000001001001110 : Branch 0 (-18199139/62500 : ℚ) vp00000000100100111 := by
  apply branch_left_normalized (c:=vp000000001001001110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-18199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-18199139/31250 : ℚ) by norm_num]
  exact coverp000000001001001110
private noncomputable def ep000000001001001111_0 : Blocks := edgeBlocks% "full/vectors/000000001001001111-E-0000.bin"
noncomputable def ep000000001001001111 : Blocks := ep000000001001001111_0
private theorem idp000000001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100100111.list =
    C ((2:ℤ)^33) * horner X vp000000001001001111.list + horner X ep000000001001001111.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001001111 : Branch 1 (-18199139/62500 : ℚ) vp00000000100100111 := by
  apply branch_checked idp000000001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-18199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-18230389/31250 : ℚ) by norm_num]
  exact coverp000000001001001111
theorem coverp00000000100100111 : Covers (-18199139/62500 : ℚ) vp00000000100100111 := join_branches bp000000001001001110 bp000000001001001111
private noncomputable def vp00000000100100110_0 : Blocks := edgeBlocks% "full/vectors/00000000100100110-V-0000.bin"
noncomputable def vp00000000100100110 : Blocks := vp00000000100100110_0
theorem coverp00000000100100110 : Covers (-18136639/62500 : ℚ) vp00000000100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010011_0 : Blocks := edgeBlocks% "full/vectors/0000000010010011-V-0000.bin"
noncomputable def vp0000000010010011 : Blocks := vp0000000010010011_0
private theorem bp00000000100100110 : Branch 0 (-18136639/125000 : ℚ) vp0000000010010011 := by
  apply branch_left_normalized (c:=vp00000000100100110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-18136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-18136639/62500 : ℚ) by norm_num]
  exact coverp00000000100100110
private noncomputable def ep00000000100100111_0 : Blocks := edgeBlocks% "full/vectors/00000000100100111-E-0000.bin"
noncomputable def ep00000000100100111 : Blocks := ep00000000100100111_0
private theorem idp00000000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010011.list =
    C ((2:ℤ)^54) * horner X vp00000000100100111.list + horner X ep00000000100100111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100100111 : Branch 1 (-18136639/125000 : ℚ) vp0000000010010011 := by
  apply branch_checked idp00000000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-18136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-18199139/62500 : ℚ) by norm_num]
  exact coverp00000000100100111
theorem coverp0000000010010011 : Covers (-18136639/125000 : ℚ) vp0000000010010011 := join_branches bp00000000100100110 bp00000000100100111
private noncomputable def vp000000001001001011_0 : Blocks := edgeBlocks% "full/vectors/000000001001001011-V-0000.bin"
noncomputable def vp000000001001001011 : Blocks := vp000000001001001011_0
theorem coverp000000001001001011 : Covers (-18105389/31250 : ℚ) vp000000001001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001001010_0 : Blocks := edgeBlocks% "full/vectors/000000001001001010-V-0000.bin"
noncomputable def vp000000001001001010 : Blocks := vp000000001001001010_0
theorem coverp000000001001001010 : Covers (-18074139/31250 : ℚ) vp000000001001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100100101_0 : Blocks := edgeBlocks% "full/vectors/00000000100100101-V-0000.bin"
noncomputable def vp00000000100100101 : Blocks := vp00000000100100101_0
private theorem bp000000001001001010 : Branch 0 (-18074139/62500 : ℚ) vp00000000100100101 := by
  apply branch_left_normalized (c:=vp000000001001001010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-18074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-18074139/31250 : ℚ) by norm_num]
  exact coverp000000001001001010
private noncomputable def ep000000001001001011_0 : Blocks := edgeBlocks% "full/vectors/000000001001001011-E-0000.bin"
noncomputable def ep000000001001001011 : Blocks := ep000000001001001011_0
private theorem idp000000001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100100101.list =
    C ((2:ℤ)^34) * horner X vp000000001001001011.list + horner X ep000000001001001011.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001001011 : Branch 1 (-18074139/62500 : ℚ) vp00000000100100101 := by
  apply branch_checked idp000000001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-18074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-18105389/31250 : ℚ) by norm_num]
  exact coverp000000001001001011
theorem coverp00000000100100101 : Covers (-18074139/62500 : ℚ) vp00000000100100101 := join_branches bp000000001001001010 bp000000001001001011
private noncomputable def vp00000000100100100_0 : Blocks := edgeBlocks% "full/vectors/00000000100100100-V-0000.bin"
noncomputable def vp00000000100100100 : Blocks := vp00000000100100100_0
theorem coverp00000000100100100 : Covers (-18011639/62500 : ℚ) vp00000000100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010010_0 : Blocks := edgeBlocks% "full/vectors/0000000010010010-V-0000.bin"
noncomputable def vp0000000010010010 : Blocks := vp0000000010010010_0
private theorem bp00000000100100100 : Branch 0 (-18011639/125000 : ℚ) vp0000000010010010 := by
  apply branch_left_normalized (c:=vp00000000100100100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-18011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-18011639/62500 : ℚ) by norm_num]
  exact coverp00000000100100100
private noncomputable def ep00000000100100101_0 : Blocks := edgeBlocks% "full/vectors/00000000100100101-E-0000.bin"
noncomputable def ep00000000100100101 : Blocks := ep00000000100100101_0
private theorem idp00000000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010010.list =
    C ((2:ℤ)^50) * horner X vp00000000100100101.list + horner X ep00000000100100101.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100100101 : Branch 1 (-18011639/125000 : ℚ) vp0000000010010010 := by
  apply branch_checked idp00000000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-18011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-18074139/62500 : ℚ) by norm_num]
  exact coverp00000000100100101
theorem coverp0000000010010010 : Covers (-18011639/125000 : ℚ) vp0000000010010010 := join_branches bp00000000100100100 bp00000000100100101
private noncomputable def vp000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000001001001-V-0000.bin"
noncomputable def vp000000001001001 : Blocks := vp000000001001001_0
private theorem bp0000000010010010 : Branch 0 (-18011639/250000 : ℚ) vp000000001001001 := by
  apply branch_left_normalized (c:=vp0000000010010010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-18011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-18011639/125000 : ℚ) by norm_num]
  exact coverp0000000010010010
private noncomputable def ep0000000010010011_0 : Blocks := edgeBlocks% "full/vectors/0000000010010011-E-0000.bin"
noncomputable def ep0000000010010011 : Blocks := ep0000000010010011_0
private theorem idp0000000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001001.list =
    C ((2:ℤ)^81) * horner X vp0000000010010011.list + horner X ep0000000010010011.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010011 : Branch 1 (-18011639/250000 : ℚ) vp000000001001001 := by
  apply branch_checked idp0000000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-18011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-18136639/125000 : ℚ) by norm_num]
  exact coverp0000000010010011
theorem coverp000000001001001 : Covers (-18011639/250000 : ℚ) vp000000001001001 := join_branches bp0000000010010010 bp0000000010010011
private noncomputable def vp00000000100100011_0 : Blocks := edgeBlocks% "full/vectors/00000000100100011-V-0000.bin"
noncomputable def vp00000000100100011 : Blocks := vp00000000100100011_0
theorem coverp00000000100100011 : Covers (-17949139/62500 : ℚ) vp00000000100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100100010_0 : Blocks := edgeBlocks% "full/vectors/00000000100100010-V-0000.bin"
noncomputable def vp00000000100100010 : Blocks := vp00000000100100010_0
theorem coverp00000000100100010 : Covers (-17886639/62500 : ℚ) vp00000000100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000000010010001-V-0000.bin"
noncomputable def vp0000000010010001 : Blocks := vp0000000010010001_0
private theorem bp00000000100100010 : Branch 0 (-17886639/125000 : ℚ) vp0000000010010001 := by
  apply branch_left_normalized (c:=vp00000000100100010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-17886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17886639/62500 : ℚ) by norm_num]
  exact coverp00000000100100010
private noncomputable def ep00000000100100011_0 : Blocks := edgeBlocks% "full/vectors/00000000100100011-E-0000.bin"
noncomputable def ep00000000100100011 : Blocks := ep00000000100100011_0
private theorem idp00000000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010001.list =
    C ((2:ℤ)^50) * horner X vp00000000100100011.list + horner X ep00000000100100011.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100100011 : Branch 1 (-17886639/125000 : ℚ) vp0000000010010001 := by
  apply branch_checked idp00000000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-17886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17949139/62500 : ℚ) by norm_num]
  exact coverp00000000100100011
theorem coverp0000000010010001 : Covers (-17886639/125000 : ℚ) vp0000000010010001 := join_branches bp00000000100100010 bp00000000100100011
private noncomputable def vp000000001001000011_0 : Blocks := edgeBlocks% "full/vectors/000000001001000011-V-0000.bin"
noncomputable def vp000000001001000011 : Blocks := vp000000001001000011_0
theorem coverp000000001001000011 : Covers (-17855389/31250 : ℚ) vp000000001001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001000010_0 : Blocks := edgeBlocks% "full/vectors/000000001001000010-V-0000.bin"
noncomputable def vp000000001001000010 : Blocks := vp000000001001000010_0
theorem coverp000000001001000010 : Covers (-17824139/31250 : ℚ) vp000000001001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000000100100001-V-0000.bin"
noncomputable def vp00000000100100001 : Blocks := vp00000000100100001_0
private theorem bp000000001001000010 : Branch 0 (-17824139/62500 : ℚ) vp00000000100100001 := by
  apply branch_left_normalized (c:=vp000000001001000010) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-17824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-17824139/31250 : ℚ) by norm_num]
  exact coverp000000001001000010
private noncomputable def ep000000001001000011_0 : Blocks := edgeBlocks% "full/vectors/000000001001000011-E-0000.bin"
noncomputable def ep000000001001000011 : Blocks := ep000000001001000011_0
private theorem idp000000001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100100001.list =
    C ((2:ℤ)^33) * horner X vp000000001001000011.list + horner X ep000000001001000011.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001000011 : Branch 1 (-17824139/62500 : ℚ) vp00000000100100001 := by
  apply branch_checked idp000000001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-17824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-17855389/31250 : ℚ) by norm_num]
  exact coverp000000001001000011
theorem coverp00000000100100001 : Covers (-17824139/62500 : ℚ) vp00000000100100001 := join_branches bp000000001001000010 bp000000001001000011
private noncomputable def vp000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000000001001000001-V-0000.bin"
noncomputable def vp000000001001000001 : Blocks := vp000000001001000001_0
theorem coverp000000001001000001 : Covers (-17792889/31250 : ℚ) vp000000001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001001000000_0 : Blocks := edgeBlocks% "full/vectors/000000001001000000-V-0000.bin"
noncomputable def vp000000001001000000 : Blocks := vp000000001001000000_0
theorem coverp000000001001000000 : Covers (-17761639/31250 : ℚ) vp000000001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100100000_0 : Blocks := edgeBlocks% "full/vectors/00000000100100000-V-0000.bin"
noncomputable def vp00000000100100000 : Blocks := vp00000000100100000_0
private theorem bp000000001001000000 : Branch 0 (-17761639/62500 : ℚ) vp00000000100100000 := by
  apply branch_left_normalized (c:=vp000000001001000000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-17761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-17761639/31250 : ℚ) by norm_num]
  exact coverp000000001001000000
private noncomputable def ep000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000000001001000001-E-0000.bin"
noncomputable def ep000000001001000001 : Blocks := ep000000001001000001_0
private theorem idp000000001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100100000.list =
    C ((2:ℤ)^32) * horner X vp000000001001000001.list + horner X ep000000001001000001.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001000001 : Branch 1 (-17761639/62500 : ℚ) vp00000000100100000 := by
  apply branch_checked idp000000001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-17792889/31250 : ℚ) by norm_num]
  exact coverp000000001001000001
theorem coverp00000000100100000 : Covers (-17761639/62500 : ℚ) vp00000000100100000 := join_branches bp000000001001000000 bp000000001001000001
private noncomputable def vp0000000010010000_0 : Blocks := edgeBlocks% "full/vectors/0000000010010000-V-0000.bin"
noncomputable def vp0000000010010000 : Blocks := vp0000000010010000_0
private theorem bp00000000100100000 : Branch 0 (-17761639/125000 : ℚ) vp0000000010010000 := by
  apply branch_left_normalized (c:=vp00000000100100000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-17761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17761639/62500 : ℚ) by norm_num]
  exact coverp00000000100100000
private noncomputable def ep00000000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000000100100001-E-0000.bin"
noncomputable def ep00000000100100001 : Blocks := ep00000000100100001_0
private theorem idp00000000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010000.list =
    C ((2:ℤ)^49) * horner X vp00000000100100001.list + horner X ep00000000100100001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100100001 : Branch 1 (-17761639/125000 : ℚ) vp0000000010010000 := by
  apply branch_checked idp00000000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17824139/62500 : ℚ) by norm_num]
  exact coverp00000000100100001
theorem coverp0000000010010000 : Covers (-17761639/125000 : ℚ) vp0000000010010000 := join_branches bp00000000100100000 bp00000000100100001
private noncomputable def vp000000001001000_0 : Blocks := edgeBlocks% "full/vectors/000000001001000-V-0000.bin"
noncomputable def vp000000001001000 : Blocks := vp000000001001000_0
private theorem bp0000000010010000 : Branch 0 (-17761639/250000 : ℚ) vp000000001001000 := by
  apply branch_left_normalized (c:=vp0000000010010000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-17761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-17761639/125000 : ℚ) by norm_num]
  exact coverp0000000010010000
private noncomputable def ep0000000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000000010010001-E-0000.bin"
noncomputable def ep0000000010010001 : Blocks := ep0000000010010001_0
private theorem idp0000000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001000.list =
    C ((2:ℤ)^80) * horner X vp0000000010010001.list + horner X ep0000000010010001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010010001 : Branch 1 (-17761639/250000 : ℚ) vp000000001001000 := by
  apply branch_checked idp0000000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-17886639/125000 : ℚ) by norm_num]
  exact coverp0000000010010001
theorem coverp000000001001000 : Covers (-17761639/250000 : ℚ) vp000000001001000 := join_branches bp0000000010010000 bp0000000010010001
private noncomputable def vp00000000100100_0 : Blocks := edgeBlocks% "full/vectors/00000000100100-V-0000.bin"
private noncomputable def vp00000000100100_1 : Blocks := edgeBlocks% "full/vectors/00000000100100-V-0001.bin"
noncomputable def vp00000000100100 : Blocks := (Blocks.join vp00000000100100_0 vp00000000100100_1)
private theorem bp000000001001000 : Branch 0 (-17761639/500000 : ℚ) vp00000000100100 := by
  apply branch_left_normalized (c:=vp000000001001000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-17761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-17761639/250000 : ℚ) by norm_num]
  exact coverp000000001001000
private noncomputable def ep000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000001001001-E-0000.bin"
private noncomputable def ep000000001001001_1 : Blocks := edgeBlocks% "full/vectors/000000001001001-E-0001.bin"
noncomputable def ep000000001001001 : Blocks := (Blocks.join ep000000001001001_0 ep000000001001001_1)
private theorem idp000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100100.list =
    C ((2:ℤ)^139) * horner X vp000000001001001.list + horner X ep000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001001 : Branch 1 (-17761639/500000 : ℚ) vp00000000100100 := by
  apply branch_checked idp000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-18011639/250000 : ℚ) by norm_num]
  exact coverp000000001001001
theorem coverp00000000100100 : Covers (-17761639/500000 : ℚ) vp00000000100100 := join_branches bp000000001001000 bp000000001001001
private noncomputable def vp0000000010010_0 : Blocks := edgeBlocks% "full/vectors/0000000010010-V-0000.bin"
private noncomputable def vp0000000010010_1 : Blocks := edgeBlocks% "full/vectors/0000000010010-V-0001.bin"
noncomputable def vp0000000010010 : Blocks := (Blocks.join vp0000000010010_0 vp0000000010010_1)
private theorem bp00000000100100 : Branch 0 (-17761639/1000000 : ℚ) vp0000000010010 := by
  apply branch_left_normalized (c:=vp00000000100100) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-17761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-17761639/500000 : ℚ) by norm_num]
  exact coverp00000000100100
private noncomputable def ep00000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000100101-E-0000.bin"
private noncomputable def ep00000000100101_1 : Blocks := edgeBlocks% "full/vectors/00000000100101-E-0001.bin"
noncomputable def ep00000000100101 : Blocks := (Blocks.join ep00000000100101_0 ep00000000100101_1)
private theorem idp00000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010010.list =
    C ((2:ℤ)^257) * horner X vp00000000100101.list + horner X ep00000000100101.list := by
  exact edge_identity (B := (2:ℤ)^480) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100101 : Branch 1 (-17761639/1000000 : ℚ) vp0000000010010 := by
  apply branch_checked idp00000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-18261639/500000 : ℚ) by norm_num]
  exact coverp00000000100101
theorem coverp0000000010010 : Covers (-17761639/1000000 : ℚ) vp0000000010010 := join_branches bp00000000100100 bp00000000100101
private noncomputable def vp000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000001001-V-0000.bin"
private noncomputable def vp000000001001_1 : Blocks := edgeBlocks% "full/vectors/000000001001-V-0001.bin"
private noncomputable def vp000000001001_2 : Blocks := edgeBlocks% "full/vectors/000000001001-V-0002.bin"
private noncomputable def vp000000001001_3 : Blocks := edgeBlocks% "full/vectors/000000001001-V-0003.bin"
noncomputable def vp000000001001 : Blocks := (Blocks.join (Blocks.join vp000000001001_0 vp000000001001_1) (Blocks.join vp000000001001_2 vp000000001001_3))
private theorem bp0000000010010 : Branch 0 (-17761639/2000000 : ℚ) vp000000001001 := by
  apply branch_left_normalized (c:=vp0000000010010) (k:=0) (m:=254) (by decide +kernel)
  rw [show 2*(-17761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-17761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010010
private noncomputable def ep0000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000010011-E-0000.bin"
private noncomputable def ep0000000010011_1 : Blocks := edgeBlocks% "full/vectors/0000000010011-E-0001.bin"
private noncomputable def ep0000000010011_2 : Blocks := edgeBlocks% "full/vectors/0000000010011-E-0002.bin"
private noncomputable def ep0000000010011_3 : Blocks := edgeBlocks% "full/vectors/0000000010011-E-0003.bin"
noncomputable def ep0000000010011 : Blocks := (Blocks.join (Blocks.join ep0000000010011_0 ep0000000010011_1) (Blocks.join ep0000000010011_2 ep0000000010011_3))
private theorem idp0000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001001.list =
    C ((2:ℤ)^499) * horner X vp0000000010011.list + horner X ep0000000010011.list := by
  exact edge_identity (B := (2:ℤ)^832) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010011 : Branch 1 (-17761639/2000000 : ℚ) vp000000001001 := by
  apply branch_checked idp0000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-17761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-18761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010011
theorem coverp000000001001 : Covers (-17761639/2000000 : ℚ) vp000000001001 := join_branches bp0000000010010 bp0000000010011
private noncomputable def vp00000000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000100011111-V-0000.bin"
noncomputable def vp00000000100011111 : Blocks := vp00000000100011111_0
theorem coverp00000000100011111 : Covers (-17699139/62500 : ℚ) vp00000000100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000111101_0 : Blocks := edgeBlocks% "full/vectors/000000001000111101-V-0000.bin"
noncomputable def vp000000001000111101 : Blocks := vp000000001000111101_0
theorem coverp000000001000111101 : Covers (-17667889/31250 : ℚ) vp000000001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000111100_0 : Blocks := edgeBlocks% "full/vectors/000000001000111100-V-0000.bin"
noncomputable def vp000000001000111100 : Blocks := vp000000001000111100_0
theorem coverp000000001000111100 : Covers (-17636639/31250 : ℚ) vp000000001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011110_0 : Blocks := edgeBlocks% "full/vectors/00000000100011110-V-0000.bin"
noncomputable def vp00000000100011110 : Blocks := vp00000000100011110_0
private theorem bp000000001000111100 : Branch 0 (-17636639/62500 : ℚ) vp00000000100011110 := by
  apply branch_left_normalized (c:=vp000000001000111100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-17636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-17636639/31250 : ℚ) by norm_num]
  exact coverp000000001000111100
private noncomputable def ep000000001000111101_0 : Blocks := edgeBlocks% "full/vectors/000000001000111101-E-0000.bin"
noncomputable def ep000000001000111101 : Blocks := ep000000001000111101_0
private theorem idp000000001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100011110.list =
    C ((2:ℤ)^33) * horner X vp000000001000111101.list + horner X ep000000001000111101.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000111101 : Branch 1 (-17636639/62500 : ℚ) vp00000000100011110 := by
  apply branch_checked idp000000001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-17636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-17667889/31250 : ℚ) by norm_num]
  exact coverp000000001000111101
theorem coverp00000000100011110 : Covers (-17636639/62500 : ℚ) vp00000000100011110 := join_branches bp000000001000111100 bp000000001000111101
private noncomputable def vp0000000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000000010001111-V-0000.bin"
noncomputable def vp0000000010001111 : Blocks := vp0000000010001111_0
private theorem bp00000000100011110 : Branch 0 (-17636639/125000 : ℚ) vp0000000010001111 := by
  apply branch_left_normalized (c:=vp00000000100011110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-17636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17636639/62500 : ℚ) by norm_num]
  exact coverp00000000100011110
private noncomputable def ep00000000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000100011111-E-0000.bin"
noncomputable def ep00000000100011111 : Blocks := ep00000000100011111_0
private theorem idp00000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001111.list =
    C ((2:ℤ)^49) * horner X vp00000000100011111.list + horner X ep00000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011111 : Branch 1 (-17636639/125000 : ℚ) vp0000000010001111 := by
  apply branch_checked idp00000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-17636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17699139/62500 : ℚ) by norm_num]
  exact coverp00000000100011111
theorem coverp0000000010001111 : Covers (-17636639/125000 : ℚ) vp0000000010001111 := join_branches bp00000000100011110 bp00000000100011111
private noncomputable def vp00000000100011101_0 : Blocks := edgeBlocks% "full/vectors/00000000100011101-V-0000.bin"
noncomputable def vp00000000100011101 : Blocks := vp00000000100011101_0
theorem coverp00000000100011101 : Covers (-17574139/62500 : ℚ) vp00000000100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011100_0 : Blocks := edgeBlocks% "full/vectors/00000000100011100-V-0000.bin"
noncomputable def vp00000000100011100 : Blocks := vp00000000100011100_0
theorem coverp00000000100011100 : Covers (-17511639/62500 : ℚ) vp00000000100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001110_0 : Blocks := edgeBlocks% "full/vectors/0000000010001110-V-0000.bin"
noncomputable def vp0000000010001110 : Blocks := vp0000000010001110_0
private theorem bp00000000100011100 : Branch 0 (-17511639/125000 : ℚ) vp0000000010001110 := by
  apply branch_left_normalized (c:=vp00000000100011100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-17511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17511639/62500 : ℚ) by norm_num]
  exact coverp00000000100011100
private noncomputable def ep00000000100011101_0 : Blocks := edgeBlocks% "full/vectors/00000000100011101-E-0000.bin"
noncomputable def ep00000000100011101 : Blocks := ep00000000100011101_0
private theorem idp00000000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001110.list =
    C ((2:ℤ)^50) * horner X vp00000000100011101.list + horner X ep00000000100011101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011101 : Branch 1 (-17511639/125000 : ℚ) vp0000000010001110 := by
  apply branch_checked idp00000000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-17511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17574139/62500 : ℚ) by norm_num]
  exact coverp00000000100011101
theorem coverp0000000010001110 : Covers (-17511639/125000 : ℚ) vp0000000010001110 := join_branches bp00000000100011100 bp00000000100011101
private noncomputable def vp000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000001000111-V-0000.bin"
noncomputable def vp000000001000111 : Blocks := vp000000001000111_0
private theorem bp0000000010001110 : Branch 0 (-17511639/250000 : ℚ) vp000000001000111 := by
  apply branch_left_normalized (c:=vp0000000010001110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-17511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-17511639/125000 : ℚ) by norm_num]
  exact coverp0000000010001110
private noncomputable def ep0000000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000000010001111-E-0000.bin"
noncomputable def ep0000000010001111 : Blocks := ep0000000010001111_0
private theorem idp0000000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000111.list =
    C ((2:ℤ)^82) * horner X vp0000000010001111.list + horner X ep0000000010001111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001111 : Branch 1 (-17511639/250000 : ℚ) vp000000001000111 := by
  apply branch_checked idp0000000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-17511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-17636639/125000 : ℚ) by norm_num]
  exact coverp0000000010001111
theorem coverp000000001000111 : Covers (-17511639/250000 : ℚ) vp000000001000111 := join_branches bp0000000010001110 bp0000000010001111
private noncomputable def vp000000001000110111_0 : Blocks := edgeBlocks% "full/vectors/000000001000110111-V-0000.bin"
noncomputable def vp000000001000110111 : Blocks := vp000000001000110111_0
theorem coverp000000001000110111 : Covers (-17480389/31250 : ℚ) vp000000001000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000110110_0 : Blocks := edgeBlocks% "full/vectors/000000001000110110-V-0000.bin"
noncomputable def vp000000001000110110 : Blocks := vp000000001000110110_0
theorem coverp000000001000110110 : Covers (-17449139/31250 : ℚ) vp000000001000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011011-V-0000.bin"
noncomputable def vp00000000100011011 : Blocks := vp00000000100011011_0
private theorem bp000000001000110110 : Branch 0 (-17449139/62500 : ℚ) vp00000000100011011 := by
  apply branch_left_normalized (c:=vp000000001000110110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-17449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-17449139/31250 : ℚ) by norm_num]
  exact coverp000000001000110110
private noncomputable def ep000000001000110111_0 : Blocks := edgeBlocks% "full/vectors/000000001000110111-E-0000.bin"
noncomputable def ep000000001000110111 : Blocks := ep000000001000110111_0
private theorem idp000000001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100011011.list =
    C ((2:ℤ)^33) * horner X vp000000001000110111.list + horner X ep000000001000110111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000110111 : Branch 1 (-17449139/62500 : ℚ) vp00000000100011011 := by
  apply branch_checked idp000000001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-17449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-17480389/31250 : ℚ) by norm_num]
  exact coverp000000001000110111
theorem coverp00000000100011011 : Covers (-17449139/62500 : ℚ) vp00000000100011011 := join_branches bp000000001000110110 bp000000001000110111
private noncomputable def vp0000000010001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101011-V-0000.bin"
noncomputable def vp0000000010001101011 : Blocks := vp0000000010001101011_0
theorem coverp0000000010001101011 : Covers (-17433514/15625 : ℚ) vp0000000010001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011010101_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010101-V-0000.bin"
noncomputable def vp00000000100011010101 : Blocks := vp00000000100011010101_0
theorem coverp00000000100011010101 : Covers (-34851403/15625 : ℚ) vp00000000100011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011010100_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010100-V-0000.bin"
noncomputable def vp00000000100011010100 : Blocks := vp00000000100011010100_0
theorem coverp00000000100011010100 : Covers (-34835778/15625 : ℚ) vp00000000100011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001101010_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101010-V-0000.bin"
noncomputable def vp0000000010001101010 : Blocks := vp0000000010001101010_0
private theorem bp00000000100011010100 : Branch 0 (-17417889/15625 : ℚ) vp0000000010001101010 := by
  apply branch_left_normalized (c:=vp00000000100011010100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-17417889/15625 : ℚ) - ((0:ℤ):ℚ) = (-34835778/15625 : ℚ) by norm_num]
  exact coverp00000000100011010100
private noncomputable def ep00000000100011010101_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010101-E-0000.bin"
noncomputable def ep00000000100011010101 : Blocks := ep00000000100011010101_0
private theorem idp00000000100011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001101010.list =
    C ((2:ℤ)^18) * horner X vp00000000100011010101.list + horner X ep00000000100011010101.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011010101 : Branch 1 (-17417889/15625 : ℚ) vp0000000010001101010 := by
  apply branch_checked idp00000000100011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-17417889/15625 : ℚ) - ((1:ℤ):ℚ) = (-34851403/15625 : ℚ) by norm_num]
  exact coverp00000000100011010101
theorem coverp0000000010001101010 : Covers (-17417889/15625 : ℚ) vp0000000010001101010 := join_branches bp00000000100011010100 bp00000000100011010101
private noncomputable def vp000000001000110101_0 : Blocks := edgeBlocks% "full/vectors/000000001000110101-V-0000.bin"
noncomputable def vp000000001000110101 : Blocks := vp000000001000110101_0
private theorem bp0000000010001101010 : Branch 0 (-17417889/31250 : ℚ) vp000000001000110101 := by
  apply branch_left_normalized (c:=vp0000000010001101010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-17417889/31250 : ℚ) - ((0:ℤ):ℚ) = (-17417889/15625 : ℚ) by norm_num]
  exact coverp0000000010001101010
private noncomputable def ep0000000010001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101011-E-0000.bin"
noncomputable def ep0000000010001101011 : Blocks := ep0000000010001101011_0
private theorem idp0000000010001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000110101.list =
    C ((2:ℤ)^24) * horner X vp0000000010001101011.list + horner X ep0000000010001101011.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001101011 : Branch 1 (-17417889/31250 : ℚ) vp000000001000110101 := by
  apply branch_checked idp0000000010001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-17417889/31250 : ℚ) - ((1:ℤ):ℚ) = (-17433514/15625 : ℚ) by norm_num]
  exact coverp0000000010001101011
theorem coverp000000001000110101 : Covers (-17417889/31250 : ℚ) vp000000001000110101 := join_branches bp0000000010001101010 bp0000000010001101011
private noncomputable def vp00000000100011010011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010011-V-0000.bin"
noncomputable def vp00000000100011010011 : Blocks := vp00000000100011010011_0
theorem coverp00000000100011010011 : Covers (-34820153/15625 : ℚ) vp00000000100011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011010010_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010010-V-0000.bin"
noncomputable def vp00000000100011010010 : Blocks := vp00000000100011010010_0
theorem coverp00000000100011010010 : Covers (-34804528/15625 : ℚ) vp00000000100011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101001-V-0000.bin"
noncomputable def vp0000000010001101001 : Blocks := vp0000000010001101001_0
private theorem bp00000000100011010010 : Branch 0 (-17402264/15625 : ℚ) vp0000000010001101001 := by
  apply branch_left_normalized (c:=vp00000000100011010010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-17402264/15625 : ℚ) - ((0:ℤ):ℚ) = (-34804528/15625 : ℚ) by norm_num]
  exact coverp00000000100011010010
private noncomputable def ep00000000100011010011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010011-E-0000.bin"
noncomputable def ep00000000100011010011 : Blocks := ep00000000100011010011_0
private theorem idp00000000100011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001101001.list =
    C ((2:ℤ)^17) * horner X vp00000000100011010011.list + horner X ep00000000100011010011.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011010011 : Branch 1 (-17402264/15625 : ℚ) vp0000000010001101001 := by
  apply branch_checked idp00000000100011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-17402264/15625 : ℚ) - ((1:ℤ):ℚ) = (-34820153/15625 : ℚ) by norm_num]
  exact coverp00000000100011010011
theorem coverp0000000010001101001 : Covers (-17402264/15625 : ℚ) vp0000000010001101001 := join_branches bp00000000100011010010 bp00000000100011010011
private noncomputable def vp0000000010001101000_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101000-V-0000.bin"
noncomputable def vp0000000010001101000 : Blocks := vp0000000010001101000_0
theorem coverp0000000010001101000 : Covers (-17386639/15625 : ℚ) vp0000000010001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000110100_0 : Blocks := edgeBlocks% "full/vectors/000000001000110100-V-0000.bin"
noncomputable def vp000000001000110100 : Blocks := vp000000001000110100_0
private theorem bp0000000010001101000 : Branch 0 (-17386639/31250 : ℚ) vp000000001000110100 := by
  apply branch_left_normalized (c:=vp0000000010001101000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-17386639/31250 : ℚ) - ((0:ℤ):ℚ) = (-17386639/15625 : ℚ) by norm_num]
  exact coverp0000000010001101000
private noncomputable def ep0000000010001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101001-E-0000.bin"
noncomputable def ep0000000010001101001 : Blocks := ep0000000010001101001_0
private theorem idp0000000010001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000110100.list =
    C ((2:ℤ)^22) * horner X vp0000000010001101001.list + horner X ep0000000010001101001.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001101001 : Branch 1 (-17386639/31250 : ℚ) vp000000001000110100 := by
  apply branch_checked idp0000000010001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-17386639/31250 : ℚ) - ((1:ℤ):ℚ) = (-17402264/15625 : ℚ) by norm_num]
  exact coverp0000000010001101001
theorem coverp000000001000110100 : Covers (-17386639/31250 : ℚ) vp000000001000110100 := join_branches bp0000000010001101000 bp0000000010001101001
private noncomputable def vp00000000100011010_0 : Blocks := edgeBlocks% "full/vectors/00000000100011010-V-0000.bin"
noncomputable def vp00000000100011010 : Blocks := vp00000000100011010_0
private theorem bp000000001000110100 : Branch 0 (-17386639/62500 : ℚ) vp00000000100011010 := by
  apply branch_left_normalized (c:=vp000000001000110100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-17386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-17386639/31250 : ℚ) by norm_num]
  exact coverp000000001000110100
private noncomputable def ep000000001000110101_0 : Blocks := edgeBlocks% "full/vectors/000000001000110101-E-0000.bin"
noncomputable def ep000000001000110101 : Blocks := ep000000001000110101_0
private theorem idp000000001000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100011010.list =
    C ((2:ℤ)^32) * horner X vp000000001000110101.list + horner X ep000000001000110101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000110101 : Branch 1 (-17386639/62500 : ℚ) vp00000000100011010 := by
  apply branch_checked idp000000001000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-17386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-17417889/31250 : ℚ) by norm_num]
  exact coverp000000001000110101
theorem coverp00000000100011010 : Covers (-17386639/62500 : ℚ) vp00000000100011010 := join_branches bp000000001000110100 bp000000001000110101
private noncomputable def vp0000000010001101_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101-V-0000.bin"
noncomputable def vp0000000010001101 : Blocks := vp0000000010001101_0
private theorem bp00000000100011010 : Branch 0 (-17386639/125000 : ℚ) vp0000000010001101 := by
  apply branch_left_normalized (c:=vp00000000100011010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-17386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17386639/62500 : ℚ) by norm_num]
  exact coverp00000000100011010
private noncomputable def ep00000000100011011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011011-E-0000.bin"
noncomputable def ep00000000100011011 : Blocks := ep00000000100011011_0
private theorem idp00000000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001101.list =
    C ((2:ℤ)^49) * horner X vp00000000100011011.list + horner X ep00000000100011011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011011 : Branch 1 (-17386639/125000 : ℚ) vp0000000010001101 := by
  apply branch_checked idp00000000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-17386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17449139/62500 : ℚ) by norm_num]
  exact coverp00000000100011011
theorem coverp0000000010001101 : Covers (-17386639/125000 : ℚ) vp0000000010001101 := join_branches bp00000000100011010 bp00000000100011011
private noncomputable def vp000000001000110011_0 : Blocks := edgeBlocks% "full/vectors/000000001000110011-V-0000.bin"
noncomputable def vp000000001000110011 : Blocks := vp000000001000110011_0
theorem coverp000000001000110011 : Covers (-17355389/31250 : ℚ) vp000000001000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000110010_0 : Blocks := edgeBlocks% "full/vectors/000000001000110010-V-0000.bin"
noncomputable def vp000000001000110010 : Blocks := vp000000001000110010_0
theorem coverp000000001000110010 : Covers (-17324139/31250 : ℚ) vp000000001000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100011001_0 : Blocks := edgeBlocks% "full/vectors/00000000100011001-V-0000.bin"
noncomputable def vp00000000100011001 : Blocks := vp00000000100011001_0
private theorem bp000000001000110010 : Branch 0 (-17324139/62500 : ℚ) vp00000000100011001 := by
  apply branch_left_normalized (c:=vp000000001000110010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-17324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-17324139/31250 : ℚ) by norm_num]
  exact coverp000000001000110010
private noncomputable def ep000000001000110011_0 : Blocks := edgeBlocks% "full/vectors/000000001000110011-E-0000.bin"
noncomputable def ep000000001000110011 : Blocks := ep000000001000110011_0
private theorem idp000000001000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100011001.list =
    C ((2:ℤ)^31) * horner X vp000000001000110011.list + horner X ep000000001000110011.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000110011 : Branch 1 (-17324139/62500 : ℚ) vp00000000100011001 := by
  apply branch_checked idp000000001000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-17324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-17355389/31250 : ℚ) by norm_num]
  exact coverp000000001000110011
theorem coverp00000000100011001 : Covers (-17324139/62500 : ℚ) vp00000000100011001 := join_branches bp000000001000110010 bp000000001000110011
private noncomputable def vp00000000100011000_0 : Blocks := edgeBlocks% "full/vectors/00000000100011000-V-0000.bin"
noncomputable def vp00000000100011000 : Blocks := vp00000000100011000_0
theorem coverp00000000100011000 : Covers (-17261639/62500 : ℚ) vp00000000100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001100_0 : Blocks := edgeBlocks% "full/vectors/0000000010001100-V-0000.bin"
noncomputable def vp0000000010001100 : Blocks := vp0000000010001100_0
private theorem bp00000000100011000 : Branch 0 (-17261639/125000 : ℚ) vp0000000010001100 := by
  apply branch_left_normalized (c:=vp00000000100011000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-17261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17261639/62500 : ℚ) by norm_num]
  exact coverp00000000100011000
private noncomputable def ep00000000100011001_0 : Blocks := edgeBlocks% "full/vectors/00000000100011001-E-0000.bin"
noncomputable def ep00000000100011001 : Blocks := ep00000000100011001_0
private theorem idp00000000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001100.list =
    C ((2:ℤ)^47) * horner X vp00000000100011001.list + horner X ep00000000100011001.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011001 : Branch 1 (-17261639/125000 : ℚ) vp0000000010001100 := by
  apply branch_checked idp00000000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-17261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17324139/62500 : ℚ) by norm_num]
  exact coverp00000000100011001
theorem coverp0000000010001100 : Covers (-17261639/125000 : ℚ) vp0000000010001100 := join_branches bp00000000100011000 bp00000000100011001
private noncomputable def vp000000001000110_0 : Blocks := edgeBlocks% "full/vectors/000000001000110-V-0000.bin"
noncomputable def vp000000001000110 : Blocks := vp000000001000110_0
private theorem bp0000000010001100 : Branch 0 (-17261639/250000 : ℚ) vp000000001000110 := by
  apply branch_left_normalized (c:=vp0000000010001100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-17261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-17261639/125000 : ℚ) by norm_num]
  exact coverp0000000010001100
private noncomputable def ep0000000010001101_0 : Blocks := edgeBlocks% "full/vectors/0000000010001101-E-0000.bin"
noncomputable def ep0000000010001101 : Blocks := ep0000000010001101_0
private theorem idp0000000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000110.list =
    C ((2:ℤ)^78) * horner X vp0000000010001101.list + horner X ep0000000010001101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001101 : Branch 1 (-17261639/250000 : ℚ) vp000000001000110 := by
  apply branch_checked idp0000000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-17261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-17386639/125000 : ℚ) by norm_num]
  exact coverp0000000010001101
theorem coverp000000001000110 : Covers (-17261639/250000 : ℚ) vp000000001000110 := join_branches bp0000000010001100 bp0000000010001101
private noncomputable def vp00000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011-V-0000.bin"
private noncomputable def vp00000000100011_1 : Blocks := edgeBlocks% "full/vectors/00000000100011-V-0001.bin"
noncomputable def vp00000000100011 : Blocks := (Blocks.join vp00000000100011_0 vp00000000100011_1)
private theorem bp000000001000110 : Branch 0 (-17261639/500000 : ℚ) vp00000000100011 := by
  apply branch_left_normalized (c:=vp000000001000110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-17261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-17261639/250000 : ℚ) by norm_num]
  exact coverp000000001000110
private noncomputable def ep000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000001000111-E-0000.bin"
private noncomputable def ep000000001000111_1 : Blocks := edgeBlocks% "full/vectors/000000001000111-E-0001.bin"
noncomputable def ep000000001000111 : Blocks := (Blocks.join ep000000001000111_0 ep000000001000111_1)
private theorem idp000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100011.list =
    C ((2:ℤ)^137) * horner X vp000000001000111.list + horner X ep000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000111 : Branch 1 (-17261639/500000 : ℚ) vp00000000100011 := by
  apply branch_checked idp000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-17261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-17511639/250000 : ℚ) by norm_num]
  exact coverp000000001000111
theorem coverp00000000100011 : Covers (-17261639/500000 : ℚ) vp00000000100011 := join_branches bp000000001000110 bp000000001000111
private noncomputable def vp0000000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001011-V-0000.bin"
noncomputable def vp0000000010001011 : Blocks := vp0000000010001011_0
theorem coverp0000000010001011 : Covers (-17136639/125000 : ℚ) vp0000000010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000100010101-V-0000.bin"
noncomputable def vp00000000100010101 : Blocks := vp00000000100010101_0
theorem coverp00000000100010101 : Covers (-17074139/62500 : ℚ) vp00000000100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000000001000101001-V-0000.bin"
noncomputable def vp000000001000101001 : Blocks := vp000000001000101001_0
theorem coverp000000001000101001 : Covers (-17042889/31250 : ℚ) vp000000001000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000101000_0 : Blocks := edgeBlocks% "full/vectors/000000001000101000-V-0000.bin"
noncomputable def vp000000001000101000 : Blocks := vp000000001000101000_0
theorem coverp000000001000101000 : Covers (-17011639/31250 : ℚ) vp000000001000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010100_0 : Blocks := edgeBlocks% "full/vectors/00000000100010100-V-0000.bin"
noncomputable def vp00000000100010100 : Blocks := vp00000000100010100_0
private theorem bp000000001000101000 : Branch 0 (-17011639/62500 : ℚ) vp00000000100010100 := by
  apply branch_left_normalized (c:=vp000000001000101000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-17011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-17011639/31250 : ℚ) by norm_num]
  exact coverp000000001000101000
private noncomputable def ep000000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000000001000101001-E-0000.bin"
noncomputable def ep000000001000101001 : Blocks := ep000000001000101001_0
private theorem idp000000001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010100.list =
    C ((2:ℤ)^33) * horner X vp000000001000101001.list + horner X ep000000001000101001.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000101001 : Branch 1 (-17011639/62500 : ℚ) vp00000000100010100 := by
  apply branch_checked idp000000001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-17011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-17042889/31250 : ℚ) by norm_num]
  exact coverp000000001000101001
theorem coverp00000000100010100 : Covers (-17011639/62500 : ℚ) vp00000000100010100 := join_branches bp000000001000101000 bp000000001000101001
private noncomputable def vp0000000010001010_0 : Blocks := edgeBlocks% "full/vectors/0000000010001010-V-0000.bin"
noncomputable def vp0000000010001010 : Blocks := vp0000000010001010_0
private theorem bp00000000100010100 : Branch 0 (-17011639/125000 : ℚ) vp0000000010001010 := by
  apply branch_left_normalized (c:=vp00000000100010100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-17011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-17011639/62500 : ℚ) by norm_num]
  exact coverp00000000100010100
private noncomputable def ep00000000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000100010101-E-0000.bin"
noncomputable def ep00000000100010101 : Blocks := ep00000000100010101_0
private theorem idp00000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001010.list =
    C ((2:ℤ)^51) * horner X vp00000000100010101.list + horner X ep00000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100010101 : Branch 1 (-17011639/125000 : ℚ) vp0000000010001010 := by
  apply branch_checked idp00000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-17011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-17074139/62500 : ℚ) by norm_num]
  exact coverp00000000100010101
theorem coverp0000000010001010 : Covers (-17011639/125000 : ℚ) vp0000000010001010 := join_branches bp00000000100010100 bp00000000100010101
private noncomputable def vp000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000001000101-V-0000.bin"
noncomputable def vp000000001000101 : Blocks := vp000000001000101_0
private theorem bp0000000010001010 : Branch 0 (-17011639/250000 : ℚ) vp000000001000101 := by
  apply branch_left_normalized (c:=vp0000000010001010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-17011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-17011639/125000 : ℚ) by norm_num]
  exact coverp0000000010001010
private noncomputable def ep0000000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001011-E-0000.bin"
noncomputable def ep0000000010001011 : Blocks := ep0000000010001011_0
private theorem idp0000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000101.list =
    C ((2:ℤ)^85) * horner X vp0000000010001011.list + horner X ep0000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001011 : Branch 1 (-17011639/250000 : ℚ) vp000000001000101 := by
  apply branch_checked idp0000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-17011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-17136639/125000 : ℚ) by norm_num]
  exact coverp0000000010001011
theorem coverp000000001000101 : Covers (-17011639/250000 : ℚ) vp000000001000101 := join_branches bp0000000010001010 bp0000000010001011
private noncomputable def vp000000001000100111_0 : Blocks := edgeBlocks% "full/vectors/000000001000100111-V-0000.bin"
noncomputable def vp000000001000100111 : Blocks := vp000000001000100111_0
theorem coverp000000001000100111 : Covers (-16980389/31250 : ℚ) vp000000001000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000100110_0 : Blocks := edgeBlocks% "full/vectors/000000001000100110-V-0000.bin"
noncomputable def vp000000001000100110 : Blocks := vp000000001000100110_0
theorem coverp000000001000100110 : Covers (-16949139/31250 : ℚ) vp000000001000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010011_0 : Blocks := edgeBlocks% "full/vectors/00000000100010011-V-0000.bin"
noncomputable def vp00000000100010011 : Blocks := vp00000000100010011_0
private theorem bp000000001000100110 : Branch 0 (-16949139/62500 : ℚ) vp00000000100010011 := by
  apply branch_left_normalized (c:=vp000000001000100110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-16949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-16949139/31250 : ℚ) by norm_num]
  exact coverp000000001000100110
private noncomputable def ep000000001000100111_0 : Blocks := edgeBlocks% "full/vectors/000000001000100111-E-0000.bin"
noncomputable def ep000000001000100111 : Blocks := ep000000001000100111_0
private theorem idp000000001000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010011.list =
    C ((2:ℤ)^34) * horner X vp000000001000100111.list + horner X ep000000001000100111.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000100111 : Branch 1 (-16949139/62500 : ℚ) vp00000000100010011 := by
  apply branch_checked idp000000001000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-16949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-16980389/31250 : ℚ) by norm_num]
  exact coverp000000001000100111
theorem coverp00000000100010011 : Covers (-16949139/62500 : ℚ) vp00000000100010011 := join_branches bp000000001000100110 bp000000001000100111
private noncomputable def vp000000001000100101_0 : Blocks := edgeBlocks% "full/vectors/000000001000100101-V-0000.bin"
noncomputable def vp000000001000100101 : Blocks := vp000000001000100101_0
theorem coverp000000001000100101 : Covers (-16917889/31250 : ℚ) vp000000001000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000100100_0 : Blocks := edgeBlocks% "full/vectors/000000001000100100-V-0000.bin"
noncomputable def vp000000001000100100 : Blocks := vp000000001000100100_0
theorem coverp000000001000100100 : Covers (-16886639/31250 : ℚ) vp000000001000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010010_0 : Blocks := edgeBlocks% "full/vectors/00000000100010010-V-0000.bin"
noncomputable def vp00000000100010010 : Blocks := vp00000000100010010_0
private theorem bp000000001000100100 : Branch 0 (-16886639/62500 : ℚ) vp00000000100010010 := by
  apply branch_left_normalized (c:=vp000000001000100100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-16886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-16886639/31250 : ℚ) by norm_num]
  exact coverp000000001000100100
private noncomputable def ep000000001000100101_0 : Blocks := edgeBlocks% "full/vectors/000000001000100101-E-0000.bin"
noncomputable def ep000000001000100101 : Blocks := ep000000001000100101_0
private theorem idp000000001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010010.list =
    C ((2:ℤ)^34) * horner X vp000000001000100101.list + horner X ep000000001000100101.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000100101 : Branch 1 (-16886639/62500 : ℚ) vp00000000100010010 := by
  apply branch_checked idp000000001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-16886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-16917889/31250 : ℚ) by norm_num]
  exact coverp000000001000100101
theorem coverp00000000100010010 : Covers (-16886639/62500 : ℚ) vp00000000100010010 := join_branches bp000000001000100100 bp000000001000100101
private noncomputable def vp0000000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001001-V-0000.bin"
noncomputable def vp0000000010001001 : Blocks := vp0000000010001001_0
private theorem bp00000000100010010 : Branch 0 (-16886639/125000 : ℚ) vp0000000010001001 := by
  apply branch_left_normalized (c:=vp00000000100010010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-16886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-16886639/62500 : ℚ) by norm_num]
  exact coverp00000000100010010
private noncomputable def ep00000000100010011_0 : Blocks := edgeBlocks% "full/vectors/00000000100010011-E-0000.bin"
noncomputable def ep00000000100010011 : Blocks := ep00000000100010011_0
private theorem idp00000000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001001.list =
    C ((2:ℤ)^51) * horner X vp00000000100010011.list + horner X ep00000000100010011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100010011 : Branch 1 (-16886639/125000 : ℚ) vp0000000010001001 := by
  apply branch_checked idp00000000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-16886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-16949139/62500 : ℚ) by norm_num]
  exact coverp00000000100010011
theorem coverp0000000010001001 : Covers (-16886639/125000 : ℚ) vp0000000010001001 := join_branches bp00000000100010010 bp00000000100010011
private noncomputable def vp000000001000100011_0 : Blocks := edgeBlocks% "full/vectors/000000001000100011-V-0000.bin"
noncomputable def vp000000001000100011 : Blocks := vp000000001000100011_0
theorem coverp000000001000100011 : Covers (-16855389/31250 : ℚ) vp000000001000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000100010_0 : Blocks := edgeBlocks% "full/vectors/000000001000100010-V-0000.bin"
noncomputable def vp000000001000100010 : Blocks := vp000000001000100010_0
theorem coverp000000001000100010 : Covers (-16824139/31250 : ℚ) vp000000001000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010001_0 : Blocks := edgeBlocks% "full/vectors/00000000100010001-V-0000.bin"
noncomputable def vp00000000100010001 : Blocks := vp00000000100010001_0
private theorem bp000000001000100010 : Branch 0 (-16824139/62500 : ℚ) vp00000000100010001 := by
  apply branch_left_normalized (c:=vp000000001000100010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-16824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-16824139/31250 : ℚ) by norm_num]
  exact coverp000000001000100010
private noncomputable def ep000000001000100011_0 : Blocks := edgeBlocks% "full/vectors/000000001000100011-E-0000.bin"
noncomputable def ep000000001000100011 : Blocks := ep000000001000100011_0
private theorem idp000000001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010001.list =
    C ((2:ℤ)^34) * horner X vp000000001000100011.list + horner X ep000000001000100011.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000100011 : Branch 1 (-16824139/62500 : ℚ) vp00000000100010001 := by
  apply branch_checked idp000000001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-16824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-16855389/31250 : ℚ) by norm_num]
  exact coverp000000001000100011
theorem coverp00000000100010001 : Covers (-16824139/62500 : ℚ) vp00000000100010001 := join_branches bp000000001000100010 bp000000001000100011
private noncomputable def vp0000000010001000011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000011-V-0000.bin"
noncomputable def vp0000000010001000011 : Blocks := vp0000000010001000011_0
theorem coverp0000000010001000011 : Covers (-16808514/15625 : ℚ) vp0000000010001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000101-V-0000.bin"
noncomputable def vp00000000100010000101 : Blocks := vp00000000100010000101_0
theorem coverp00000000100010000101 : Covers (-33601403/15625 : ℚ) vp00000000100010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010000100_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000100-V-0000.bin"
noncomputable def vp00000000100010000100 : Blocks := vp00000000100010000100_0
theorem coverp00000000100010000100 : Covers (-33585778/15625 : ℚ) vp00000000100010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001000010_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000010-V-0000.bin"
noncomputable def vp0000000010001000010 : Blocks := vp0000000010001000010_0
private theorem bp00000000100010000100 : Branch 0 (-16792889/15625 : ℚ) vp0000000010001000010 := by
  apply branch_left_normalized (c:=vp00000000100010000100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-16792889/15625 : ℚ) - ((0:ℤ):ℚ) = (-33585778/15625 : ℚ) by norm_num]
  exact coverp00000000100010000100
private noncomputable def ep00000000100010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000101-E-0000.bin"
noncomputable def ep00000000100010000101 : Blocks := ep00000000100010000101_0
private theorem idp00000000100010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001000010.list =
    C ((2:ℤ)^17) * horner X vp00000000100010000101.list + horner X ep00000000100010000101.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100010000101 : Branch 1 (-16792889/15625 : ℚ) vp0000000010001000010 := by
  apply branch_checked idp00000000100010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-16792889/15625 : ℚ) - ((1:ℤ):ℚ) = (-33601403/15625 : ℚ) by norm_num]
  exact coverp00000000100010000101
theorem coverp0000000010001000010 : Covers (-16792889/15625 : ℚ) vp0000000010001000010 := join_branches bp00000000100010000100 bp00000000100010000101
private noncomputable def vp000000001000100001_0 : Blocks := edgeBlocks% "full/vectors/000000001000100001-V-0000.bin"
noncomputable def vp000000001000100001 : Blocks := vp000000001000100001_0
private theorem bp0000000010001000010 : Branch 0 (-16792889/31250 : ℚ) vp000000001000100001 := by
  apply branch_left_normalized (c:=vp0000000010001000010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-16792889/31250 : ℚ) - ((0:ℤ):ℚ) = (-16792889/15625 : ℚ) by norm_num]
  exact coverp0000000010001000010
private noncomputable def ep0000000010001000011_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000011-E-0000.bin"
noncomputable def ep0000000010001000011 : Blocks := ep0000000010001000011_0
private theorem idp0000000010001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000100001.list =
    C ((2:ℤ)^23) * horner X vp0000000010001000011.list + horner X ep0000000010001000011.list := by
  exact edge_identity (B := (2:ℤ)^134) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001000011 : Branch 1 (-16792889/31250 : ℚ) vp000000001000100001 := by
  apply branch_checked idp0000000010001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-16792889/31250 : ℚ) - ((1:ℤ):ℚ) = (-16808514/15625 : ℚ) by norm_num]
  exact coverp0000000010001000011
theorem coverp000000001000100001 : Covers (-16792889/31250 : ℚ) vp000000001000100001 := join_branches bp0000000010001000010 bp0000000010001000011
private noncomputable def vp00000000100010000011_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000011-V-0000.bin"
noncomputable def vp00000000100010000011 : Blocks := vp00000000100010000011_0
theorem coverp00000000100010000011 : Covers (-33570153/15625 : ℚ) vp00000000100010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100010000010_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000010-V-0000.bin"
noncomputable def vp00000000100010000010 : Blocks := vp00000000100010000010_0
theorem coverp00000000100010000010 : Covers (-33554528/15625 : ℚ) vp00000000100010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010001000001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000001-V-0000.bin"
noncomputable def vp0000000010001000001 : Blocks := vp0000000010001000001_0
private theorem bp00000000100010000010 : Branch 0 (-16777264/15625 : ℚ) vp0000000010001000001 := by
  apply branch_left_normalized (c:=vp00000000100010000010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-16777264/15625 : ℚ) - ((0:ℤ):ℚ) = (-33554528/15625 : ℚ) by norm_num]
  exact coverp00000000100010000010
private noncomputable def ep00000000100010000011_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000011-E-0000.bin"
noncomputable def ep00000000100010000011 : Blocks := ep00000000100010000011_0
private theorem idp00000000100010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001000001.list =
    C ((2:ℤ)^17) * horner X vp00000000100010000011.list + horner X ep00000000100010000011.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100010000011 : Branch 1 (-16777264/15625 : ℚ) vp0000000010001000001 := by
  apply branch_checked idp00000000100010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-16777264/15625 : ℚ) - ((1:ℤ):ℚ) = (-33570153/15625 : ℚ) by norm_num]
  exact coverp00000000100010000011
theorem coverp0000000010001000001 : Covers (-16777264/15625 : ℚ) vp0000000010001000001 := join_branches bp00000000100010000010 bp00000000100010000011
private noncomputable def vp0000000010001000000_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000000-V-0000.bin"
noncomputable def vp0000000010001000000 : Blocks := vp0000000010001000000_0
theorem coverp0000000010001000000 : Covers (-16761639/15625 : ℚ) vp0000000010001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000100000_0 : Blocks := edgeBlocks% "full/vectors/000000001000100000-V-0000.bin"
noncomputable def vp000000001000100000 : Blocks := vp000000001000100000_0
private theorem bp0000000010001000000 : Branch 0 (-16761639/31250 : ℚ) vp000000001000100000 := by
  apply branch_left_normalized (c:=vp0000000010001000000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-16761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-16761639/15625 : ℚ) by norm_num]
  exact coverp0000000010001000000
private noncomputable def ep0000000010001000001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000001-E-0000.bin"
noncomputable def ep0000000010001000001 : Blocks := ep0000000010001000001_0
private theorem idp0000000010001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000100000.list =
    C ((2:ℤ)^23) * horner X vp0000000010001000001.list + horner X ep0000000010001000001.list := by
  exact edge_identity (B := (2:ℤ)^135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001000001 : Branch 1 (-16761639/31250 : ℚ) vp000000001000100000 := by
  apply branch_checked idp0000000010001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-16777264/15625 : ℚ) by norm_num]
  exact coverp0000000010001000001
theorem coverp000000001000100000 : Covers (-16761639/31250 : ℚ) vp000000001000100000 := join_branches bp0000000010001000000 bp0000000010001000001
private noncomputable def vp00000000100010000_0 : Blocks := edgeBlocks% "full/vectors/00000000100010000-V-0000.bin"
noncomputable def vp00000000100010000 : Blocks := vp00000000100010000_0
private theorem bp000000001000100000 : Branch 0 (-16761639/62500 : ℚ) vp00000000100010000 := by
  apply branch_left_normalized (c:=vp000000001000100000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-16761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-16761639/31250 : ℚ) by norm_num]
  exact coverp000000001000100000
private noncomputable def ep000000001000100001_0 : Blocks := edgeBlocks% "full/vectors/000000001000100001-E-0000.bin"
noncomputable def ep000000001000100001 : Blocks := ep000000001000100001_0
private theorem idp000000001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010000.list =
    C ((2:ℤ)^32) * horner X vp000000001000100001.list + horner X ep000000001000100001.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000100001 : Branch 1 (-16761639/62500 : ℚ) vp00000000100010000 := by
  apply branch_checked idp000000001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-16792889/31250 : ℚ) by norm_num]
  exact coverp000000001000100001
theorem coverp00000000100010000 : Covers (-16761639/62500 : ℚ) vp00000000100010000 := join_branches bp000000001000100000 bp000000001000100001
private noncomputable def vp0000000010001000_0 : Blocks := edgeBlocks% "full/vectors/0000000010001000-V-0000.bin"
noncomputable def vp0000000010001000 : Blocks := vp0000000010001000_0
private theorem bp00000000100010000 : Branch 0 (-16761639/125000 : ℚ) vp0000000010001000 := by
  apply branch_left_normalized (c:=vp00000000100010000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-16761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-16761639/62500 : ℚ) by norm_num]
  exact coverp00000000100010000
private noncomputable def ep00000000100010001_0 : Blocks := edgeBlocks% "full/vectors/00000000100010001-E-0000.bin"
noncomputable def ep00000000100010001 : Blocks := ep00000000100010001_0
private theorem idp00000000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001000.list =
    C ((2:ℤ)^49) * horner X vp00000000100010001.list + horner X ep00000000100010001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100010001 : Branch 1 (-16761639/125000 : ℚ) vp0000000010001000 := by
  apply branch_checked idp00000000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-16824139/62500 : ℚ) by norm_num]
  exact coverp00000000100010001
theorem coverp0000000010001000 : Covers (-16761639/125000 : ℚ) vp0000000010001000 := join_branches bp00000000100010000 bp00000000100010001
private noncomputable def vp000000001000100_0 : Blocks := edgeBlocks% "full/vectors/000000001000100-V-0000.bin"
noncomputable def vp000000001000100 : Blocks := vp000000001000100_0
private theorem bp0000000010001000 : Branch 0 (-16761639/250000 : ℚ) vp000000001000100 := by
  apply branch_left_normalized (c:=vp0000000010001000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-16761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-16761639/125000 : ℚ) by norm_num]
  exact coverp0000000010001000
private noncomputable def ep0000000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001001-E-0000.bin"
noncomputable def ep0000000010001001 : Blocks := ep0000000010001001_0
private theorem idp0000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000100.list =
    C ((2:ℤ)^81) * horner X vp0000000010001001.list + horner X ep0000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001001 : Branch 1 (-16761639/250000 : ℚ) vp000000001000100 := by
  apply branch_checked idp0000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-16886639/125000 : ℚ) by norm_num]
  exact coverp0000000010001001
theorem coverp000000001000100 : Covers (-16761639/250000 : ℚ) vp000000001000100 := join_branches bp0000000010001000 bp0000000010001001
private noncomputable def vp00000000100010_0 : Blocks := edgeBlocks% "full/vectors/00000000100010-V-0000.bin"
private noncomputable def vp00000000100010_1 : Blocks := edgeBlocks% "full/vectors/00000000100010-V-0001.bin"
noncomputable def vp00000000100010 : Blocks := (Blocks.join vp00000000100010_0 vp00000000100010_1)
private theorem bp000000001000100 : Branch 0 (-16761639/500000 : ℚ) vp00000000100010 := by
  apply branch_left_normalized (c:=vp000000001000100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-16761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-16761639/250000 : ℚ) by norm_num]
  exact coverp000000001000100
private noncomputable def ep000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000001000101-E-0000.bin"
private noncomputable def ep000000001000101_1 : Blocks := edgeBlocks% "full/vectors/000000001000101-E-0001.bin"
noncomputable def ep000000001000101 : Blocks := (Blocks.join ep000000001000101_0 ep000000001000101_1)
private theorem idp000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100010.list =
    C ((2:ℤ)^140) * horner X vp000000001000101.list + horner X ep000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000101 : Branch 1 (-16761639/500000 : ℚ) vp00000000100010 := by
  apply branch_checked idp000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-17011639/250000 : ℚ) by norm_num]
  exact coverp000000001000101
theorem coverp00000000100010 : Covers (-16761639/500000 : ℚ) vp00000000100010 := join_branches bp000000001000100 bp000000001000101
private noncomputable def vp0000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001-V-0000.bin"
private noncomputable def vp0000000010001_1 : Blocks := edgeBlocks% "full/vectors/0000000010001-V-0001.bin"
private noncomputable def vp0000000010001_2 : Blocks := edgeBlocks% "full/vectors/0000000010001-V-0002.bin"
noncomputable def vp0000000010001 : Blocks := (Blocks.join vp0000000010001_0 (Blocks.join vp0000000010001_1 vp0000000010001_2))
private theorem bp00000000100010 : Branch 0 (-16761639/1000000 : ℚ) vp0000000010001 := by
  apply branch_left_normalized (c:=vp00000000100010) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-16761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-16761639/500000 : ℚ) by norm_num]
  exact coverp00000000100010
private noncomputable def ep00000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000100011-E-0000.bin"
private noncomputable def ep00000000100011_1 : Blocks := edgeBlocks% "full/vectors/00000000100011-E-0001.bin"
private noncomputable def ep00000000100011_2 : Blocks := edgeBlocks% "full/vectors/00000000100011-E-0002.bin"
noncomputable def ep00000000100011 : Blocks := (Blocks.join ep00000000100011_0 (Blocks.join ep00000000100011_1 ep00000000100011_2))
private theorem idp00000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010001.list =
    C ((2:ℤ)^267) * horner X vp00000000100011.list + horner X ep00000000100011.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100011 : Branch 1 (-16761639/1000000 : ℚ) vp0000000010001 := by
  apply branch_checked idp00000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-16761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-17261639/500000 : ℚ) by norm_num]
  exact coverp00000000100011
theorem coverp0000000010001 : Covers (-16761639/1000000 : ℚ) vp0000000010001 := join_branches bp00000000100010 bp00000000100011
private noncomputable def vp000000001000011111_0 : Blocks := edgeBlocks% "full/vectors/000000001000011111-V-0000.bin"
noncomputable def vp000000001000011111 : Blocks := vp000000001000011111_0
theorem coverp000000001000011111 : Covers (-16730389/31250 : ℚ) vp000000001000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000011110_0 : Blocks := edgeBlocks% "full/vectors/000000001000011110-V-0000.bin"
noncomputable def vp000000001000011110 : Blocks := vp000000001000011110_0
theorem coverp000000001000011110 : Covers (-16699139/31250 : ℚ) vp000000001000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000100001111-V-0000.bin"
noncomputable def vp00000000100001111 : Blocks := vp00000000100001111_0
private theorem bp000000001000011110 : Branch 0 (-16699139/62500 : ℚ) vp00000000100001111 := by
  apply branch_left_normalized (c:=vp000000001000011110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-16699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-16699139/31250 : ℚ) by norm_num]
  exact coverp000000001000011110
private noncomputable def ep000000001000011111_0 : Blocks := edgeBlocks% "full/vectors/000000001000011111-E-0000.bin"
noncomputable def ep000000001000011111 : Blocks := ep000000001000011111_0
private theorem idp000000001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100001111.list =
    C ((2:ℤ)^31) * horner X vp000000001000011111.list + horner X ep000000001000011111.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000011111 : Branch 1 (-16699139/62500 : ℚ) vp00000000100001111 := by
  apply branch_checked idp000000001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-16699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-16730389/31250 : ℚ) by norm_num]
  exact coverp000000001000011111
theorem coverp00000000100001111 : Covers (-16699139/62500 : ℚ) vp00000000100001111 := join_branches bp000000001000011110 bp000000001000011111
private noncomputable def vp00000000100001110_0 : Blocks := edgeBlocks% "full/vectors/00000000100001110-V-0000.bin"
noncomputable def vp00000000100001110 : Blocks := vp00000000100001110_0
theorem coverp00000000100001110 : Covers (-16636639/62500 : ℚ) vp00000000100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010000111_0 : Blocks := edgeBlocks% "full/vectors/0000000010000111-V-0000.bin"
noncomputable def vp0000000010000111 : Blocks := vp0000000010000111_0
private theorem bp00000000100001110 : Branch 0 (-16636639/125000 : ℚ) vp0000000010000111 := by
  apply branch_left_normalized (c:=vp00000000100001110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-16636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-16636639/62500 : ℚ) by norm_num]
  exact coverp00000000100001110
private noncomputable def ep00000000100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000100001111-E-0000.bin"
noncomputable def ep00000000100001111 : Blocks := ep00000000100001111_0
private theorem idp00000000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000111.list =
    C ((2:ℤ)^48) * horner X vp00000000100001111.list + horner X ep00000000100001111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100001111 : Branch 1 (-16636639/125000 : ℚ) vp0000000010000111 := by
  apply branch_checked idp00000000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-16636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-16699139/62500 : ℚ) by norm_num]
  exact coverp00000000100001111
theorem coverp0000000010000111 : Covers (-16636639/125000 : ℚ) vp0000000010000111 := join_branches bp00000000100001110 bp00000000100001111
private noncomputable def vp0000000010000110_0 : Blocks := edgeBlocks% "full/vectors/0000000010000110-V-0000.bin"
noncomputable def vp0000000010000110 : Blocks := vp0000000010000110_0
theorem coverp0000000010000110 : Covers (-16511639/125000 : ℚ) vp0000000010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000001000011-V-0000.bin"
noncomputable def vp000000001000011 : Blocks := vp000000001000011_0
private theorem bp0000000010000110 : Branch 0 (-16511639/250000 : ℚ) vp000000001000011 := by
  apply branch_left_normalized (c:=vp0000000010000110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-16511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-16511639/125000 : ℚ) by norm_num]
  exact coverp0000000010000110
private noncomputable def ep0000000010000111_0 : Blocks := edgeBlocks% "full/vectors/0000000010000111-E-0000.bin"
noncomputable def ep0000000010000111 : Blocks := ep0000000010000111_0
private theorem idp0000000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000011.list =
    C ((2:ℤ)^79) * horner X vp0000000010000111.list + horner X ep0000000010000111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010000111 : Branch 1 (-16511639/250000 : ℚ) vp000000001000011 := by
  apply branch_checked idp0000000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-16511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-16636639/125000 : ℚ) by norm_num]
  exact coverp0000000010000111
theorem coverp000000001000011 : Covers (-16511639/250000 : ℚ) vp000000001000011 := join_branches bp0000000010000110 bp0000000010000111
private noncomputable def vp0000000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000000010000101-V-0000.bin"
noncomputable def vp0000000010000101 : Blocks := vp0000000010000101_0
theorem coverp0000000010000101 : Covers (-16386639/125000 : ℚ) vp0000000010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010000100_0 : Blocks := edgeBlocks% "full/vectors/0000000010000100-V-0000.bin"
noncomputable def vp0000000010000100 : Blocks := vp0000000010000100_0
theorem coverp0000000010000100 : Covers (-16261639/125000 : ℚ) vp0000000010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000010_0 : Blocks := edgeBlocks% "full/vectors/000000001000010-V-0000.bin"
noncomputable def vp000000001000010 : Blocks := vp000000001000010_0
private theorem bp0000000010000100 : Branch 0 (-16261639/250000 : ℚ) vp000000001000010 := by
  apply branch_left_normalized (c:=vp0000000010000100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-16261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-16261639/125000 : ℚ) by norm_num]
  exact coverp0000000010000100
private noncomputable def ep0000000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000000010000101-E-0000.bin"
noncomputable def ep0000000010000101 : Blocks := ep0000000010000101_0
private theorem idp0000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000010.list =
    C ((2:ℤ)^83) * horner X vp0000000010000101.list + horner X ep0000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010000101 : Branch 1 (-16261639/250000 : ℚ) vp000000001000010 := by
  apply branch_checked idp0000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-16261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-16386639/125000 : ℚ) by norm_num]
  exact coverp0000000010000101
theorem coverp000000001000010 : Covers (-16261639/250000 : ℚ) vp000000001000010 := join_branches bp0000000010000100 bp0000000010000101
private noncomputable def vp00000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000100001-V-0000.bin"
private noncomputable def vp00000000100001_1 : Blocks := edgeBlocks% "full/vectors/00000000100001-V-0001.bin"
noncomputable def vp00000000100001 : Blocks := (Blocks.join vp00000000100001_0 vp00000000100001_1)
private theorem bp000000001000010 : Branch 0 (-16261639/500000 : ℚ) vp00000000100001 := by
  apply branch_left_normalized (c:=vp000000001000010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-16261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-16261639/250000 : ℚ) by norm_num]
  exact coverp000000001000010
private noncomputable def ep000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000001000011-E-0000.bin"
private noncomputable def ep000000001000011_1 : Blocks := edgeBlocks% "full/vectors/000000001000011-E-0001.bin"
noncomputable def ep000000001000011 : Blocks := (Blocks.join ep000000001000011_0 ep000000001000011_1)
private theorem idp000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100001.list =
    C ((2:ℤ)^146) * horner X vp000000001000011.list + horner X ep000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000011 : Branch 1 (-16261639/500000 : ℚ) vp00000000100001 := by
  apply branch_checked idp000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-16261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-16511639/250000 : ℚ) by norm_num]
  exact coverp000000001000011
theorem coverp00000000100001 : Covers (-16261639/500000 : ℚ) vp00000000100001 := join_branches bp000000001000010 bp000000001000011
private noncomputable def vp00000000100000111_0 : Blocks := edgeBlocks% "full/vectors/00000000100000111-V-0000.bin"
noncomputable def vp00000000100000111 : Blocks := vp00000000100000111_0
theorem coverp00000000100000111 : Covers (-16199139/62500 : ℚ) vp00000000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100000110_0 : Blocks := edgeBlocks% "full/vectors/00000000100000110-V-0000.bin"
noncomputable def vp00000000100000110 : Blocks := vp00000000100000110_0
theorem coverp00000000100000110 : Covers (-16136639/62500 : ℚ) vp00000000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000010000011-V-0000.bin"
noncomputable def vp0000000010000011 : Blocks := vp0000000010000011_0
private theorem bp00000000100000110 : Branch 0 (-16136639/125000 : ℚ) vp0000000010000011 := by
  apply branch_left_normalized (c:=vp00000000100000110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-16136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-16136639/62500 : ℚ) by norm_num]
  exact coverp00000000100000110
private noncomputable def ep00000000100000111_0 : Blocks := edgeBlocks% "full/vectors/00000000100000111-E-0000.bin"
noncomputable def ep00000000100000111 : Blocks := ep00000000100000111_0
private theorem idp00000000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000011.list =
    C ((2:ℤ)^54) * horner X vp00000000100000111.list + horner X ep00000000100000111.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100000111 : Branch 1 (-16136639/125000 : ℚ) vp0000000010000011 := by
  apply branch_checked idp00000000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-16136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-16199139/62500 : ℚ) by norm_num]
  exact coverp00000000100000111
theorem coverp0000000010000011 : Covers (-16136639/125000 : ℚ) vp0000000010000011 := join_branches bp00000000100000110 bp00000000100000111
private noncomputable def vp00000000100000101_0 : Blocks := edgeBlocks% "full/vectors/00000000100000101-V-0000.bin"
noncomputable def vp00000000100000101 : Blocks := vp00000000100000101_0
theorem coverp00000000100000101 : Covers (-16074139/62500 : ℚ) vp00000000100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100000100_0 : Blocks := edgeBlocks% "full/vectors/00000000100000100-V-0000.bin"
noncomputable def vp00000000100000100 : Blocks := vp00000000100000100_0
theorem coverp00000000100000100 : Covers (-16011639/62500 : ℚ) vp00000000100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010000010_0 : Blocks := edgeBlocks% "full/vectors/0000000010000010-V-0000.bin"
noncomputable def vp0000000010000010 : Blocks := vp0000000010000010_0
private theorem bp00000000100000100 : Branch 0 (-16011639/125000 : ℚ) vp0000000010000010 := by
  apply branch_left_normalized (c:=vp00000000100000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-16011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-16011639/62500 : ℚ) by norm_num]
  exact coverp00000000100000100
private noncomputable def ep00000000100000101_0 : Blocks := edgeBlocks% "full/vectors/00000000100000101-E-0000.bin"
noncomputable def ep00000000100000101 : Blocks := ep00000000100000101_0
private theorem idp00000000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000010.list =
    C ((2:ℤ)^53) * horner X vp00000000100000101.list + horner X ep00000000100000101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100000101 : Branch 1 (-16011639/125000 : ℚ) vp0000000010000010 := by
  apply branch_checked idp00000000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-16011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-16074139/62500 : ℚ) by norm_num]
  exact coverp00000000100000101
theorem coverp0000000010000010 : Covers (-16011639/125000 : ℚ) vp0000000010000010 := join_branches bp00000000100000100 bp00000000100000101
private noncomputable def vp000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000001000001-V-0000.bin"
noncomputable def vp000000001000001 : Blocks := vp000000001000001_0
private theorem bp0000000010000010 : Branch 0 (-16011639/250000 : ℚ) vp000000001000001 := by
  apply branch_left_normalized (c:=vp0000000010000010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-16011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-16011639/125000 : ℚ) by norm_num]
  exact coverp0000000010000010
private noncomputable def ep0000000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000010000011-E-0000.bin"
noncomputable def ep0000000010000011 : Blocks := ep0000000010000011_0
private theorem idp0000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000001.list =
    C ((2:ℤ)^86) * horner X vp0000000010000011.list + horner X ep0000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010000011 : Branch 1 (-16011639/250000 : ℚ) vp000000001000001 := by
  apply branch_checked idp0000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-16011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-16136639/125000 : ℚ) by norm_num]
  exact coverp0000000010000011
theorem coverp000000001000001 : Covers (-16011639/250000 : ℚ) vp000000001000001 := join_branches bp0000000010000010 bp0000000010000011
private noncomputable def vp00000000100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000100000011-V-0000.bin"
noncomputable def vp00000000100000011 : Blocks := vp00000000100000011_0
theorem coverp00000000100000011 : Covers (-15949139/62500 : ℚ) vp00000000100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000000101_0 : Blocks := edgeBlocks% "full/vectors/000000001000000101-V-0000.bin"
noncomputable def vp000000001000000101 : Blocks := vp000000001000000101_0
theorem coverp000000001000000101 : Covers (-15917889/31250 : ℚ) vp000000001000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001000000100_0 : Blocks := edgeBlocks% "full/vectors/000000001000000100-V-0000.bin"
noncomputable def vp000000001000000100 : Blocks := vp000000001000000100_0
theorem coverp000000001000000100 : Covers (-15886639/31250 : ℚ) vp000000001000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100000010_0 : Blocks := edgeBlocks% "full/vectors/00000000100000010-V-0000.bin"
noncomputable def vp00000000100000010 : Blocks := vp00000000100000010_0
private theorem bp000000001000000100 : Branch 0 (-15886639/62500 : ℚ) vp00000000100000010 := by
  apply branch_left_normalized (c:=vp000000001000000100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-15886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-15886639/31250 : ℚ) by norm_num]
  exact coverp000000001000000100
private noncomputable def ep000000001000000101_0 : Blocks := edgeBlocks% "full/vectors/000000001000000101-E-0000.bin"
noncomputable def ep000000001000000101 : Blocks := ep000000001000000101_0
private theorem idp000000001000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100000010.list =
    C ((2:ℤ)^34) * horner X vp000000001000000101.list + horner X ep000000001000000101.list := by
  exact edge_identity (B := (2:ℤ)^147) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000000101 : Branch 1 (-15886639/62500 : ℚ) vp00000000100000010 := by
  apply branch_checked idp000000001000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-15886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-15917889/31250 : ℚ) by norm_num]
  exact coverp000000001000000101
theorem coverp00000000100000010 : Covers (-15886639/62500 : ℚ) vp00000000100000010 := join_branches bp000000001000000100 bp000000001000000101
private noncomputable def vp0000000010000001_0 : Blocks := edgeBlocks% "full/vectors/0000000010000001-V-0000.bin"
noncomputable def vp0000000010000001 : Blocks := vp0000000010000001_0
private theorem bp00000000100000010 : Branch 0 (-15886639/125000 : ℚ) vp0000000010000001 := by
  apply branch_left_normalized (c:=vp00000000100000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-15886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15886639/62500 : ℚ) by norm_num]
  exact coverp00000000100000010
private noncomputable def ep00000000100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000100000011-E-0000.bin"
noncomputable def ep00000000100000011 : Blocks := ep00000000100000011_0
private theorem idp00000000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000001.list =
    C ((2:ℤ)^52) * horner X vp00000000100000011.list + horner X ep00000000100000011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100000011 : Branch 1 (-15886639/125000 : ℚ) vp0000000010000001 := by
  apply branch_checked idp00000000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-15886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15949139/62500 : ℚ) by norm_num]
  exact coverp00000000100000011
theorem coverp0000000010000001 : Covers (-15886639/125000 : ℚ) vp0000000010000001 := join_branches bp00000000100000010 bp00000000100000011
private noncomputable def vp00000000100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000100000001-V-0000.bin"
noncomputable def vp00000000100000001 : Blocks := vp00000000100000001_0
theorem coverp00000000100000001 : Covers (-15824139/62500 : ℚ) vp00000000100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000100000000_0 : Blocks := edgeBlocks% "full/vectors/00000000100000000-V-0000.bin"
noncomputable def vp00000000100000000 : Blocks := vp00000000100000000_0
theorem coverp00000000100000000 : Covers (-15761639/62500 : ℚ) vp00000000100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000010000000_0 : Blocks := edgeBlocks% "full/vectors/0000000010000000-V-0000.bin"
noncomputable def vp0000000010000000 : Blocks := vp0000000010000000_0
private theorem bp00000000100000000 : Branch 0 (-15761639/125000 : ℚ) vp0000000010000000 := by
  apply branch_left_normalized (c:=vp00000000100000000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-15761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/62500 : ℚ) by norm_num]
  exact coverp00000000100000000
private noncomputable def ep00000000100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000100000001-E-0000.bin"
noncomputable def ep00000000100000001 : Blocks := ep00000000100000001_0
private theorem idp00000000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000000.list =
    C ((2:ℤ)^53) * horner X vp00000000100000001.list + horner X ep00000000100000001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100000001 : Branch 1 (-15761639/125000 : ℚ) vp0000000010000000 := by
  apply branch_checked idp00000000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15824139/62500 : ℚ) by norm_num]
  exact coverp00000000100000001
theorem coverp0000000010000000 : Covers (-15761639/125000 : ℚ) vp0000000010000000 := join_branches bp00000000100000000 bp00000000100000001
private noncomputable def vp000000001000000_0 : Blocks := edgeBlocks% "full/vectors/000000001000000-V-0000.bin"
noncomputable def vp000000001000000 : Blocks := vp000000001000000_0
private theorem bp0000000010000000 : Branch 0 (-15761639/250000 : ℚ) vp000000001000000 := by
  apply branch_left_normalized (c:=vp0000000010000000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-15761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/125000 : ℚ) by norm_num]
  exact coverp0000000010000000
private noncomputable def ep0000000010000001_0 : Blocks := edgeBlocks% "full/vectors/0000000010000001-E-0000.bin"
noncomputable def ep0000000010000001 : Blocks := ep0000000010000001_0
private theorem idp0000000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000000.list =
    C ((2:ℤ)^86) * horner X vp0000000010000001.list + horner X ep0000000010000001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010000001 : Branch 1 (-15761639/250000 : ℚ) vp000000001000000 := by
  apply branch_checked idp0000000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-15886639/125000 : ℚ) by norm_num]
  exact coverp0000000010000001
theorem coverp000000001000000 : Covers (-15761639/250000 : ℚ) vp000000001000000 := join_branches bp0000000010000000 bp0000000010000001
private noncomputable def vp00000000100000_0 : Blocks := edgeBlocks% "full/vectors/00000000100000-V-0000.bin"
private noncomputable def vp00000000100000_1 : Blocks := edgeBlocks% "full/vectors/00000000100000-V-0001.bin"
noncomputable def vp00000000100000 : Blocks := (Blocks.join vp00000000100000_0 vp00000000100000_1)
private theorem bp000000001000000 : Branch 0 (-15761639/500000 : ℚ) vp00000000100000 := by
  apply branch_left_normalized (c:=vp000000001000000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-15761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/250000 : ℚ) by norm_num]
  exact coverp000000001000000
private noncomputable def ep000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000001000001-E-0000.bin"
private noncomputable def ep000000001000001_1 : Blocks := edgeBlocks% "full/vectors/000000001000001-E-0001.bin"
noncomputable def ep000000001000001 : Blocks := (Blocks.join ep000000001000001_0 ep000000001000001_1)
private theorem idp000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100000.list =
    C ((2:ℤ)^150) * horner X vp000000001000001.list + horner X ep000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001000001 : Branch 1 (-15761639/500000 : ℚ) vp00000000100000 := by
  apply branch_checked idp000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-16011639/250000 : ℚ) by norm_num]
  exact coverp000000001000001
theorem coverp00000000100000 : Covers (-15761639/500000 : ℚ) vp00000000100000 := join_branches bp000000001000000 bp000000001000001
private noncomputable def vp0000000010000_0 : Blocks := edgeBlocks% "full/vectors/0000000010000-V-0000.bin"
private noncomputable def vp0000000010000_1 : Blocks := edgeBlocks% "full/vectors/0000000010000-V-0001.bin"
private noncomputable def vp0000000010000_2 : Blocks := edgeBlocks% "full/vectors/0000000010000-V-0002.bin"
noncomputable def vp0000000010000 : Blocks := (Blocks.join vp0000000010000_0 (Blocks.join vp0000000010000_1 vp0000000010000_2))
private theorem bp00000000100000 : Branch 0 (-15761639/1000000 : ℚ) vp0000000010000 := by
  apply branch_left_normalized (c:=vp00000000100000) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-15761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/500000 : ℚ) by norm_num]
  exact coverp00000000100000
private noncomputable def ep00000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000100001-E-0000.bin"
private noncomputable def ep00000000100001_1 : Blocks := edgeBlocks% "full/vectors/00000000100001-E-0001.bin"
private noncomputable def ep00000000100001_2 : Blocks := edgeBlocks% "full/vectors/00000000100001-E-0002.bin"
noncomputable def ep00000000100001 : Blocks := (Blocks.join ep00000000100001_0 (Blocks.join ep00000000100001_1 ep00000000100001_2))
private theorem idp00000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010000.list =
    C ((2:ℤ)^279) * horner X vp00000000100001.list + horner X ep00000000100001.list := by
  exact edge_identity (B := (2:ℤ)^505) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000100001 : Branch 1 (-15761639/1000000 : ℚ) vp0000000010000 := by
  apply branch_checked idp00000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-16261639/500000 : ℚ) by norm_num]
  exact coverp00000000100001
theorem coverp0000000010000 : Covers (-15761639/1000000 : ℚ) vp0000000010000 := join_branches bp00000000100000 bp00000000100001
private noncomputable def vp000000001000_0 : Blocks := edgeBlocks% "full/vectors/000000001000-V-0000.bin"
private noncomputable def vp000000001000_1 : Blocks := edgeBlocks% "full/vectors/000000001000-V-0001.bin"
private noncomputable def vp000000001000_2 : Blocks := edgeBlocks% "full/vectors/000000001000-V-0002.bin"
private noncomputable def vp000000001000_3 : Blocks := edgeBlocks% "full/vectors/000000001000-V-0003.bin"
private noncomputable def vp000000001000_4 : Blocks := edgeBlocks% "full/vectors/000000001000-V-0004.bin"
noncomputable def vp000000001000 : Blocks := (Blocks.join (Blocks.join vp000000001000_0 vp000000001000_1) (Blocks.join vp000000001000_2 (Blocks.join vp000000001000_3 vp000000001000_4)))
private theorem bp0000000010000 : Branch 0 (-15761639/2000000 : ℚ) vp000000001000 := by
  apply branch_left_normalized (c:=vp0000000010000) (k:=0) (m:=269) (by decide +kernel)
  rw [show 2*(-15761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010000
private noncomputable def ep0000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000010001-E-0000.bin"
private noncomputable def ep0000000010001_1 : Blocks := edgeBlocks% "full/vectors/0000000010001-E-0001.bin"
private noncomputable def ep0000000010001_2 : Blocks := edgeBlocks% "full/vectors/0000000010001-E-0002.bin"
private noncomputable def ep0000000010001_3 : Blocks := edgeBlocks% "full/vectors/0000000010001-E-0003.bin"
private noncomputable def ep0000000010001_4 : Blocks := edgeBlocks% "full/vectors/0000000010001-E-0004.bin"
noncomputable def ep0000000010001 : Blocks := (Blocks.join (Blocks.join ep0000000010001_0 ep0000000010001_1) (Blocks.join ep0000000010001_2 (Blocks.join ep0000000010001_3 ep0000000010001_4)))
private theorem idp0000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001000.list =
    C ((2:ℤ)^524) * horner X vp0000000010001.list + horner X ep0000000010001.list := by
  exact edge_identity (B := (2:ℤ)^879) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000010001 : Branch 1 (-15761639/2000000 : ℚ) vp000000001000 := by
  apply branch_checked idp0000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-16761639/1000000 : ℚ) by norm_num]
  exact coverp0000000010001
theorem coverp000000001000 : Covers (-15761639/2000000 : ℚ) vp000000001000 := join_branches bp0000000010000 bp0000000010001
private noncomputable def vp00000000100_0 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0000.bin"
private noncomputable def vp00000000100_1 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0001.bin"
private noncomputable def vp00000000100_2 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0002.bin"
private noncomputable def vp00000000100_3 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0003.bin"
private noncomputable def vp00000000100_4 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0004.bin"
private noncomputable def vp00000000100_5 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0005.bin"
private noncomputable def vp00000000100_6 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0006.bin"
private noncomputable def vp00000000100_7 : Blocks := edgeBlocks% "full/vectors/00000000100-V-0007.bin"
noncomputable def vp00000000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00000000100_0 vp00000000100_1) (Blocks.join vp00000000100_2 vp00000000100_3)) (Blocks.join (Blocks.join vp00000000100_4 vp00000000100_5) (Blocks.join vp00000000100_6 vp00000000100_7)))
private theorem bp000000001000 : Branch 0 (-15761639/4000000 : ℚ) vp00000000100 := by
  apply branch_left_normalized (c:=vp000000001000) (k:=0) (m:=513) (by decide +kernel)
  rw [show 2*(-15761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/2000000 : ℚ) by norm_num]
  exact coverp000000001000
private noncomputable def ep000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0000.bin"
private noncomputable def ep000000001001_1 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0001.bin"
private noncomputable def ep000000001001_2 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0002.bin"
private noncomputable def ep000000001001_3 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0003.bin"
private noncomputable def ep000000001001_4 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0004.bin"
private noncomputable def ep000000001001_5 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0005.bin"
private noncomputable def ep000000001001_6 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0006.bin"
private noncomputable def ep000000001001_7 : Blocks := edgeBlocks% "full/vectors/000000001001-E-0007.bin"
noncomputable def ep000000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000000001001_0 ep000000001001_1) (Blocks.join ep000000001001_2 ep000000001001_3)) (Blocks.join (Blocks.join ep000000001001_4 ep000000001001_5) (Blocks.join ep000000001001_6 ep000000001001_7)))
private theorem idp000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000100.list =
    C ((2:ℤ)^1009) * horner X vp000000001001.list + horner X ep000000001001.list := by
  exact edge_identity (B := (2:ℤ)^1619) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001001 : Branch 1 (-15761639/4000000 : ℚ) vp00000000100 := by
  apply branch_checked idp000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-17761639/2000000 : ℚ) by norm_num]
  exact coverp000000001001
theorem coverp00000000100 : Covers (-15761639/4000000 : ℚ) vp00000000100 := join_branches bp000000001000 bp000000001001
private noncomputable def vp0000000010_0 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0000.bin"
private noncomputable def vp0000000010_1 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0001.bin"
private noncomputable def vp0000000010_2 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0002.bin"
private noncomputable def vp0000000010_3 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0003.bin"
private noncomputable def vp0000000010_4 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0004.bin"
private noncomputable def vp0000000010_5 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0005.bin"
private noncomputable def vp0000000010_6 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0006.bin"
private noncomputable def vp0000000010_7 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0007.bin"
private noncomputable def vp0000000010_8 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0008.bin"
private noncomputable def vp0000000010_9 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0009.bin"
private noncomputable def vp0000000010_10 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0010.bin"
private noncomputable def vp0000000010_11 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0011.bin"
private noncomputable def vp0000000010_12 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0012.bin"
private noncomputable def vp0000000010_13 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0013.bin"
private noncomputable def vp0000000010_14 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0014.bin"
private noncomputable def vp0000000010_15 : Blocks := edgeBlocks% "full/vectors/0000000010-V-0015.bin"
noncomputable def vp0000000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000000010_0 vp0000000010_1) (Blocks.join vp0000000010_2 vp0000000010_3)) (Blocks.join (Blocks.join vp0000000010_4 vp0000000010_5) (Blocks.join vp0000000010_6 vp0000000010_7))) (Blocks.join (Blocks.join (Blocks.join vp0000000010_8 vp0000000010_9) (Blocks.join vp0000000010_10 vp0000000010_11)) (Blocks.join (Blocks.join vp0000000010_12 vp0000000010_13) (Blocks.join vp0000000010_14 vp0000000010_15))))
private theorem bp00000000100 : Branch 0 (-15761639/8000000 : ℚ) vp0000000010 := by
  apply branch_left_normalized (c:=vp00000000100) (k:=0) (m:=994) (by decide +kernel)
  rw [show 2*(-15761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/4000000 : ℚ) by norm_num]
  exact coverp00000000100
private noncomputable def ep00000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0000.bin"
private noncomputable def ep00000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0001.bin"
private noncomputable def ep00000000101_2 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0002.bin"
private noncomputable def ep00000000101_3 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0003.bin"
private noncomputable def ep00000000101_4 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0004.bin"
private noncomputable def ep00000000101_5 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0005.bin"
private noncomputable def ep00000000101_6 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0006.bin"
private noncomputable def ep00000000101_7 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0007.bin"
private noncomputable def ep00000000101_8 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0008.bin"
private noncomputable def ep00000000101_9 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0009.bin"
private noncomputable def ep00000000101_10 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0010.bin"
private noncomputable def ep00000000101_11 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0011.bin"
private noncomputable def ep00000000101_12 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0012.bin"
private noncomputable def ep00000000101_13 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0013.bin"
private noncomputable def ep00000000101_14 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0014.bin"
private noncomputable def ep00000000101_15 : Blocks := edgeBlocks% "full/vectors/00000000101-E-0015.bin"
noncomputable def ep00000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000000101_0 ep00000000101_1) (Blocks.join ep00000000101_2 ep00000000101_3)) (Blocks.join (Blocks.join ep00000000101_4 ep00000000101_5) (Blocks.join ep00000000101_6 ep00000000101_7))) (Blocks.join (Blocks.join (Blocks.join ep00000000101_8 ep00000000101_9) (Blocks.join ep00000000101_10 ep00000000101_11)) (Blocks.join (Blocks.join ep00000000101_12 ep00000000101_13) (Blocks.join ep00000000101_14 ep00000000101_15))))
private theorem idp00000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000010.list =
    C ((2:ℤ)^1971) * horner X vp00000000101.list + horner X ep00000000101.list := by
  exact edge_identity (B := (2:ℤ)^3072) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000101 : Branch 1 (-15761639/8000000 : ℚ) vp0000000010 := by
  apply branch_checked idp00000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-19761639/4000000 : ℚ) by norm_num]
  exact coverp00000000101
theorem coverp0000000010 : Covers (-15761639/8000000 : ℚ) vp0000000010 := join_branches bp00000000100 bp00000000101
end NextProof.EdgeFull

