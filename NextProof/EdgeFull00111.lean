import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00110

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp01000011111_0 : Blocks := edgeBlocks% "full/vectors/01000011111-V-0000.bin"
noncomputable def vp01000011111 : Blocks := vp01000011111_0
theorem coverp01000011111 : Covers (-2171761639/4000000 : ℚ) vp01000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011110_0 : Blocks := edgeBlocks% "full/vectors/01000011110-V-0000.bin"
noncomputable def vp01000011110 : Blocks := vp01000011110_0
theorem coverp01000011110 : Covers (-2167761639/4000000 : ℚ) vp01000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0100001111_0 : Blocks := edgeBlocks% "full/vectors/0100001111-V-0000.bin"
private noncomputable def vp0100001111_1 : Blocks := edgeBlocks% "full/vectors/0100001111-V-0001.bin"
noncomputable def vp0100001111 : Blocks := (Blocks.join vp0100001111_0 vp0100001111_1)
private theorem bp01000011110 : Branch 0 (-2167761639/8000000 : ℚ) vp0100001111 := by
  apply branch_left_normalized (c:=vp01000011110) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2167761639/4000000 : ℚ) by norm_num]
  exact coverp01000011110
private noncomputable def ep01000011111_0 : Blocks := edgeBlocks% "full/vectors/01000011111-E-0000.bin"
private noncomputable def ep01000011111_1 : Blocks := edgeBlocks% "full/vectors/01000011111-E-0001.bin"
noncomputable def ep01000011111 : Blocks := (Blocks.join ep01000011111_0 ep01000011111_1)
private theorem idp01000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001111.list =
    C ((2:ℤ)^209) * horner X vp01000011111.list + horner X ep01000011111.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000011111 : Branch 1 (-2167761639/8000000 : ℚ) vp0100001111 := by
  apply branch_checked idp01000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2171761639/4000000 : ℚ) by norm_num]
  exact coverp01000011111
theorem coverp0100001111 : Covers (-2167761639/8000000 : ℚ) vp0100001111 := join_branches bp01000011110 bp01000011111
private noncomputable def vp010000111011_0 : Blocks := edgeBlocks% "full/vectors/010000111011-V-0000.bin"
noncomputable def vp010000111011 : Blocks := vp010000111011_0
theorem coverp010000111011 : Covers (-2165761639/2000000 : ℚ) vp010000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000111010_0 : Blocks := edgeBlocks% "full/vectors/010000111010-V-0000.bin"
noncomputable def vp010000111010 : Blocks := vp010000111010_0
theorem coverp010000111010 : Covers (-2163761639/2000000 : ℚ) vp010000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011101_0 : Blocks := edgeBlocks% "full/vectors/01000011101-V-0000.bin"
noncomputable def vp01000011101 : Blocks := vp01000011101_0
private theorem bp010000111010 : Branch 0 (-2163761639/4000000 : ℚ) vp01000011101 := by
  apply branch_left_normalized (c:=vp010000111010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2163761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2163761639/2000000 : ℚ) by norm_num]
  exact coverp010000111010
private noncomputable def ep010000111011_0 : Blocks := edgeBlocks% "full/vectors/010000111011-E-0000.bin"
noncomputable def ep010000111011 : Blocks := ep010000111011_0
private theorem idp010000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011101.list =
    C ((2:ℤ)^114) * horner X vp010000111011.list + horner X ep010000111011.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000111011 : Branch 1 (-2163761639/4000000 : ℚ) vp01000011101 := by
  apply branch_checked idp010000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2163761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2165761639/2000000 : ℚ) by norm_num]
  exact coverp010000111011
theorem coverp01000011101 : Covers (-2163761639/4000000 : ℚ) vp01000011101 := join_branches bp010000111010 bp010000111011
private noncomputable def vp010000111001_0 : Blocks := edgeBlocks% "full/vectors/010000111001-V-0000.bin"
noncomputable def vp010000111001 : Blocks := vp010000111001_0
theorem coverp010000111001 : Covers (-2161761639/2000000 : ℚ) vp010000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000111000_0 : Blocks := edgeBlocks% "full/vectors/010000111000-V-0000.bin"
noncomputable def vp010000111000 : Blocks := vp010000111000_0
theorem coverp010000111000 : Covers (-2159761639/2000000 : ℚ) vp010000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011100_0 : Blocks := edgeBlocks% "full/vectors/01000011100-V-0000.bin"
noncomputable def vp01000011100 : Blocks := vp01000011100_0
private theorem bp010000111000 : Branch 0 (-2159761639/4000000 : ℚ) vp01000011100 := by
  apply branch_left_normalized (c:=vp010000111000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2159761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2159761639/2000000 : ℚ) by norm_num]
  exact coverp010000111000
private noncomputable def ep010000111001_0 : Blocks := edgeBlocks% "full/vectors/010000111001-E-0000.bin"
noncomputable def ep010000111001 : Blocks := ep010000111001_0
private theorem idp010000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011100.list =
    C ((2:ℤ)^115) * horner X vp010000111001.list + horner X ep010000111001.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000111001 : Branch 1 (-2159761639/4000000 : ℚ) vp01000011100 := by
  apply branch_checked idp010000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2159761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2161761639/2000000 : ℚ) by norm_num]
  exact coverp010000111001
theorem coverp01000011100 : Covers (-2159761639/4000000 : ℚ) vp01000011100 := join_branches bp010000111000 bp010000111001
private noncomputable def vp0100001110_0 : Blocks := edgeBlocks% "full/vectors/0100001110-V-0000.bin"
private noncomputable def vp0100001110_1 : Blocks := edgeBlocks% "full/vectors/0100001110-V-0001.bin"
noncomputable def vp0100001110 : Blocks := (Blocks.join vp0100001110_0 vp0100001110_1)
private theorem bp01000011100 : Branch 0 (-2159761639/8000000 : ℚ) vp0100001110 := by
  apply branch_left_normalized (c:=vp01000011100) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-2159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2159761639/4000000 : ℚ) by norm_num]
  exact coverp01000011100
private noncomputable def ep01000011101_0 : Blocks := edgeBlocks% "full/vectors/01000011101-E-0000.bin"
private noncomputable def ep01000011101_1 : Blocks := edgeBlocks% "full/vectors/01000011101-E-0001.bin"
noncomputable def ep01000011101 : Blocks := (Blocks.join ep01000011101_0 ep01000011101_1)
private theorem idp01000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001110.list =
    C ((2:ℤ)^213) * horner X vp01000011101.list + horner X ep01000011101.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000011101 : Branch 1 (-2159761639/8000000 : ℚ) vp0100001110 := by
  apply branch_checked idp01000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2163761639/4000000 : ℚ) by norm_num]
  exact coverp01000011101
theorem coverp0100001110 : Covers (-2159761639/8000000 : ℚ) vp0100001110 := join_branches bp01000011100 bp01000011101
private noncomputable def vp010000111_0 : Blocks := edgeBlocks% "full/vectors/010000111-V-0000.bin"
private noncomputable def vp010000111_1 : Blocks := edgeBlocks% "full/vectors/010000111-V-0001.bin"
private noncomputable def vp010000111_2 : Blocks := edgeBlocks% "full/vectors/010000111-V-0002.bin"
noncomputable def vp010000111 : Blocks := (Blocks.join vp010000111_0 (Blocks.join vp010000111_1 vp010000111_2))
private theorem bp0100001110 : Branch 0 (-2159761639/16000000 : ℚ) vp010000111 := by
  apply branch_left_normalized (c:=vp0100001110) (k:=0) (m:=187) (by decide +kernel)
  rw [show 2*(-2159761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2159761639/8000000 : ℚ) by norm_num]
  exact coverp0100001110
private noncomputable def ep0100001111_0 : Blocks := edgeBlocks% "full/vectors/0100001111-E-0000.bin"
private noncomputable def ep0100001111_1 : Blocks := edgeBlocks% "full/vectors/0100001111-E-0001.bin"
private noncomputable def ep0100001111_2 : Blocks := edgeBlocks% "full/vectors/0100001111-E-0002.bin"
noncomputable def ep0100001111 : Blocks := (Blocks.join ep0100001111_0 (Blocks.join ep0100001111_1 ep0100001111_2))
private theorem idp0100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000111.list =
    C ((2:ℤ)^405) * horner X vp0100001111.list + horner X ep0100001111.list := by
  exact edge_identity (B := (2:ℤ)^629) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100001111 : Branch 1 (-2159761639/16000000 : ℚ) vp010000111 := by
  apply branch_checked idp0100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2159761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2167761639/8000000 : ℚ) by norm_num]
  exact coverp0100001111
theorem coverp010000111 : Covers (-2159761639/16000000 : ℚ) vp010000111 := join_branches bp0100001110 bp0100001111
private noncomputable def vp010000110111_0 : Blocks := edgeBlocks% "full/vectors/010000110111-V-0000.bin"
noncomputable def vp010000110111 : Blocks := vp010000110111_0
theorem coverp010000110111 : Covers (-2157761639/2000000 : ℚ) vp010000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000110110_0 : Blocks := edgeBlocks% "full/vectors/010000110110-V-0000.bin"
noncomputable def vp010000110110 : Blocks := vp010000110110_0
theorem coverp010000110110 : Covers (-2155761639/2000000 : ℚ) vp010000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011011_0 : Blocks := edgeBlocks% "full/vectors/01000011011-V-0000.bin"
noncomputable def vp01000011011 : Blocks := vp01000011011_0
private theorem bp010000110110 : Branch 0 (-2155761639/4000000 : ℚ) vp01000011011 := by
  apply branch_left_normalized (c:=vp010000110110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2155761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2155761639/2000000 : ℚ) by norm_num]
  exact coverp010000110110
private noncomputable def ep010000110111_0 : Blocks := edgeBlocks% "full/vectors/010000110111-E-0000.bin"
noncomputable def ep010000110111 : Blocks := ep010000110111_0
private theorem idp010000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011011.list =
    C ((2:ℤ)^118) * horner X vp010000110111.list + horner X ep010000110111.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000110111 : Branch 1 (-2155761639/4000000 : ℚ) vp01000011011 := by
  apply branch_checked idp010000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2155761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2157761639/2000000 : ℚ) by norm_num]
  exact coverp010000110111
theorem coverp01000011011 : Covers (-2155761639/4000000 : ℚ) vp01000011011 := join_branches bp010000110110 bp010000110111
private noncomputable def vp010000110101_0 : Blocks := edgeBlocks% "full/vectors/010000110101-V-0000.bin"
noncomputable def vp010000110101 : Blocks := vp010000110101_0
theorem coverp010000110101 : Covers (-2153761639/2000000 : ℚ) vp010000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000110100_0 : Blocks := edgeBlocks% "full/vectors/010000110100-V-0000.bin"
noncomputable def vp010000110100 : Blocks := vp010000110100_0
theorem coverp010000110100 : Covers (-2151761639/2000000 : ℚ) vp010000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011010_0 : Blocks := edgeBlocks% "full/vectors/01000011010-V-0000.bin"
noncomputable def vp01000011010 : Blocks := vp01000011010_0
private theorem bp010000110100 : Branch 0 (-2151761639/4000000 : ℚ) vp01000011010 := by
  apply branch_left_normalized (c:=vp010000110100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2151761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2151761639/2000000 : ℚ) by norm_num]
  exact coverp010000110100
private noncomputable def ep010000110101_0 : Blocks := edgeBlocks% "full/vectors/010000110101-E-0000.bin"
noncomputable def ep010000110101 : Blocks := ep010000110101_0
private theorem idp010000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011010.list =
    C ((2:ℤ)^117) * horner X vp010000110101.list + horner X ep010000110101.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000110101 : Branch 1 (-2151761639/4000000 : ℚ) vp01000011010 := by
  apply branch_checked idp010000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2151761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2153761639/2000000 : ℚ) by norm_num]
  exact coverp010000110101
theorem coverp01000011010 : Covers (-2151761639/4000000 : ℚ) vp01000011010 := join_branches bp010000110100 bp010000110101
private noncomputable def vp0100001101_0 : Blocks := edgeBlocks% "full/vectors/0100001101-V-0000.bin"
private noncomputable def vp0100001101_1 : Blocks := edgeBlocks% "full/vectors/0100001101-V-0001.bin"
noncomputable def vp0100001101 : Blocks := (Blocks.join vp0100001101_0 vp0100001101_1)
private theorem bp01000011010 : Branch 0 (-2151761639/8000000 : ℚ) vp0100001101 := by
  apply branch_left_normalized (c:=vp01000011010) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-2151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2151761639/4000000 : ℚ) by norm_num]
  exact coverp01000011010
private noncomputable def ep01000011011_0 : Blocks := edgeBlocks% "full/vectors/01000011011-E-0000.bin"
private noncomputable def ep01000011011_1 : Blocks := edgeBlocks% "full/vectors/01000011011-E-0001.bin"
noncomputable def ep01000011011 : Blocks := (Blocks.join ep01000011011_0 ep01000011011_1)
private theorem idp01000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001101.list =
    C ((2:ℤ)^217) * horner X vp01000011011.list + horner X ep01000011011.list := by
  exact edge_identity (B := (2:ℤ)^381) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000011011 : Branch 1 (-2151761639/8000000 : ℚ) vp0100001101 := by
  apply branch_checked idp01000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2155761639/4000000 : ℚ) by norm_num]
  exact coverp01000011011
theorem coverp0100001101 : Covers (-2151761639/8000000 : ℚ) vp0100001101 := join_branches bp01000011010 bp01000011011
private noncomputable def vp010000110011_0 : Blocks := edgeBlocks% "full/vectors/010000110011-V-0000.bin"
noncomputable def vp010000110011 : Blocks := vp010000110011_0
theorem coverp010000110011 : Covers (-2149761639/2000000 : ℚ) vp010000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000110010_0 : Blocks := edgeBlocks% "full/vectors/010000110010-V-0000.bin"
noncomputable def vp010000110010 : Blocks := vp010000110010_0
theorem coverp010000110010 : Covers (-2147761639/2000000 : ℚ) vp010000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011001_0 : Blocks := edgeBlocks% "full/vectors/01000011001-V-0000.bin"
noncomputable def vp01000011001 : Blocks := vp01000011001_0
private theorem bp010000110010 : Branch 0 (-2147761639/4000000 : ℚ) vp01000011001 := by
  apply branch_left_normalized (c:=vp010000110010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2147761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2147761639/2000000 : ℚ) by norm_num]
  exact coverp010000110010
private noncomputable def ep010000110011_0 : Blocks := edgeBlocks% "full/vectors/010000110011-E-0000.bin"
noncomputable def ep010000110011 : Blocks := ep010000110011_0
private theorem idp010000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011001.list =
    C ((2:ℤ)^116) * horner X vp010000110011.list + horner X ep010000110011.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000110011 : Branch 1 (-2147761639/4000000 : ℚ) vp01000011001 := by
  apply branch_checked idp010000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2147761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2149761639/2000000 : ℚ) by norm_num]
  exact coverp010000110011
theorem coverp01000011001 : Covers (-2147761639/4000000 : ℚ) vp01000011001 := join_branches bp010000110010 bp010000110011
private noncomputable def vp010000110001_0 : Blocks := edgeBlocks% "full/vectors/010000110001-V-0000.bin"
noncomputable def vp010000110001 : Blocks := vp010000110001_0
theorem coverp010000110001 : Covers (-2145761639/2000000 : ℚ) vp010000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000110000_0 : Blocks := edgeBlocks% "full/vectors/010000110000-V-0000.bin"
noncomputable def vp010000110000 : Blocks := vp010000110000_0
theorem coverp010000110000 : Covers (-2143761639/2000000 : ℚ) vp010000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000011000_0 : Blocks := edgeBlocks% "full/vectors/01000011000-V-0000.bin"
noncomputable def vp01000011000 : Blocks := vp01000011000_0
private theorem bp010000110000 : Branch 0 (-2143761639/4000000 : ℚ) vp01000011000 := by
  apply branch_left_normalized (c:=vp010000110000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2143761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2143761639/2000000 : ℚ) by norm_num]
  exact coverp010000110000
private noncomputable def ep010000110001_0 : Blocks := edgeBlocks% "full/vectors/010000110001-E-0000.bin"
noncomputable def ep010000110001 : Blocks := ep010000110001_0
private theorem idp010000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011000.list =
    C ((2:ℤ)^118) * horner X vp010000110001.list + horner X ep010000110001.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000110001 : Branch 1 (-2143761639/4000000 : ℚ) vp01000011000 := by
  apply branch_checked idp010000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2143761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2145761639/2000000 : ℚ) by norm_num]
  exact coverp010000110001
theorem coverp01000011000 : Covers (-2143761639/4000000 : ℚ) vp01000011000 := join_branches bp010000110000 bp010000110001
private noncomputable def vp0100001100_0 : Blocks := edgeBlocks% "full/vectors/0100001100-V-0000.bin"
private noncomputable def vp0100001100_1 : Blocks := edgeBlocks% "full/vectors/0100001100-V-0001.bin"
noncomputable def vp0100001100 : Blocks := (Blocks.join vp0100001100_0 vp0100001100_1)
private theorem bp01000011000 : Branch 0 (-2143761639/8000000 : ℚ) vp0100001100 := by
  apply branch_left_normalized (c:=vp01000011000) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-2143761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2143761639/4000000 : ℚ) by norm_num]
  exact coverp01000011000
private noncomputable def ep01000011001_0 : Blocks := edgeBlocks% "full/vectors/01000011001-E-0000.bin"
private noncomputable def ep01000011001_1 : Blocks := edgeBlocks% "full/vectors/01000011001-E-0001.bin"
noncomputable def ep01000011001 : Blocks := (Blocks.join ep01000011001_0 ep01000011001_1)
private theorem idp01000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001100.list =
    C ((2:ℤ)^215) * horner X vp01000011001.list + horner X ep01000011001.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000011001 : Branch 1 (-2143761639/8000000 : ℚ) vp0100001100 := by
  apply branch_checked idp01000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2143761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2147761639/4000000 : ℚ) by norm_num]
  exact coverp01000011001
theorem coverp0100001100 : Covers (-2143761639/8000000 : ℚ) vp0100001100 := join_branches bp01000011000 bp01000011001
private noncomputable def vp010000110_0 : Blocks := edgeBlocks% "full/vectors/010000110-V-0000.bin"
private noncomputable def vp010000110_1 : Blocks := edgeBlocks% "full/vectors/010000110-V-0001.bin"
private noncomputable def vp010000110_2 : Blocks := edgeBlocks% "full/vectors/010000110-V-0002.bin"
noncomputable def vp010000110 : Blocks := (Blocks.join vp010000110_0 (Blocks.join vp010000110_1 vp010000110_2))
private theorem bp0100001100 : Branch 0 (-2143761639/16000000 : ℚ) vp010000110 := by
  apply branch_left_normalized (c:=vp0100001100) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-2143761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2143761639/8000000 : ℚ) by norm_num]
  exact coverp0100001100
private noncomputable def ep0100001101_0 : Blocks := edgeBlocks% "full/vectors/0100001101-E-0000.bin"
private noncomputable def ep0100001101_1 : Blocks := edgeBlocks% "full/vectors/0100001101-E-0001.bin"
private noncomputable def ep0100001101_2 : Blocks := edgeBlocks% "full/vectors/0100001101-E-0002.bin"
noncomputable def ep0100001101 : Blocks := (Blocks.join ep0100001101_0 (Blocks.join ep0100001101_1 ep0100001101_2))
private theorem idp0100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000110.list =
    C ((2:ℤ)^405) * horner X vp0100001101.list + horner X ep0100001101.list := by
  exact edge_identity (B := (2:ℤ)^639) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100001101 : Branch 1 (-2143761639/16000000 : ℚ) vp010000110 := by
  apply branch_checked idp0100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2143761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2151761639/8000000 : ℚ) by norm_num]
  exact coverp0100001101
theorem coverp010000110 : Covers (-2143761639/16000000 : ℚ) vp010000110 := join_branches bp0100001100 bp0100001101
private noncomputable def vp01000011_0 : Blocks := edgeBlocks% "full/vectors/01000011-V-0000.bin"
private noncomputable def vp01000011_1 : Blocks := edgeBlocks% "full/vectors/01000011-V-0001.bin"
private noncomputable def vp01000011_2 : Blocks := edgeBlocks% "full/vectors/01000011-V-0002.bin"
private noncomputable def vp01000011_3 : Blocks := edgeBlocks% "full/vectors/01000011-V-0003.bin"
private noncomputable def vp01000011_4 : Blocks := edgeBlocks% "full/vectors/01000011-V-0004.bin"
private noncomputable def vp01000011_5 : Blocks := edgeBlocks% "full/vectors/01000011-V-0005.bin"
noncomputable def vp01000011 : Blocks := (Blocks.join (Blocks.join vp01000011_0 (Blocks.join vp01000011_1 vp01000011_2)) (Blocks.join vp01000011_3 (Blocks.join vp01000011_4 vp01000011_5)))
private theorem bp010000110 : Branch 0 (-2143761639/32000000 : ℚ) vp01000011 := by
  apply branch_left_normalized (c:=vp010000110) (k:=0) (m:=359) (by decide +kernel)
  rw [show 2*(-2143761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2143761639/16000000 : ℚ) by norm_num]
  exact coverp010000110
private noncomputable def ep010000111_0 : Blocks := edgeBlocks% "full/vectors/010000111-E-0000.bin"
private noncomputable def ep010000111_1 : Blocks := edgeBlocks% "full/vectors/010000111-E-0001.bin"
private noncomputable def ep010000111_2 : Blocks := edgeBlocks% "full/vectors/010000111-E-0002.bin"
private noncomputable def ep010000111_3 : Blocks := edgeBlocks% "full/vectors/010000111-E-0003.bin"
private noncomputable def ep010000111_4 : Blocks := edgeBlocks% "full/vectors/010000111-E-0004.bin"
private noncomputable def ep010000111_5 : Blocks := edgeBlocks% "full/vectors/010000111-E-0005.bin"
noncomputable def ep010000111 : Blocks := (Blocks.join (Blocks.join ep010000111_0 (Blocks.join ep010000111_1 ep010000111_2)) (Blocks.join ep010000111_3 (Blocks.join ep010000111_4 ep010000111_5)))
private theorem idp010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000011.list =
    C ((2:ℤ)^792) * horner X vp010000111.list + horner X ep010000111.list := by
  exact edge_identity (B := (2:ℤ)^1153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000111 : Branch 1 (-2143761639/32000000 : ℚ) vp01000011 := by
  apply branch_checked idp010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2143761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2159761639/16000000 : ℚ) by norm_num]
  exact coverp010000111
theorem coverp01000011 : Covers (-2143761639/32000000 : ℚ) vp01000011 := join_branches bp010000110 bp010000111
private noncomputable def vp010000101111_0 : Blocks := edgeBlocks% "full/vectors/010000101111-V-0000.bin"
noncomputable def vp010000101111 : Blocks := vp010000101111_0
theorem coverp010000101111 : Covers (-2141761639/2000000 : ℚ) vp010000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000101110_0 : Blocks := edgeBlocks% "full/vectors/010000101110-V-0000.bin"
noncomputable def vp010000101110 : Blocks := vp010000101110_0
theorem coverp010000101110 : Covers (-2139761639/2000000 : ℚ) vp010000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010111_0 : Blocks := edgeBlocks% "full/vectors/01000010111-V-0000.bin"
noncomputable def vp01000010111 : Blocks := vp01000010111_0
private theorem bp010000101110 : Branch 0 (-2139761639/4000000 : ℚ) vp01000010111 := by
  apply branch_left_normalized (c:=vp010000101110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2139761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2139761639/2000000 : ℚ) by norm_num]
  exact coverp010000101110
private noncomputable def ep010000101111_0 : Blocks := edgeBlocks% "full/vectors/010000101111-E-0000.bin"
noncomputable def ep010000101111 : Blocks := ep010000101111_0
private theorem idp010000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010111.list =
    C ((2:ℤ)^120) * horner X vp010000101111.list + horner X ep010000101111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000101111 : Branch 1 (-2139761639/4000000 : ℚ) vp01000010111 := by
  apply branch_checked idp010000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2139761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2141761639/2000000 : ℚ) by norm_num]
  exact coverp010000101111
theorem coverp01000010111 : Covers (-2139761639/4000000 : ℚ) vp01000010111 := join_branches bp010000101110 bp010000101111
private noncomputable def vp010000101101_0 : Blocks := edgeBlocks% "full/vectors/010000101101-V-0000.bin"
noncomputable def vp010000101101 : Blocks := vp010000101101_0
theorem coverp010000101101 : Covers (-2137761639/2000000 : ℚ) vp010000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000101100_0 : Blocks := edgeBlocks% "full/vectors/010000101100-V-0000.bin"
noncomputable def vp010000101100 : Blocks := vp010000101100_0
theorem coverp010000101100 : Covers (-2135761639/2000000 : ℚ) vp010000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010110_0 : Blocks := edgeBlocks% "full/vectors/01000010110-V-0000.bin"
noncomputable def vp01000010110 : Blocks := vp01000010110_0
private theorem bp010000101100 : Branch 0 (-2135761639/4000000 : ℚ) vp01000010110 := by
  apply branch_left_normalized (c:=vp010000101100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2135761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2135761639/2000000 : ℚ) by norm_num]
  exact coverp010000101100
private noncomputable def ep010000101101_0 : Blocks := edgeBlocks% "full/vectors/010000101101-E-0000.bin"
noncomputable def ep010000101101 : Blocks := ep010000101101_0
private theorem idp010000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010110.list =
    C ((2:ℤ)^118) * horner X vp010000101101.list + horner X ep010000101101.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000101101 : Branch 1 (-2135761639/4000000 : ℚ) vp01000010110 := by
  apply branch_checked idp010000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2135761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2137761639/2000000 : ℚ) by norm_num]
  exact coverp010000101101
theorem coverp01000010110 : Covers (-2135761639/4000000 : ℚ) vp01000010110 := join_branches bp010000101100 bp010000101101
private noncomputable def vp0100001011_0 : Blocks := edgeBlocks% "full/vectors/0100001011-V-0000.bin"
private noncomputable def vp0100001011_1 : Blocks := edgeBlocks% "full/vectors/0100001011-V-0001.bin"
noncomputable def vp0100001011 : Blocks := (Blocks.join vp0100001011_0 vp0100001011_1)
private theorem bp01000010110 : Branch 0 (-2135761639/8000000 : ℚ) vp0100001011 := by
  apply branch_left_normalized (c:=vp01000010110) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2135761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2135761639/4000000 : ℚ) by norm_num]
  exact coverp01000010110
private noncomputable def ep01000010111_0 : Blocks := edgeBlocks% "full/vectors/01000010111-E-0000.bin"
private noncomputable def ep01000010111_1 : Blocks := edgeBlocks% "full/vectors/01000010111-E-0001.bin"
noncomputable def ep01000010111 : Blocks := (Blocks.join ep01000010111_0 ep01000010111_1)
private theorem idp01000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001011.list =
    C ((2:ℤ)^213) * horner X vp01000010111.list + horner X ep01000010111.list := by
  exact edge_identity (B := (2:ℤ)^382) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000010111 : Branch 1 (-2135761639/8000000 : ℚ) vp0100001011 := by
  apply branch_checked idp01000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2135761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2139761639/4000000 : ℚ) by norm_num]
  exact coverp01000010111
theorem coverp0100001011 : Covers (-2135761639/8000000 : ℚ) vp0100001011 := join_branches bp01000010110 bp01000010111
private noncomputable def vp010000101011_0 : Blocks := edgeBlocks% "full/vectors/010000101011-V-0000.bin"
noncomputable def vp010000101011 : Blocks := vp010000101011_0
theorem coverp010000101011 : Covers (-2133761639/2000000 : ℚ) vp010000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000101010_0 : Blocks := edgeBlocks% "full/vectors/010000101010-V-0000.bin"
noncomputable def vp010000101010 : Blocks := vp010000101010_0
theorem coverp010000101010 : Covers (-2131761639/2000000 : ℚ) vp010000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010101_0 : Blocks := edgeBlocks% "full/vectors/01000010101-V-0000.bin"
noncomputable def vp01000010101 : Blocks := vp01000010101_0
private theorem bp010000101010 : Branch 0 (-2131761639/4000000 : ℚ) vp01000010101 := by
  apply branch_left_normalized (c:=vp010000101010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2131761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2131761639/2000000 : ℚ) by norm_num]
  exact coverp010000101010
private noncomputable def ep010000101011_0 : Blocks := edgeBlocks% "full/vectors/010000101011-E-0000.bin"
noncomputable def ep010000101011 : Blocks := ep010000101011_0
private theorem idp010000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010101.list =
    C ((2:ℤ)^118) * horner X vp010000101011.list + horner X ep010000101011.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000101011 : Branch 1 (-2131761639/4000000 : ℚ) vp01000010101 := by
  apply branch_checked idp010000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2131761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2133761639/2000000 : ℚ) by norm_num]
  exact coverp010000101011
theorem coverp01000010101 : Covers (-2131761639/4000000 : ℚ) vp01000010101 := join_branches bp010000101010 bp010000101011
private noncomputable def vp010000101001_0 : Blocks := edgeBlocks% "full/vectors/010000101001-V-0000.bin"
noncomputable def vp010000101001 : Blocks := vp010000101001_0
theorem coverp010000101001 : Covers (-2129761639/2000000 : ℚ) vp010000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000101000_0 : Blocks := edgeBlocks% "full/vectors/010000101000-V-0000.bin"
noncomputable def vp010000101000 : Blocks := vp010000101000_0
theorem coverp010000101000 : Covers (-2127761639/2000000 : ℚ) vp010000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010100_0 : Blocks := edgeBlocks% "full/vectors/01000010100-V-0000.bin"
noncomputable def vp01000010100 : Blocks := vp01000010100_0
private theorem bp010000101000 : Branch 0 (-2127761639/4000000 : ℚ) vp01000010100 := by
  apply branch_left_normalized (c:=vp010000101000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2127761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2127761639/2000000 : ℚ) by norm_num]
  exact coverp010000101000
private noncomputable def ep010000101001_0 : Blocks := edgeBlocks% "full/vectors/010000101001-E-0000.bin"
noncomputable def ep010000101001 : Blocks := ep010000101001_0
private theorem idp010000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010100.list =
    C ((2:ℤ)^119) * horner X vp010000101001.list + horner X ep010000101001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000101001 : Branch 1 (-2127761639/4000000 : ℚ) vp01000010100 := by
  apply branch_checked idp010000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2127761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2129761639/2000000 : ℚ) by norm_num]
  exact coverp010000101001
theorem coverp01000010100 : Covers (-2127761639/4000000 : ℚ) vp01000010100 := join_branches bp010000101000 bp010000101001
private noncomputable def vp0100001010_0 : Blocks := edgeBlocks% "full/vectors/0100001010-V-0000.bin"
private noncomputable def vp0100001010_1 : Blocks := edgeBlocks% "full/vectors/0100001010-V-0001.bin"
noncomputable def vp0100001010 : Blocks := (Blocks.join vp0100001010_0 vp0100001010_1)
private theorem bp01000010100 : Branch 0 (-2127761639/8000000 : ℚ) vp0100001010 := by
  apply branch_left_normalized (c:=vp01000010100) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2127761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2127761639/4000000 : ℚ) by norm_num]
  exact coverp01000010100
private noncomputable def ep01000010101_0 : Blocks := edgeBlocks% "full/vectors/01000010101-E-0000.bin"
private noncomputable def ep01000010101_1 : Blocks := edgeBlocks% "full/vectors/01000010101-E-0001.bin"
noncomputable def ep01000010101 : Blocks := (Blocks.join ep01000010101_0 ep01000010101_1)
private theorem idp01000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001010.list =
    C ((2:ℤ)^217) * horner X vp01000010101.list + horner X ep01000010101.list := by
  exact edge_identity (B := (2:ℤ)^384) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000010101 : Branch 1 (-2127761639/8000000 : ℚ) vp0100001010 := by
  apply branch_checked idp01000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2127761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2131761639/4000000 : ℚ) by norm_num]
  exact coverp01000010101
theorem coverp0100001010 : Covers (-2127761639/8000000 : ℚ) vp0100001010 := join_branches bp01000010100 bp01000010101
private noncomputable def vp010000101_0 : Blocks := edgeBlocks% "full/vectors/010000101-V-0000.bin"
private noncomputable def vp010000101_1 : Blocks := edgeBlocks% "full/vectors/010000101-V-0001.bin"
private noncomputable def vp010000101_2 : Blocks := edgeBlocks% "full/vectors/010000101-V-0002.bin"
noncomputable def vp010000101 : Blocks := (Blocks.join vp010000101_0 (Blocks.join vp010000101_1 vp010000101_2))
private theorem bp0100001010 : Branch 0 (-2127761639/16000000 : ℚ) vp010000101 := by
  apply branch_left_normalized (c:=vp0100001010) (k:=0) (m:=192) (by decide +kernel)
  rw [show 2*(-2127761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2127761639/8000000 : ℚ) by norm_num]
  exact coverp0100001010
private noncomputable def ep0100001011_0 : Blocks := edgeBlocks% "full/vectors/0100001011-E-0000.bin"
private noncomputable def ep0100001011_1 : Blocks := edgeBlocks% "full/vectors/0100001011-E-0001.bin"
private noncomputable def ep0100001011_2 : Blocks := edgeBlocks% "full/vectors/0100001011-E-0002.bin"
noncomputable def ep0100001011 : Blocks := (Blocks.join ep0100001011_0 (Blocks.join ep0100001011_1 ep0100001011_2))
private theorem idp0100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000101.list =
    C ((2:ℤ)^409) * horner X vp0100001011.list + horner X ep0100001011.list := by
  exact edge_identity (B := (2:ℤ)^643) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100001011 : Branch 1 (-2127761639/16000000 : ℚ) vp010000101 := by
  apply branch_checked idp0100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2127761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2135761639/8000000 : ℚ) by norm_num]
  exact coverp0100001011
theorem coverp010000101 : Covers (-2127761639/16000000 : ℚ) vp010000101 := join_branches bp0100001010 bp0100001011
private noncomputable def vp010000100111_0 : Blocks := edgeBlocks% "full/vectors/010000100111-V-0000.bin"
noncomputable def vp010000100111 : Blocks := vp010000100111_0
theorem coverp010000100111 : Covers (-2125761639/2000000 : ℚ) vp010000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000100110_0 : Blocks := edgeBlocks% "full/vectors/010000100110-V-0000.bin"
noncomputable def vp010000100110 : Blocks := vp010000100110_0
theorem coverp010000100110 : Covers (-2123761639/2000000 : ℚ) vp010000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010011_0 : Blocks := edgeBlocks% "full/vectors/01000010011-V-0000.bin"
noncomputable def vp01000010011 : Blocks := vp01000010011_0
private theorem bp010000100110 : Branch 0 (-2123761639/4000000 : ℚ) vp01000010011 := by
  apply branch_left_normalized (c:=vp010000100110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2123761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2123761639/2000000 : ℚ) by norm_num]
  exact coverp010000100110
private noncomputable def ep010000100111_0 : Blocks := edgeBlocks% "full/vectors/010000100111-E-0000.bin"
noncomputable def ep010000100111 : Blocks := ep010000100111_0
private theorem idp010000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010011.list =
    C ((2:ℤ)^119) * horner X vp010000100111.list + horner X ep010000100111.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000100111 : Branch 1 (-2123761639/4000000 : ℚ) vp01000010011 := by
  apply branch_checked idp010000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2123761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2125761639/2000000 : ℚ) by norm_num]
  exact coverp010000100111
theorem coverp01000010011 : Covers (-2123761639/4000000 : ℚ) vp01000010011 := join_branches bp010000100110 bp010000100111
private noncomputable def vp010000100101_0 : Blocks := edgeBlocks% "full/vectors/010000100101-V-0000.bin"
noncomputable def vp010000100101 : Blocks := vp010000100101_0
theorem coverp010000100101 : Covers (-2121761639/2000000 : ℚ) vp010000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000100100_0 : Blocks := edgeBlocks% "full/vectors/010000100100-V-0000.bin"
noncomputable def vp010000100100 : Blocks := vp010000100100_0
theorem coverp010000100100 : Covers (-2119761639/2000000 : ℚ) vp010000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010010_0 : Blocks := edgeBlocks% "full/vectors/01000010010-V-0000.bin"
noncomputable def vp01000010010 : Blocks := vp01000010010_0
private theorem bp010000100100 : Branch 0 (-2119761639/4000000 : ℚ) vp01000010010 := by
  apply branch_left_normalized (c:=vp010000100100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2119761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2119761639/2000000 : ℚ) by norm_num]
  exact coverp010000100100
private noncomputable def ep010000100101_0 : Blocks := edgeBlocks% "full/vectors/010000100101-E-0000.bin"
noncomputable def ep010000100101 : Blocks := ep010000100101_0
private theorem idp010000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010010.list =
    C ((2:ℤ)^119) * horner X vp010000100101.list + horner X ep010000100101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000100101 : Branch 1 (-2119761639/4000000 : ℚ) vp01000010010 := by
  apply branch_checked idp010000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2119761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2121761639/2000000 : ℚ) by norm_num]
  exact coverp010000100101
theorem coverp01000010010 : Covers (-2119761639/4000000 : ℚ) vp01000010010 := join_branches bp010000100100 bp010000100101
private noncomputable def vp0100001001_0 : Blocks := edgeBlocks% "full/vectors/0100001001-V-0000.bin"
private noncomputable def vp0100001001_1 : Blocks := edgeBlocks% "full/vectors/0100001001-V-0001.bin"
noncomputable def vp0100001001 : Blocks := (Blocks.join vp0100001001_0 vp0100001001_1)
private theorem bp01000010010 : Branch 0 (-2119761639/8000000 : ℚ) vp0100001001 := by
  apply branch_left_normalized (c:=vp01000010010) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2119761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2119761639/4000000 : ℚ) by norm_num]
  exact coverp01000010010
private noncomputable def ep01000010011_0 : Blocks := edgeBlocks% "full/vectors/01000010011-E-0000.bin"
private noncomputable def ep01000010011_1 : Blocks := edgeBlocks% "full/vectors/01000010011-E-0001.bin"
noncomputable def ep01000010011 : Blocks := (Blocks.join ep01000010011_0 ep01000010011_1)
private theorem idp01000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001001.list =
    C ((2:ℤ)^216) * horner X vp01000010011.list + horner X ep01000010011.list := by
  exact edge_identity (B := (2:ℤ)^385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000010011 : Branch 1 (-2119761639/8000000 : ℚ) vp0100001001 := by
  apply branch_checked idp01000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2119761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2123761639/4000000 : ℚ) by norm_num]
  exact coverp01000010011
theorem coverp0100001001 : Covers (-2119761639/8000000 : ℚ) vp0100001001 := join_branches bp01000010010 bp01000010011
private noncomputable def vp010000100011_0 : Blocks := edgeBlocks% "full/vectors/010000100011-V-0000.bin"
noncomputable def vp010000100011 : Blocks := vp010000100011_0
theorem coverp010000100011 : Covers (-2117761639/2000000 : ℚ) vp010000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000100010_0 : Blocks := edgeBlocks% "full/vectors/010000100010-V-0000.bin"
noncomputable def vp010000100010 : Blocks := vp010000100010_0
theorem coverp010000100010 : Covers (-2115761639/2000000 : ℚ) vp010000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010001_0 : Blocks := edgeBlocks% "full/vectors/01000010001-V-0000.bin"
noncomputable def vp01000010001 : Blocks := vp01000010001_0
private theorem bp010000100010 : Branch 0 (-2115761639/4000000 : ℚ) vp01000010001 := by
  apply branch_left_normalized (c:=vp010000100010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2115761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2115761639/2000000 : ℚ) by norm_num]
  exact coverp010000100010
private noncomputable def ep010000100011_0 : Blocks := edgeBlocks% "full/vectors/010000100011-E-0000.bin"
noncomputable def ep010000100011 : Blocks := ep010000100011_0
private theorem idp010000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010001.list =
    C ((2:ℤ)^119) * horner X vp010000100011.list + horner X ep010000100011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000100011 : Branch 1 (-2115761639/4000000 : ℚ) vp01000010001 := by
  apply branch_checked idp010000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2115761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2117761639/2000000 : ℚ) by norm_num]
  exact coverp010000100011
theorem coverp01000010001 : Covers (-2115761639/4000000 : ℚ) vp01000010001 := join_branches bp010000100010 bp010000100011
private noncomputable def vp010000100001_0 : Blocks := edgeBlocks% "full/vectors/010000100001-V-0000.bin"
noncomputable def vp010000100001 : Blocks := vp010000100001_0
theorem coverp010000100001 : Covers (-2113761639/2000000 : ℚ) vp010000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000100000_0 : Blocks := edgeBlocks% "full/vectors/010000100000-V-0000.bin"
noncomputable def vp010000100000 : Blocks := vp010000100000_0
theorem coverp010000100000 : Covers (-2111761639/2000000 : ℚ) vp010000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000010000_0 : Blocks := edgeBlocks% "full/vectors/01000010000-V-0000.bin"
noncomputable def vp01000010000 : Blocks := vp01000010000_0
private theorem bp010000100000 : Branch 0 (-2111761639/4000000 : ℚ) vp01000010000 := by
  apply branch_left_normalized (c:=vp010000100000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2111761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2111761639/2000000 : ℚ) by norm_num]
  exact coverp010000100000
private noncomputable def ep010000100001_0 : Blocks := edgeBlocks% "full/vectors/010000100001-E-0000.bin"
noncomputable def ep010000100001 : Blocks := ep010000100001_0
private theorem idp010000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010000.list =
    C ((2:ℤ)^119) * horner X vp010000100001.list + horner X ep010000100001.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000100001 : Branch 1 (-2111761639/4000000 : ℚ) vp01000010000 := by
  apply branch_checked idp010000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2111761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2113761639/2000000 : ℚ) by norm_num]
  exact coverp010000100001
theorem coverp01000010000 : Covers (-2111761639/4000000 : ℚ) vp01000010000 := join_branches bp010000100000 bp010000100001
private noncomputable def vp0100001000_0 : Blocks := edgeBlocks% "full/vectors/0100001000-V-0000.bin"
private noncomputable def vp0100001000_1 : Blocks := edgeBlocks% "full/vectors/0100001000-V-0001.bin"
noncomputable def vp0100001000 : Blocks := (Blocks.join vp0100001000_0 vp0100001000_1)
private theorem bp01000010000 : Branch 0 (-2111761639/8000000 : ℚ) vp0100001000 := by
  apply branch_left_normalized (c:=vp01000010000) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-2111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2111761639/4000000 : ℚ) by norm_num]
  exact coverp01000010000
private noncomputable def ep01000010001_0 : Blocks := edgeBlocks% "full/vectors/01000010001-E-0000.bin"
private noncomputable def ep01000010001_1 : Blocks := edgeBlocks% "full/vectors/01000010001-E-0001.bin"
noncomputable def ep01000010001 : Blocks := (Blocks.join ep01000010001_0 ep01000010001_1)
private theorem idp01000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001000.list =
    C ((2:ℤ)^217) * horner X vp01000010001.list + horner X ep01000010001.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000010001 : Branch 1 (-2111761639/8000000 : ℚ) vp0100001000 := by
  apply branch_checked idp01000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2115761639/4000000 : ℚ) by norm_num]
  exact coverp01000010001
theorem coverp0100001000 : Covers (-2111761639/8000000 : ℚ) vp0100001000 := join_branches bp01000010000 bp01000010001
private noncomputable def vp010000100_0 : Blocks := edgeBlocks% "full/vectors/010000100-V-0000.bin"
private noncomputable def vp010000100_1 : Blocks := edgeBlocks% "full/vectors/010000100-V-0001.bin"
private noncomputable def vp010000100_2 : Blocks := edgeBlocks% "full/vectors/010000100-V-0002.bin"
noncomputable def vp010000100 : Blocks := (Blocks.join vp010000100_0 (Blocks.join vp010000100_1 vp010000100_2))
private theorem bp0100001000 : Branch 0 (-2111761639/16000000 : ℚ) vp010000100 := by
  apply branch_left_normalized (c:=vp0100001000) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-2111761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2111761639/8000000 : ℚ) by norm_num]
  exact coverp0100001000
private noncomputable def ep0100001001_0 : Blocks := edgeBlocks% "full/vectors/0100001001-E-0000.bin"
private noncomputable def ep0100001001_1 : Blocks := edgeBlocks% "full/vectors/0100001001-E-0001.bin"
private noncomputable def ep0100001001_2 : Blocks := edgeBlocks% "full/vectors/0100001001-E-0002.bin"
noncomputable def ep0100001001 : Blocks := (Blocks.join ep0100001001_0 (Blocks.join ep0100001001_1 ep0100001001_2))
private theorem idp0100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000100.list =
    C ((2:ℤ)^410) * horner X vp0100001001.list + horner X ep0100001001.list := by
  exact edge_identity (B := (2:ℤ)^646) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100001001 : Branch 1 (-2111761639/16000000 : ℚ) vp010000100 := by
  apply branch_checked idp0100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2111761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2119761639/8000000 : ℚ) by norm_num]
  exact coverp0100001001
theorem coverp010000100 : Covers (-2111761639/16000000 : ℚ) vp010000100 := join_branches bp0100001000 bp0100001001
private noncomputable def vp01000010_0 : Blocks := edgeBlocks% "full/vectors/01000010-V-0000.bin"
private noncomputable def vp01000010_1 : Blocks := edgeBlocks% "full/vectors/01000010-V-0001.bin"
private noncomputable def vp01000010_2 : Blocks := edgeBlocks% "full/vectors/01000010-V-0002.bin"
private noncomputable def vp01000010_3 : Blocks := edgeBlocks% "full/vectors/01000010-V-0003.bin"
private noncomputable def vp01000010_4 : Blocks := edgeBlocks% "full/vectors/01000010-V-0004.bin"
private noncomputable def vp01000010_5 : Blocks := edgeBlocks% "full/vectors/01000010-V-0005.bin"
noncomputable def vp01000010 : Blocks := (Blocks.join (Blocks.join vp01000010_0 (Blocks.join vp01000010_1 vp01000010_2)) (Blocks.join vp01000010_3 (Blocks.join vp01000010_4 vp01000010_5)))
private theorem bp010000100 : Branch 0 (-2111761639/32000000 : ℚ) vp01000010 := by
  apply branch_left_normalized (c:=vp010000100) (k:=0) (m:=363) (by decide +kernel)
  rw [show 2*(-2111761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2111761639/16000000 : ℚ) by norm_num]
  exact coverp010000100
private noncomputable def ep010000101_0 : Blocks := edgeBlocks% "full/vectors/010000101-E-0000.bin"
private noncomputable def ep010000101_1 : Blocks := edgeBlocks% "full/vectors/010000101-E-0001.bin"
private noncomputable def ep010000101_2 : Blocks := edgeBlocks% "full/vectors/010000101-E-0002.bin"
private noncomputable def ep010000101_3 : Blocks := edgeBlocks% "full/vectors/010000101-E-0003.bin"
private noncomputable def ep010000101_4 : Blocks := edgeBlocks% "full/vectors/010000101-E-0004.bin"
private noncomputable def ep010000101_5 : Blocks := edgeBlocks% "full/vectors/010000101-E-0005.bin"
noncomputable def ep010000101 : Blocks := (Blocks.join (Blocks.join ep010000101_0 (Blocks.join ep010000101_1 ep010000101_2)) (Blocks.join ep010000101_3 (Blocks.join ep010000101_4 ep010000101_5)))
private theorem idp010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000010.list =
    C ((2:ℤ)^794) * horner X vp010000101.list + horner X ep010000101.list := by
  exact edge_identity (B := (2:ℤ)^1164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000101 : Branch 1 (-2111761639/32000000 : ℚ) vp01000010 := by
  apply branch_checked idp010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2111761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2127761639/16000000 : ℚ) by norm_num]
  exact coverp010000101
theorem coverp01000010 : Covers (-2111761639/32000000 : ℚ) vp01000010 := join_branches bp010000100 bp010000101
private noncomputable def vp0100001_0 : Blocks := edgeBlocks% "full/vectors/0100001-V-0000.bin"
private noncomputable def vp0100001_1 : Blocks := edgeBlocks% "full/vectors/0100001-V-0001.bin"
private noncomputable def vp0100001_2 : Blocks := edgeBlocks% "full/vectors/0100001-V-0002.bin"
private noncomputable def vp0100001_3 : Blocks := edgeBlocks% "full/vectors/0100001-V-0003.bin"
private noncomputable def vp0100001_4 : Blocks := edgeBlocks% "full/vectors/0100001-V-0004.bin"
private noncomputable def vp0100001_5 : Blocks := edgeBlocks% "full/vectors/0100001-V-0005.bin"
private noncomputable def vp0100001_6 : Blocks := edgeBlocks% "full/vectors/0100001-V-0006.bin"
private noncomputable def vp0100001_7 : Blocks := edgeBlocks% "full/vectors/0100001-V-0007.bin"
private noncomputable def vp0100001_8 : Blocks := edgeBlocks% "full/vectors/0100001-V-0008.bin"
private noncomputable def vp0100001_9 : Blocks := edgeBlocks% "full/vectors/0100001-V-0009.bin"
private noncomputable def vp0100001_10 : Blocks := edgeBlocks% "full/vectors/0100001-V-0010.bin"
noncomputable def vp0100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100001_0 vp0100001_1) (Blocks.join vp0100001_2 (Blocks.join vp0100001_3 vp0100001_4))) (Blocks.join (Blocks.join vp0100001_5 (Blocks.join vp0100001_6 vp0100001_7)) (Blocks.join vp0100001_8 (Blocks.join vp0100001_9 vp0100001_10))))
private theorem bp01000010 : Branch 0 (-2111761639/64000000 : ℚ) vp0100001 := by
  apply branch_left_normalized (c:=vp01000010) (k:=0) (m:=700) (by decide +kernel)
  rw [show 2*(-2111761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2111761639/32000000 : ℚ) by norm_num]
  exact coverp01000010
private noncomputable def ep01000011_0 : Blocks := edgeBlocks% "full/vectors/01000011-E-0000.bin"
private noncomputable def ep01000011_1 : Blocks := edgeBlocks% "full/vectors/01000011-E-0001.bin"
private noncomputable def ep01000011_2 : Blocks := edgeBlocks% "full/vectors/01000011-E-0002.bin"
private noncomputable def ep01000011_3 : Blocks := edgeBlocks% "full/vectors/01000011-E-0003.bin"
private noncomputable def ep01000011_4 : Blocks := edgeBlocks% "full/vectors/01000011-E-0004.bin"
private noncomputable def ep01000011_5 : Blocks := edgeBlocks% "full/vectors/01000011-E-0005.bin"
private noncomputable def ep01000011_6 : Blocks := edgeBlocks% "full/vectors/01000011-E-0006.bin"
private noncomputable def ep01000011_7 : Blocks := edgeBlocks% "full/vectors/01000011-E-0007.bin"
private noncomputable def ep01000011_8 : Blocks := edgeBlocks% "full/vectors/01000011-E-0008.bin"
private noncomputable def ep01000011_9 : Blocks := edgeBlocks% "full/vectors/01000011-E-0009.bin"
private noncomputable def ep01000011_10 : Blocks := edgeBlocks% "full/vectors/01000011-E-0010.bin"
noncomputable def ep01000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01000011_0 ep01000011_1) (Blocks.join ep01000011_2 (Blocks.join ep01000011_3 ep01000011_4))) (Blocks.join (Blocks.join ep01000011_5 (Blocks.join ep01000011_6 ep01000011_7)) (Blocks.join ep01000011_8 (Blocks.join ep01000011_9 ep01000011_10))))
private theorem idp01000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100001.list =
    C ((2:ℤ)^1552) * horner X vp01000011.list + horner X ep01000011.list := by
  exact edge_identity (B := (2:ℤ)^2188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000011 : Branch 1 (-2111761639/64000000 : ℚ) vp0100001 := by
  apply branch_checked idp01000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2111761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2143761639/32000000 : ℚ) by norm_num]
  exact coverp01000011
theorem coverp0100001 : Covers (-2111761639/64000000 : ℚ) vp0100001 := join_branches bp01000010 bp01000011
private noncomputable def vp010000011111_0 : Blocks := edgeBlocks% "full/vectors/010000011111-V-0000.bin"
noncomputable def vp010000011111 : Blocks := vp010000011111_0
theorem coverp010000011111 : Covers (-2109761639/2000000 : ℚ) vp010000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000011110_0 : Blocks := edgeBlocks% "full/vectors/010000011110-V-0000.bin"
noncomputable def vp010000011110 : Blocks := vp010000011110_0
theorem coverp010000011110 : Covers (-2107761639/2000000 : ℚ) vp010000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001111_0 : Blocks := edgeBlocks% "full/vectors/01000001111-V-0000.bin"
noncomputable def vp01000001111 : Blocks := vp01000001111_0
private theorem bp010000011110 : Branch 0 (-2107761639/4000000 : ℚ) vp01000001111 := by
  apply branch_left_normalized (c:=vp010000011110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2107761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2107761639/2000000 : ℚ) by norm_num]
  exact coverp010000011110
private noncomputable def ep010000011111_0 : Blocks := edgeBlocks% "full/vectors/010000011111-E-0000.bin"
noncomputable def ep010000011111 : Blocks := ep010000011111_0
private theorem idp010000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001111.list =
    C ((2:ℤ)^120) * horner X vp010000011111.list + horner X ep010000011111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000011111 : Branch 1 (-2107761639/4000000 : ℚ) vp01000001111 := by
  apply branch_checked idp010000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2107761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2109761639/2000000 : ℚ) by norm_num]
  exact coverp010000011111
theorem coverp01000001111 : Covers (-2107761639/4000000 : ℚ) vp01000001111 := join_branches bp010000011110 bp010000011111
private noncomputable def vp010000011101_0 : Blocks := edgeBlocks% "full/vectors/010000011101-V-0000.bin"
noncomputable def vp010000011101 : Blocks := vp010000011101_0
theorem coverp010000011101 : Covers (-2105761639/2000000 : ℚ) vp010000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000011100_0 : Blocks := edgeBlocks% "full/vectors/010000011100-V-0000.bin"
noncomputable def vp010000011100 : Blocks := vp010000011100_0
theorem coverp010000011100 : Covers (-2103761639/2000000 : ℚ) vp010000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001110_0 : Blocks := edgeBlocks% "full/vectors/01000001110-V-0000.bin"
noncomputable def vp01000001110 : Blocks := vp01000001110_0
private theorem bp010000011100 : Branch 0 (-2103761639/4000000 : ℚ) vp01000001110 := by
  apply branch_left_normalized (c:=vp010000011100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2103761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2103761639/2000000 : ℚ) by norm_num]
  exact coverp010000011100
private noncomputable def ep010000011101_0 : Blocks := edgeBlocks% "full/vectors/010000011101-E-0000.bin"
noncomputable def ep010000011101 : Blocks := ep010000011101_0
private theorem idp010000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001110.list =
    C ((2:ℤ)^119) * horner X vp010000011101.list + horner X ep010000011101.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000011101 : Branch 1 (-2103761639/4000000 : ℚ) vp01000001110 := by
  apply branch_checked idp010000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2103761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2105761639/2000000 : ℚ) by norm_num]
  exact coverp010000011101
theorem coverp01000001110 : Covers (-2103761639/4000000 : ℚ) vp01000001110 := join_branches bp010000011100 bp010000011101
private noncomputable def vp0100000111_0 : Blocks := edgeBlocks% "full/vectors/0100000111-V-0000.bin"
private noncomputable def vp0100000111_1 : Blocks := edgeBlocks% "full/vectors/0100000111-V-0001.bin"
noncomputable def vp0100000111 : Blocks := (Blocks.join vp0100000111_0 vp0100000111_1)
private theorem bp01000001110 : Branch 0 (-2103761639/8000000 : ℚ) vp0100000111 := by
  apply branch_left_normalized (c:=vp01000001110) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2103761639/4000000 : ℚ) by norm_num]
  exact coverp01000001110
private noncomputable def ep01000001111_0 : Blocks := edgeBlocks% "full/vectors/01000001111-E-0000.bin"
private noncomputable def ep01000001111_1 : Blocks := edgeBlocks% "full/vectors/01000001111-E-0001.bin"
noncomputable def ep01000001111 : Blocks := (Blocks.join ep01000001111_0 ep01000001111_1)
private theorem idp01000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000111.list =
    C ((2:ℤ)^217) * horner X vp01000001111.list + horner X ep01000001111.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000001111 : Branch 1 (-2103761639/8000000 : ℚ) vp0100000111 := by
  apply branch_checked idp01000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2107761639/4000000 : ℚ) by norm_num]
  exact coverp01000001111
theorem coverp0100000111 : Covers (-2103761639/8000000 : ℚ) vp0100000111 := join_branches bp01000001110 bp01000001111
private noncomputable def vp010000011011_0 : Blocks := edgeBlocks% "full/vectors/010000011011-V-0000.bin"
noncomputable def vp010000011011 : Blocks := vp010000011011_0
theorem coverp010000011011 : Covers (-2101761639/2000000 : ℚ) vp010000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000011010_0 : Blocks := edgeBlocks% "full/vectors/010000011010-V-0000.bin"
noncomputable def vp010000011010 : Blocks := vp010000011010_0
theorem coverp010000011010 : Covers (-2099761639/2000000 : ℚ) vp010000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001101_0 : Blocks := edgeBlocks% "full/vectors/01000001101-V-0000.bin"
noncomputable def vp01000001101 : Blocks := vp01000001101_0
private theorem bp010000011010 : Branch 0 (-2099761639/4000000 : ℚ) vp01000001101 := by
  apply branch_left_normalized (c:=vp010000011010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2099761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2099761639/2000000 : ℚ) by norm_num]
  exact coverp010000011010
private noncomputable def ep010000011011_0 : Blocks := edgeBlocks% "full/vectors/010000011011-E-0000.bin"
noncomputable def ep010000011011 : Blocks := ep010000011011_0
private theorem idp010000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001101.list =
    C ((2:ℤ)^120) * horner X vp010000011011.list + horner X ep010000011011.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000011011 : Branch 1 (-2099761639/4000000 : ℚ) vp01000001101 := by
  apply branch_checked idp010000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2099761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2101761639/2000000 : ℚ) by norm_num]
  exact coverp010000011011
theorem coverp01000001101 : Covers (-2099761639/4000000 : ℚ) vp01000001101 := join_branches bp010000011010 bp010000011011
private noncomputable def vp010000011001_0 : Blocks := edgeBlocks% "full/vectors/010000011001-V-0000.bin"
noncomputable def vp010000011001 : Blocks := vp010000011001_0
theorem coverp010000011001 : Covers (-2097761639/2000000 : ℚ) vp010000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000011000_0 : Blocks := edgeBlocks% "full/vectors/010000011000-V-0000.bin"
noncomputable def vp010000011000 : Blocks := vp010000011000_0
theorem coverp010000011000 : Covers (-2095761639/2000000 : ℚ) vp010000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001100_0 : Blocks := edgeBlocks% "full/vectors/01000001100-V-0000.bin"
noncomputable def vp01000001100 : Blocks := vp01000001100_0
private theorem bp010000011000 : Branch 0 (-2095761639/4000000 : ℚ) vp01000001100 := by
  apply branch_left_normalized (c:=vp010000011000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2095761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2095761639/2000000 : ℚ) by norm_num]
  exact coverp010000011000
private noncomputable def ep010000011001_0 : Blocks := edgeBlocks% "full/vectors/010000011001-E-0000.bin"
noncomputable def ep010000011001 : Blocks := ep010000011001_0
private theorem idp010000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001100.list =
    C ((2:ℤ)^119) * horner X vp010000011001.list + horner X ep010000011001.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000011001 : Branch 1 (-2095761639/4000000 : ℚ) vp01000001100 := by
  apply branch_checked idp010000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2095761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2097761639/2000000 : ℚ) by norm_num]
  exact coverp010000011001
theorem coverp01000001100 : Covers (-2095761639/4000000 : ℚ) vp01000001100 := join_branches bp010000011000 bp010000011001
private noncomputable def vp0100000110_0 : Blocks := edgeBlocks% "full/vectors/0100000110-V-0000.bin"
private noncomputable def vp0100000110_1 : Blocks := edgeBlocks% "full/vectors/0100000110-V-0001.bin"
noncomputable def vp0100000110 : Blocks := (Blocks.join vp0100000110_0 vp0100000110_1)
private theorem bp01000001100 : Branch 0 (-2095761639/8000000 : ℚ) vp0100000110 := by
  apply branch_left_normalized (c:=vp01000001100) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-2095761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2095761639/4000000 : ℚ) by norm_num]
  exact coverp01000001100
private noncomputable def ep01000001101_0 : Blocks := edgeBlocks% "full/vectors/01000001101-E-0000.bin"
private noncomputable def ep01000001101_1 : Blocks := edgeBlocks% "full/vectors/01000001101-E-0001.bin"
noncomputable def ep01000001101 : Blocks := (Blocks.join ep01000001101_0 ep01000001101_1)
private theorem idp01000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000110.list =
    C ((2:ℤ)^216) * horner X vp01000001101.list + horner X ep01000001101.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000001101 : Branch 1 (-2095761639/8000000 : ℚ) vp0100000110 := by
  apply branch_checked idp01000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2095761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2099761639/4000000 : ℚ) by norm_num]
  exact coverp01000001101
theorem coverp0100000110 : Covers (-2095761639/8000000 : ℚ) vp0100000110 := join_branches bp01000001100 bp01000001101
private noncomputable def vp010000011_0 : Blocks := edgeBlocks% "full/vectors/010000011-V-0000.bin"
private noncomputable def vp010000011_1 : Blocks := edgeBlocks% "full/vectors/010000011-V-0001.bin"
private noncomputable def vp010000011_2 : Blocks := edgeBlocks% "full/vectors/010000011-V-0002.bin"
noncomputable def vp010000011 : Blocks := (Blocks.join vp010000011_0 (Blocks.join vp010000011_1 vp010000011_2))
private theorem bp0100000110 : Branch 0 (-2095761639/16000000 : ℚ) vp010000011 := by
  apply branch_left_normalized (c:=vp0100000110) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-2095761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2095761639/8000000 : ℚ) by norm_num]
  exact coverp0100000110
private noncomputable def ep0100000111_0 : Blocks := edgeBlocks% "full/vectors/0100000111-E-0000.bin"
private noncomputable def ep0100000111_1 : Blocks := edgeBlocks% "full/vectors/0100000111-E-0001.bin"
private noncomputable def ep0100000111_2 : Blocks := edgeBlocks% "full/vectors/0100000111-E-0002.bin"
noncomputable def ep0100000111 : Blocks := (Blocks.join ep0100000111_0 (Blocks.join ep0100000111_1 ep0100000111_2))
private theorem idp0100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000011.list =
    C ((2:ℤ)^412) * horner X vp0100000111.list + horner X ep0100000111.list := by
  exact edge_identity (B := (2:ℤ)^649) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100000111 : Branch 1 (-2095761639/16000000 : ℚ) vp010000011 := by
  apply branch_checked idp0100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2095761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2103761639/8000000 : ℚ) by norm_num]
  exact coverp0100000111
theorem coverp010000011 : Covers (-2095761639/16000000 : ℚ) vp010000011 := join_branches bp0100000110 bp0100000111
private noncomputable def vp010000010111_0 : Blocks := edgeBlocks% "full/vectors/010000010111-V-0000.bin"
noncomputable def vp010000010111 : Blocks := vp010000010111_0
theorem coverp010000010111 : Covers (-2093761639/2000000 : ℚ) vp010000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000010110_0 : Blocks := edgeBlocks% "full/vectors/010000010110-V-0000.bin"
noncomputable def vp010000010110 : Blocks := vp010000010110_0
theorem coverp010000010110 : Covers (-2091761639/2000000 : ℚ) vp010000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001011_0 : Blocks := edgeBlocks% "full/vectors/01000001011-V-0000.bin"
noncomputable def vp01000001011 : Blocks := vp01000001011_0
private theorem bp010000010110 : Branch 0 (-2091761639/4000000 : ℚ) vp01000001011 := by
  apply branch_left_normalized (c:=vp010000010110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2091761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2091761639/2000000 : ℚ) by norm_num]
  exact coverp010000010110
private noncomputable def ep010000010111_0 : Blocks := edgeBlocks% "full/vectors/010000010111-E-0000.bin"
noncomputable def ep010000010111 : Blocks := ep010000010111_0
private theorem idp010000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001011.list =
    C ((2:ℤ)^119) * horner X vp010000010111.list + horner X ep010000010111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000010111 : Branch 1 (-2091761639/4000000 : ℚ) vp01000001011 := by
  apply branch_checked idp010000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2091761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2093761639/2000000 : ℚ) by norm_num]
  exact coverp010000010111
theorem coverp01000001011 : Covers (-2091761639/4000000 : ℚ) vp01000001011 := join_branches bp010000010110 bp010000010111
private noncomputable def vp010000010101_0 : Blocks := edgeBlocks% "full/vectors/010000010101-V-0000.bin"
noncomputable def vp010000010101 : Blocks := vp010000010101_0
theorem coverp010000010101 : Covers (-2089761639/2000000 : ℚ) vp010000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000010100_0 : Blocks := edgeBlocks% "full/vectors/010000010100-V-0000.bin"
noncomputable def vp010000010100 : Blocks := vp010000010100_0
theorem coverp010000010100 : Covers (-2087761639/2000000 : ℚ) vp010000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001010_0 : Blocks := edgeBlocks% "full/vectors/01000001010-V-0000.bin"
noncomputable def vp01000001010 : Blocks := vp01000001010_0
private theorem bp010000010100 : Branch 0 (-2087761639/4000000 : ℚ) vp01000001010 := by
  apply branch_left_normalized (c:=vp010000010100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2087761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2087761639/2000000 : ℚ) by norm_num]
  exact coverp010000010100
private noncomputable def ep010000010101_0 : Blocks := edgeBlocks% "full/vectors/010000010101-E-0000.bin"
noncomputable def ep010000010101 : Blocks := ep010000010101_0
private theorem idp010000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001010.list =
    C ((2:ℤ)^120) * horner X vp010000010101.list + horner X ep010000010101.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000010101 : Branch 1 (-2087761639/4000000 : ℚ) vp01000001010 := by
  apply branch_checked idp010000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2087761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2089761639/2000000 : ℚ) by norm_num]
  exact coverp010000010101
theorem coverp01000001010 : Covers (-2087761639/4000000 : ℚ) vp01000001010 := join_branches bp010000010100 bp010000010101
private noncomputable def vp0100000101_0 : Blocks := edgeBlocks% "full/vectors/0100000101-V-0000.bin"
private noncomputable def vp0100000101_1 : Blocks := edgeBlocks% "full/vectors/0100000101-V-0001.bin"
noncomputable def vp0100000101 : Blocks := (Blocks.join vp0100000101_0 vp0100000101_1)
private theorem bp01000001010 : Branch 0 (-2087761639/8000000 : ℚ) vp0100000101 := by
  apply branch_left_normalized (c:=vp01000001010) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-2087761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2087761639/4000000 : ℚ) by norm_num]
  exact coverp01000001010
private noncomputable def ep01000001011_0 : Blocks := edgeBlocks% "full/vectors/01000001011-E-0000.bin"
private noncomputable def ep01000001011_1 : Blocks := edgeBlocks% "full/vectors/01000001011-E-0001.bin"
noncomputable def ep01000001011 : Blocks := (Blocks.join ep01000001011_0 ep01000001011_1)
private theorem idp01000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000101.list =
    C ((2:ℤ)^219) * horner X vp01000001011.list + horner X ep01000001011.list := by
  exact edge_identity (B := (2:ℤ)^388) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000001011 : Branch 1 (-2087761639/8000000 : ℚ) vp0100000101 := by
  apply branch_checked idp01000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2087761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2091761639/4000000 : ℚ) by norm_num]
  exact coverp01000001011
theorem coverp0100000101 : Covers (-2087761639/8000000 : ℚ) vp0100000101 := join_branches bp01000001010 bp01000001011
private noncomputable def vp010000010011_0 : Blocks := edgeBlocks% "full/vectors/010000010011-V-0000.bin"
noncomputable def vp010000010011 : Blocks := vp010000010011_0
theorem coverp010000010011 : Covers (-2085761639/2000000 : ℚ) vp010000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000010010_0 : Blocks := edgeBlocks% "full/vectors/010000010010-V-0000.bin"
noncomputable def vp010000010010 : Blocks := vp010000010010_0
theorem coverp010000010010 : Covers (-2083761639/2000000 : ℚ) vp010000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001001_0 : Blocks := edgeBlocks% "full/vectors/01000001001-V-0000.bin"
noncomputable def vp01000001001 : Blocks := vp01000001001_0
private theorem bp010000010010 : Branch 0 (-2083761639/4000000 : ℚ) vp01000001001 := by
  apply branch_left_normalized (c:=vp010000010010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2083761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2083761639/2000000 : ℚ) by norm_num]
  exact coverp010000010010
private noncomputable def ep010000010011_0 : Blocks := edgeBlocks% "full/vectors/010000010011-E-0000.bin"
noncomputable def ep010000010011 : Blocks := ep010000010011_0
private theorem idp010000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001001.list =
    C ((2:ℤ)^119) * horner X vp010000010011.list + horner X ep010000010011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000010011 : Branch 1 (-2083761639/4000000 : ℚ) vp01000001001 := by
  apply branch_checked idp010000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2083761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2085761639/2000000 : ℚ) by norm_num]
  exact coverp010000010011
theorem coverp01000001001 : Covers (-2083761639/4000000 : ℚ) vp01000001001 := join_branches bp010000010010 bp010000010011
private noncomputable def vp010000010001_0 : Blocks := edgeBlocks% "full/vectors/010000010001-V-0000.bin"
noncomputable def vp010000010001 : Blocks := vp010000010001_0
theorem coverp010000010001 : Covers (-2081761639/2000000 : ℚ) vp010000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000010000_0 : Blocks := edgeBlocks% "full/vectors/010000010000-V-0000.bin"
noncomputable def vp010000010000 : Blocks := vp010000010000_0
theorem coverp010000010000 : Covers (-2079761639/2000000 : ℚ) vp010000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000001000_0 : Blocks := edgeBlocks% "full/vectors/01000001000-V-0000.bin"
noncomputable def vp01000001000 : Blocks := vp01000001000_0
private theorem bp010000010000 : Branch 0 (-2079761639/4000000 : ℚ) vp01000001000 := by
  apply branch_left_normalized (c:=vp010000010000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2079761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2079761639/2000000 : ℚ) by norm_num]
  exact coverp010000010000
private noncomputable def ep010000010001_0 : Blocks := edgeBlocks% "full/vectors/010000010001-E-0000.bin"
noncomputable def ep010000010001 : Blocks := ep010000010001_0
private theorem idp010000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001000.list =
    C ((2:ℤ)^118) * horner X vp010000010001.list + horner X ep010000010001.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000010001 : Branch 1 (-2079761639/4000000 : ℚ) vp01000001000 := by
  apply branch_checked idp010000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2079761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2081761639/2000000 : ℚ) by norm_num]
  exact coverp010000010001
theorem coverp01000001000 : Covers (-2079761639/4000000 : ℚ) vp01000001000 := join_branches bp010000010000 bp010000010001
private noncomputable def vp0100000100_0 : Blocks := edgeBlocks% "full/vectors/0100000100-V-0000.bin"
private noncomputable def vp0100000100_1 : Blocks := edgeBlocks% "full/vectors/0100000100-V-0001.bin"
noncomputable def vp0100000100 : Blocks := (Blocks.join vp0100000100_0 vp0100000100_1)
private theorem bp01000001000 : Branch 0 (-2079761639/8000000 : ℚ) vp0100000100 := by
  apply branch_left_normalized (c:=vp01000001000) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2079761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2079761639/4000000 : ℚ) by norm_num]
  exact coverp01000001000
private noncomputable def ep01000001001_0 : Blocks := edgeBlocks% "full/vectors/01000001001-E-0000.bin"
private noncomputable def ep01000001001_1 : Blocks := edgeBlocks% "full/vectors/01000001001-E-0001.bin"
noncomputable def ep01000001001 : Blocks := (Blocks.join ep01000001001_0 ep01000001001_1)
private theorem idp01000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000100.list =
    C ((2:ℤ)^217) * horner X vp01000001001.list + horner X ep01000001001.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000001001 : Branch 1 (-2079761639/8000000 : ℚ) vp0100000100 := by
  apply branch_checked idp01000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2079761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2083761639/4000000 : ℚ) by norm_num]
  exact coverp01000001001
theorem coverp0100000100 : Covers (-2079761639/8000000 : ℚ) vp0100000100 := join_branches bp01000001000 bp01000001001
private noncomputable def vp010000010_0 : Blocks := edgeBlocks% "full/vectors/010000010-V-0000.bin"
private noncomputable def vp010000010_1 : Blocks := edgeBlocks% "full/vectors/010000010-V-0001.bin"
private noncomputable def vp010000010_2 : Blocks := edgeBlocks% "full/vectors/010000010-V-0002.bin"
noncomputable def vp010000010 : Blocks := (Blocks.join vp010000010_0 (Blocks.join vp010000010_1 vp010000010_2))
private theorem bp0100000100 : Branch 0 (-2079761639/16000000 : ℚ) vp010000010 := by
  apply branch_left_normalized (c:=vp0100000100) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-2079761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2079761639/8000000 : ℚ) by norm_num]
  exact coverp0100000100
private noncomputable def ep0100000101_0 : Blocks := edgeBlocks% "full/vectors/0100000101-E-0000.bin"
private noncomputable def ep0100000101_1 : Blocks := edgeBlocks% "full/vectors/0100000101-E-0001.bin"
private noncomputable def ep0100000101_2 : Blocks := edgeBlocks% "full/vectors/0100000101-E-0002.bin"
noncomputable def ep0100000101 : Blocks := (Blocks.join ep0100000101_0 (Blocks.join ep0100000101_1 ep0100000101_2))
private theorem idp0100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000010.list =
    C ((2:ℤ)^412) * horner X vp0100000101.list + horner X ep0100000101.list := by
  exact edge_identity (B := (2:ℤ)^650) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100000101 : Branch 1 (-2079761639/16000000 : ℚ) vp010000010 := by
  apply branch_checked idp0100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2079761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2087761639/8000000 : ℚ) by norm_num]
  exact coverp0100000101
theorem coverp010000010 : Covers (-2079761639/16000000 : ℚ) vp010000010 := join_branches bp0100000100 bp0100000101
private noncomputable def vp01000001_0 : Blocks := edgeBlocks% "full/vectors/01000001-V-0000.bin"
private noncomputable def vp01000001_1 : Blocks := edgeBlocks% "full/vectors/01000001-V-0001.bin"
private noncomputable def vp01000001_2 : Blocks := edgeBlocks% "full/vectors/01000001-V-0002.bin"
private noncomputable def vp01000001_3 : Blocks := edgeBlocks% "full/vectors/01000001-V-0003.bin"
private noncomputable def vp01000001_4 : Blocks := edgeBlocks% "full/vectors/01000001-V-0004.bin"
private noncomputable def vp01000001_5 : Blocks := edgeBlocks% "full/vectors/01000001-V-0005.bin"
noncomputable def vp01000001 : Blocks := (Blocks.join (Blocks.join vp01000001_0 (Blocks.join vp01000001_1 vp01000001_2)) (Blocks.join vp01000001_3 (Blocks.join vp01000001_4 vp01000001_5)))
private theorem bp010000010 : Branch 0 (-2079761639/32000000 : ℚ) vp01000001 := by
  apply branch_left_normalized (c:=vp010000010) (k:=0) (m:=366) (by decide +kernel)
  rw [show 2*(-2079761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2079761639/16000000 : ℚ) by norm_num]
  exact coverp010000010
private noncomputable def ep010000011_0 : Blocks := edgeBlocks% "full/vectors/010000011-E-0000.bin"
private noncomputable def ep010000011_1 : Blocks := edgeBlocks% "full/vectors/010000011-E-0001.bin"
private noncomputable def ep010000011_2 : Blocks := edgeBlocks% "full/vectors/010000011-E-0002.bin"
private noncomputable def ep010000011_3 : Blocks := edgeBlocks% "full/vectors/010000011-E-0003.bin"
private noncomputable def ep010000011_4 : Blocks := edgeBlocks% "full/vectors/010000011-E-0004.bin"
private noncomputable def ep010000011_5 : Blocks := edgeBlocks% "full/vectors/010000011-E-0005.bin"
noncomputable def ep010000011 : Blocks := (Blocks.join (Blocks.join ep010000011_0 (Blocks.join ep010000011_1 ep010000011_2)) (Blocks.join ep010000011_3 (Blocks.join ep010000011_4 ep010000011_5)))
private theorem idp010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000001.list =
    C ((2:ℤ)^798) * horner X vp010000011.list + horner X ep010000011.list := by
  exact edge_identity (B := (2:ℤ)^1171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000011 : Branch 1 (-2079761639/32000000 : ℚ) vp01000001 := by
  apply branch_checked idp010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2079761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2095761639/16000000 : ℚ) by norm_num]
  exact coverp010000011
theorem coverp01000001 : Covers (-2079761639/32000000 : ℚ) vp01000001 := join_branches bp010000010 bp010000011
private noncomputable def vp010000001111_0 : Blocks := edgeBlocks% "full/vectors/010000001111-V-0000.bin"
noncomputable def vp010000001111 : Blocks := vp010000001111_0
theorem coverp010000001111 : Covers (-2077761639/2000000 : ℚ) vp010000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000001110_0 : Blocks := edgeBlocks% "full/vectors/010000001110-V-0000.bin"
noncomputable def vp010000001110 : Blocks := vp010000001110_0
theorem coverp010000001110 : Covers (-2075761639/2000000 : ℚ) vp010000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000111_0 : Blocks := edgeBlocks% "full/vectors/01000000111-V-0000.bin"
noncomputable def vp01000000111 : Blocks := vp01000000111_0
private theorem bp010000001110 : Branch 0 (-2075761639/4000000 : ℚ) vp01000000111 := by
  apply branch_left_normalized (c:=vp010000001110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2075761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2075761639/2000000 : ℚ) by norm_num]
  exact coverp010000001110
private noncomputable def ep010000001111_0 : Blocks := edgeBlocks% "full/vectors/010000001111-E-0000.bin"
noncomputable def ep010000001111 : Blocks := ep010000001111_0
private theorem idp010000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000111.list =
    C ((2:ℤ)^121) * horner X vp010000001111.list + horner X ep010000001111.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000001111 : Branch 1 (-2075761639/4000000 : ℚ) vp01000000111 := by
  apply branch_checked idp010000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2075761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2077761639/2000000 : ℚ) by norm_num]
  exact coverp010000001111
theorem coverp01000000111 : Covers (-2075761639/4000000 : ℚ) vp01000000111 := join_branches bp010000001110 bp010000001111
private noncomputable def vp010000001101_0 : Blocks := edgeBlocks% "full/vectors/010000001101-V-0000.bin"
noncomputable def vp010000001101 : Blocks := vp010000001101_0
theorem coverp010000001101 : Covers (-2073761639/2000000 : ℚ) vp010000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000001100_0 : Blocks := edgeBlocks% "full/vectors/010000001100-V-0000.bin"
noncomputable def vp010000001100 : Blocks := vp010000001100_0
theorem coverp010000001100 : Covers (-2071761639/2000000 : ℚ) vp010000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000110_0 : Blocks := edgeBlocks% "full/vectors/01000000110-V-0000.bin"
noncomputable def vp01000000110 : Blocks := vp01000000110_0
private theorem bp010000001100 : Branch 0 (-2071761639/4000000 : ℚ) vp01000000110 := by
  apply branch_left_normalized (c:=vp010000001100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2071761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2071761639/2000000 : ℚ) by norm_num]
  exact coverp010000001100
private noncomputable def ep010000001101_0 : Blocks := edgeBlocks% "full/vectors/010000001101-E-0000.bin"
noncomputable def ep010000001101 : Blocks := ep010000001101_0
private theorem idp010000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000110.list =
    C ((2:ℤ)^120) * horner X vp010000001101.list + horner X ep010000001101.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000001101 : Branch 1 (-2071761639/4000000 : ℚ) vp01000000110 := by
  apply branch_checked idp010000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2071761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2073761639/2000000 : ℚ) by norm_num]
  exact coverp010000001101
theorem coverp01000000110 : Covers (-2071761639/4000000 : ℚ) vp01000000110 := join_branches bp010000001100 bp010000001101
private noncomputable def vp0100000011_0 : Blocks := edgeBlocks% "full/vectors/0100000011-V-0000.bin"
private noncomputable def vp0100000011_1 : Blocks := edgeBlocks% "full/vectors/0100000011-V-0001.bin"
noncomputable def vp0100000011 : Blocks := (Blocks.join vp0100000011_0 vp0100000011_1)
private theorem bp01000000110 : Branch 0 (-2071761639/8000000 : ℚ) vp0100000011 := by
  apply branch_left_normalized (c:=vp01000000110) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-2071761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2071761639/4000000 : ℚ) by norm_num]
  exact coverp01000000110
private noncomputable def ep01000000111_0 : Blocks := edgeBlocks% "full/vectors/01000000111-E-0000.bin"
private noncomputable def ep01000000111_1 : Blocks := edgeBlocks% "full/vectors/01000000111-E-0001.bin"
noncomputable def ep01000000111 : Blocks := (Blocks.join ep01000000111_0 ep01000000111_1)
private theorem idp01000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000011.list =
    C ((2:ℤ)^218) * horner X vp01000000111.list + horner X ep01000000111.list := by
  exact edge_identity (B := (2:ℤ)^388) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000000111 : Branch 1 (-2071761639/8000000 : ℚ) vp0100000011 := by
  apply branch_checked idp01000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2071761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2075761639/4000000 : ℚ) by norm_num]
  exact coverp01000000111
theorem coverp0100000011 : Covers (-2071761639/8000000 : ℚ) vp0100000011 := join_branches bp01000000110 bp01000000111
private noncomputable def vp010000001011_0 : Blocks := edgeBlocks% "full/vectors/010000001011-V-0000.bin"
noncomputable def vp010000001011 : Blocks := vp010000001011_0
theorem coverp010000001011 : Covers (-2069761639/2000000 : ℚ) vp010000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000001010_0 : Blocks := edgeBlocks% "full/vectors/010000001010-V-0000.bin"
noncomputable def vp010000001010 : Blocks := vp010000001010_0
theorem coverp010000001010 : Covers (-2067761639/2000000 : ℚ) vp010000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000101_0 : Blocks := edgeBlocks% "full/vectors/01000000101-V-0000.bin"
noncomputable def vp01000000101 : Blocks := vp01000000101_0
private theorem bp010000001010 : Branch 0 (-2067761639/4000000 : ℚ) vp01000000101 := by
  apply branch_left_normalized (c:=vp010000001010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2067761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2067761639/2000000 : ℚ) by norm_num]
  exact coverp010000001010
private noncomputable def ep010000001011_0 : Blocks := edgeBlocks% "full/vectors/010000001011-E-0000.bin"
noncomputable def ep010000001011 : Blocks := ep010000001011_0
private theorem idp010000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000101.list =
    C ((2:ℤ)^119) * horner X vp010000001011.list + horner X ep010000001011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000001011 : Branch 1 (-2067761639/4000000 : ℚ) vp01000000101 := by
  apply branch_checked idp010000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2067761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2069761639/2000000 : ℚ) by norm_num]
  exact coverp010000001011
theorem coverp01000000101 : Covers (-2067761639/4000000 : ℚ) vp01000000101 := join_branches bp010000001010 bp010000001011
private noncomputable def vp010000001001_0 : Blocks := edgeBlocks% "full/vectors/010000001001-V-0000.bin"
noncomputable def vp010000001001 : Blocks := vp010000001001_0
theorem coverp010000001001 : Covers (-2065761639/2000000 : ℚ) vp010000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000001000_0 : Blocks := edgeBlocks% "full/vectors/010000001000-V-0000.bin"
noncomputable def vp010000001000 : Blocks := vp010000001000_0
theorem coverp010000001000 : Covers (-2063761639/2000000 : ℚ) vp010000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000100_0 : Blocks := edgeBlocks% "full/vectors/01000000100-V-0000.bin"
noncomputable def vp01000000100 : Blocks := vp01000000100_0
private theorem bp010000001000 : Branch 0 (-2063761639/4000000 : ℚ) vp01000000100 := by
  apply branch_left_normalized (c:=vp010000001000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2063761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2063761639/2000000 : ℚ) by norm_num]
  exact coverp010000001000
private noncomputable def ep010000001001_0 : Blocks := edgeBlocks% "full/vectors/010000001001-E-0000.bin"
noncomputable def ep010000001001 : Blocks := ep010000001001_0
private theorem idp010000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000100.list =
    C ((2:ℤ)^121) * horner X vp010000001001.list + horner X ep010000001001.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000001001 : Branch 1 (-2063761639/4000000 : ℚ) vp01000000100 := by
  apply branch_checked idp010000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2063761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2065761639/2000000 : ℚ) by norm_num]
  exact coverp010000001001
theorem coverp01000000100 : Covers (-2063761639/4000000 : ℚ) vp01000000100 := join_branches bp010000001000 bp010000001001
private noncomputable def vp0100000010_0 : Blocks := edgeBlocks% "full/vectors/0100000010-V-0000.bin"
private noncomputable def vp0100000010_1 : Blocks := edgeBlocks% "full/vectors/0100000010-V-0001.bin"
noncomputable def vp0100000010 : Blocks := (Blocks.join vp0100000010_0 vp0100000010_1)
private theorem bp01000000100 : Branch 0 (-2063761639/8000000 : ℚ) vp0100000010 := by
  apply branch_left_normalized (c:=vp01000000100) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-2063761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2063761639/4000000 : ℚ) by norm_num]
  exact coverp01000000100
private noncomputable def ep01000000101_0 : Blocks := edgeBlocks% "full/vectors/01000000101-E-0000.bin"
private noncomputable def ep01000000101_1 : Blocks := edgeBlocks% "full/vectors/01000000101-E-0001.bin"
noncomputable def ep01000000101 : Blocks := (Blocks.join ep01000000101_0 ep01000000101_1)
private theorem idp01000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000010.list =
    C ((2:ℤ)^220) * horner X vp01000000101.list + horner X ep01000000101.list := by
  exact edge_identity (B := (2:ℤ)^389) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000000101 : Branch 1 (-2063761639/8000000 : ℚ) vp0100000010 := by
  apply branch_checked idp01000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2063761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2067761639/4000000 : ℚ) by norm_num]
  exact coverp01000000101
theorem coverp0100000010 : Covers (-2063761639/8000000 : ℚ) vp0100000010 := join_branches bp01000000100 bp01000000101
private noncomputable def vp010000001_0 : Blocks := edgeBlocks% "full/vectors/010000001-V-0000.bin"
private noncomputable def vp010000001_1 : Blocks := edgeBlocks% "full/vectors/010000001-V-0001.bin"
private noncomputable def vp010000001_2 : Blocks := edgeBlocks% "full/vectors/010000001-V-0002.bin"
noncomputable def vp010000001 : Blocks := (Blocks.join vp010000001_0 (Blocks.join vp010000001_1 vp010000001_2))
private theorem bp0100000010 : Branch 0 (-2063761639/16000000 : ℚ) vp010000001 := by
  apply branch_left_normalized (c:=vp0100000010) (k:=0) (m:=195) (by decide +kernel)
  rw [show 2*(-2063761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2063761639/8000000 : ℚ) by norm_num]
  exact coverp0100000010
private noncomputable def ep0100000011_0 : Blocks := edgeBlocks% "full/vectors/0100000011-E-0000.bin"
private noncomputable def ep0100000011_1 : Blocks := edgeBlocks% "full/vectors/0100000011-E-0001.bin"
private noncomputable def ep0100000011_2 : Blocks := edgeBlocks% "full/vectors/0100000011-E-0002.bin"
noncomputable def ep0100000011 : Blocks := (Blocks.join ep0100000011_0 (Blocks.join ep0100000011_1 ep0100000011_2))
private theorem idp0100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000001.list =
    C ((2:ℤ)^414) * horner X vp0100000011.list + horner X ep0100000011.list := by
  exact edge_identity (B := (2:ℤ)^653) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100000011 : Branch 1 (-2063761639/16000000 : ℚ) vp010000001 := by
  apply branch_checked idp0100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2063761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2071761639/8000000 : ℚ) by norm_num]
  exact coverp0100000011
theorem coverp010000001 : Covers (-2063761639/16000000 : ℚ) vp010000001 := join_branches bp0100000010 bp0100000011
private noncomputable def vp010000000111_0 : Blocks := edgeBlocks% "full/vectors/010000000111-V-0000.bin"
noncomputable def vp010000000111 : Blocks := vp010000000111_0
theorem coverp010000000111 : Covers (-2061761639/2000000 : ℚ) vp010000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010000000110_0 : Blocks := edgeBlocks% "full/vectors/010000000110-V-0000.bin"
noncomputable def vp010000000110 : Blocks := vp010000000110_0
theorem coverp010000000110 : Covers (-2059761639/2000000 : ℚ) vp010000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000011_0 : Blocks := edgeBlocks% "full/vectors/01000000011-V-0000.bin"
noncomputable def vp01000000011 : Blocks := vp01000000011_0
private theorem bp010000000110 : Branch 0 (-2059761639/4000000 : ℚ) vp01000000011 := by
  apply branch_left_normalized (c:=vp010000000110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2059761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2059761639/2000000 : ℚ) by norm_num]
  exact coverp010000000110
private noncomputable def ep010000000111_0 : Blocks := edgeBlocks% "full/vectors/010000000111-E-0000.bin"
noncomputable def ep010000000111 : Blocks := ep010000000111_0
private theorem idp010000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000011.list =
    C ((2:ℤ)^118) * horner X vp010000000111.list + horner X ep010000000111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000000111 : Branch 1 (-2059761639/4000000 : ℚ) vp01000000011 := by
  apply branch_checked idp010000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2059761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2061761639/2000000 : ℚ) by norm_num]
  exact coverp010000000111
theorem coverp01000000011 : Covers (-2059761639/4000000 : ℚ) vp01000000011 := join_branches bp010000000110 bp010000000111
private noncomputable def vp010000000101_0 : Blocks := edgeBlocks% "full/vectors/010000000101-V-0000.bin"
noncomputable def vp010000000101 : Blocks := vp010000000101_0
theorem coverp010000000101 : Covers (-2057761639/2000000 : ℚ) vp010000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010000000100_0 : Blocks := edgeBlocks% "full/vectors/010000000100-V-0000.bin"
noncomputable def vp010000000100 : Blocks := vp010000000100_0
theorem coverp010000000100 : Covers (-2055761639/2000000 : ℚ) vp010000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000010_0 : Blocks := edgeBlocks% "full/vectors/01000000010-V-0000.bin"
noncomputable def vp01000000010 : Blocks := vp01000000010_0
private theorem bp010000000100 : Branch 0 (-2055761639/4000000 : ℚ) vp01000000010 := by
  apply branch_left_normalized (c:=vp010000000100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2055761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2055761639/2000000 : ℚ) by norm_num]
  exact coverp010000000100
private noncomputable def ep010000000101_0 : Blocks := edgeBlocks% "full/vectors/010000000101-E-0000.bin"
noncomputable def ep010000000101 : Blocks := ep010000000101_0
private theorem idp010000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000010.list =
    C ((2:ℤ)^119) * horner X vp010000000101.list + horner X ep010000000101.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000000101 : Branch 1 (-2055761639/4000000 : ℚ) vp01000000010 := by
  apply branch_checked idp010000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2055761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2057761639/2000000 : ℚ) by norm_num]
  exact coverp010000000101
theorem coverp01000000010 : Covers (-2055761639/4000000 : ℚ) vp01000000010 := join_branches bp010000000100 bp010000000101
private noncomputable def vp0100000001_0 : Blocks := edgeBlocks% "full/vectors/0100000001-V-0000.bin"
private noncomputable def vp0100000001_1 : Blocks := edgeBlocks% "full/vectors/0100000001-V-0001.bin"
noncomputable def vp0100000001 : Blocks := (Blocks.join vp0100000001_0 vp0100000001_1)
private theorem bp01000000010 : Branch 0 (-2055761639/8000000 : ℚ) vp0100000001 := by
  apply branch_left_normalized (c:=vp01000000010) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-2055761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2055761639/4000000 : ℚ) by norm_num]
  exact coverp01000000010
private noncomputable def ep01000000011_0 : Blocks := edgeBlocks% "full/vectors/01000000011-E-0000.bin"
private noncomputable def ep01000000011_1 : Blocks := edgeBlocks% "full/vectors/01000000011-E-0001.bin"
noncomputable def ep01000000011 : Blocks := (Blocks.join ep01000000011_0 ep01000000011_1)
private theorem idp01000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000001.list =
    C ((2:ℤ)^217) * horner X vp01000000011.list + horner X ep01000000011.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000000011 : Branch 1 (-2055761639/8000000 : ℚ) vp0100000001 := by
  apply branch_checked idp01000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2055761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2059761639/4000000 : ℚ) by norm_num]
  exact coverp01000000011
theorem coverp0100000001 : Covers (-2055761639/8000000 : ℚ) vp0100000001 := join_branches bp01000000010 bp01000000011
private noncomputable def vp010000000011_0 : Blocks := edgeBlocks% "full/vectors/010000000011-V-0000.bin"
noncomputable def vp010000000011 : Blocks := vp010000000011_0
theorem coverp010000000011 : Covers (-2053761639/2000000 : ℚ) vp010000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010000000010_0 : Blocks := edgeBlocks% "full/vectors/010000000010-V-0000.bin"
noncomputable def vp010000000010 : Blocks := vp010000000010_0
theorem coverp010000000010 : Covers (-2051761639/2000000 : ℚ) vp010000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000001_0 : Blocks := edgeBlocks% "full/vectors/01000000001-V-0000.bin"
noncomputable def vp01000000001 : Blocks := vp01000000001_0
private theorem bp010000000010 : Branch 0 (-2051761639/4000000 : ℚ) vp01000000001 := by
  apply branch_left_normalized (c:=vp010000000010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-2051761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2051761639/2000000 : ℚ) by norm_num]
  exact coverp010000000010
private noncomputable def ep010000000011_0 : Blocks := edgeBlocks% "full/vectors/010000000011-E-0000.bin"
noncomputable def ep010000000011 : Blocks := ep010000000011_0
private theorem idp010000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000001.list =
    C ((2:ℤ)^121) * horner X vp010000000011.list + horner X ep010000000011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000000011 : Branch 1 (-2051761639/4000000 : ℚ) vp01000000001 := by
  apply branch_checked idp010000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2051761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2053761639/2000000 : ℚ) by norm_num]
  exact coverp010000000011
theorem coverp01000000001 : Covers (-2051761639/4000000 : ℚ) vp01000000001 := join_branches bp010000000010 bp010000000011
private noncomputable def vp010000000001_0 : Blocks := edgeBlocks% "full/vectors/010000000001-V-0000.bin"
noncomputable def vp010000000001 : Blocks := vp010000000001_0
theorem coverp010000000001 : Covers (-2049761639/2000000 : ℚ) vp010000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010000000000_0 : Blocks := edgeBlocks% "full/vectors/010000000000-V-0000.bin"
noncomputable def vp010000000000 : Blocks := vp010000000000_0
theorem coverp010000000000 : Covers (-2047761639/2000000 : ℚ) vp010000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000000000_0 : Blocks := edgeBlocks% "full/vectors/01000000000-V-0000.bin"
noncomputable def vp01000000000 : Blocks := vp01000000000_0
private theorem bp010000000000 : Branch 0 (-2047761639/4000000 : ℚ) vp01000000000 := by
  apply branch_left_normalized (c:=vp010000000000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2047761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/2000000 : ℚ) by norm_num]
  exact coverp010000000000
private noncomputable def ep010000000001_0 : Blocks := edgeBlocks% "full/vectors/010000000001-E-0000.bin"
noncomputable def ep010000000001 : Blocks := ep010000000001_0
private theorem idp010000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000000.list =
    C ((2:ℤ)^115) * horner X vp010000000001.list + horner X ep010000000001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000000001 : Branch 1 (-2047761639/4000000 : ℚ) vp01000000000 := by
  apply branch_checked idp010000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2049761639/2000000 : ℚ) by norm_num]
  exact coverp010000000001
theorem coverp01000000000 : Covers (-2047761639/4000000 : ℚ) vp01000000000 := join_branches bp010000000000 bp010000000001
private noncomputable def vp0100000000_0 : Blocks := edgeBlocks% "full/vectors/0100000000-V-0000.bin"
private noncomputable def vp0100000000_1 : Blocks := edgeBlocks% "full/vectors/0100000000-V-0001.bin"
noncomputable def vp0100000000 : Blocks := (Blocks.join vp0100000000_0 vp0100000000_1)
private theorem bp01000000000 : Branch 0 (-2047761639/8000000 : ℚ) vp0100000000 := by
  apply branch_left_normalized (c:=vp01000000000) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-2047761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/4000000 : ℚ) by norm_num]
  exact coverp01000000000
private noncomputable def ep01000000001_0 : Blocks := edgeBlocks% "full/vectors/01000000001-E-0000.bin"
private noncomputable def ep01000000001_1 : Blocks := edgeBlocks% "full/vectors/01000000001-E-0001.bin"
noncomputable def ep01000000001 : Blocks := (Blocks.join ep01000000001_0 ep01000000001_1)
private theorem idp01000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000000.list =
    C ((2:ℤ)^215) * horner X vp01000000001.list + horner X ep01000000001.list := by
  exact edge_identity (B := (2:ℤ)^384) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000000001 : Branch 1 (-2047761639/8000000 : ℚ) vp0100000000 := by
  apply branch_checked idp01000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2051761639/4000000 : ℚ) by norm_num]
  exact coverp01000000001
theorem coverp0100000000 : Covers (-2047761639/8000000 : ℚ) vp0100000000 := join_branches bp01000000000 bp01000000001
private noncomputable def vp010000000_0 : Blocks := edgeBlocks% "full/vectors/010000000-V-0000.bin"
private noncomputable def vp010000000_1 : Blocks := edgeBlocks% "full/vectors/010000000-V-0001.bin"
private noncomputable def vp010000000_2 : Blocks := edgeBlocks% "full/vectors/010000000-V-0002.bin"
noncomputable def vp010000000 : Blocks := (Blocks.join vp010000000_0 (Blocks.join vp010000000_1 vp010000000_2))
private theorem bp0100000000 : Branch 0 (-2047761639/16000000 : ℚ) vp010000000 := by
  apply branch_left_normalized (c:=vp0100000000) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-2047761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/8000000 : ℚ) by norm_num]
  exact coverp0100000000
private noncomputable def ep0100000001_0 : Blocks := edgeBlocks% "full/vectors/0100000001-E-0000.bin"
private noncomputable def ep0100000001_1 : Blocks := edgeBlocks% "full/vectors/0100000001-E-0001.bin"
private noncomputable def ep0100000001_2 : Blocks := edgeBlocks% "full/vectors/0100000001-E-0002.bin"
noncomputable def ep0100000001 : Blocks := (Blocks.join ep0100000001_0 (Blocks.join ep0100000001_1 ep0100000001_2))
private theorem idp0100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000000.list =
    C ((2:ℤ)^412) * horner X vp0100000001.list + horner X ep0100000001.list := by
  exact edge_identity (B := (2:ℤ)^649) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100000001 : Branch 1 (-2047761639/16000000 : ℚ) vp010000000 := by
  apply branch_checked idp0100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2055761639/8000000 : ℚ) by norm_num]
  exact coverp0100000001
theorem coverp010000000 : Covers (-2047761639/16000000 : ℚ) vp010000000 := join_branches bp0100000000 bp0100000001
private noncomputable def vp01000000_0 : Blocks := edgeBlocks% "full/vectors/01000000-V-0000.bin"
private noncomputable def vp01000000_1 : Blocks := edgeBlocks% "full/vectors/01000000-V-0001.bin"
private noncomputable def vp01000000_2 : Blocks := edgeBlocks% "full/vectors/01000000-V-0002.bin"
private noncomputable def vp01000000_3 : Blocks := edgeBlocks% "full/vectors/01000000-V-0003.bin"
private noncomputable def vp01000000_4 : Blocks := edgeBlocks% "full/vectors/01000000-V-0004.bin"
private noncomputable def vp01000000_5 : Blocks := edgeBlocks% "full/vectors/01000000-V-0005.bin"
noncomputable def vp01000000 : Blocks := (Blocks.join (Blocks.join vp01000000_0 (Blocks.join vp01000000_1 vp01000000_2)) (Blocks.join vp01000000_3 (Blocks.join vp01000000_4 vp01000000_5)))
private theorem bp010000000 : Branch 0 (-2047761639/32000000 : ℚ) vp01000000 := by
  apply branch_left_normalized (c:=vp010000000) (k:=0) (m:=366) (by decide +kernel)
  rw [show 2*(-2047761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/16000000 : ℚ) by norm_num]
  exact coverp010000000
private noncomputable def ep010000001_0 : Blocks := edgeBlocks% "full/vectors/010000001-E-0000.bin"
private noncomputable def ep010000001_1 : Blocks := edgeBlocks% "full/vectors/010000001-E-0001.bin"
private noncomputable def ep010000001_2 : Blocks := edgeBlocks% "full/vectors/010000001-E-0002.bin"
private noncomputable def ep010000001_3 : Blocks := edgeBlocks% "full/vectors/010000001-E-0003.bin"
private noncomputable def ep010000001_4 : Blocks := edgeBlocks% "full/vectors/010000001-E-0004.bin"
private noncomputable def ep010000001_5 : Blocks := edgeBlocks% "full/vectors/010000001-E-0005.bin"
noncomputable def ep010000001 : Blocks := (Blocks.join (Blocks.join ep010000001_0 (Blocks.join ep010000001_1 ep010000001_2)) (Blocks.join ep010000001_3 (Blocks.join ep010000001_4 ep010000001_5)))
private theorem idp010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000000.list =
    C ((2:ℤ)^798) * horner X vp010000001.list + horner X ep010000001.list := by
  exact edge_identity (B := (2:ℤ)^1175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010000001 : Branch 1 (-2047761639/32000000 : ℚ) vp01000000 := by
  apply branch_checked idp010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2063761639/16000000 : ℚ) by norm_num]
  exact coverp010000001
theorem coverp01000000 : Covers (-2047761639/32000000 : ℚ) vp01000000 := join_branches bp010000000 bp010000001
private noncomputable def vp0100000_0 : Blocks := edgeBlocks% "full/vectors/0100000-V-0000.bin"
private noncomputable def vp0100000_1 : Blocks := edgeBlocks% "full/vectors/0100000-V-0001.bin"
private noncomputable def vp0100000_2 : Blocks := edgeBlocks% "full/vectors/0100000-V-0002.bin"
private noncomputable def vp0100000_3 : Blocks := edgeBlocks% "full/vectors/0100000-V-0003.bin"
private noncomputable def vp0100000_4 : Blocks := edgeBlocks% "full/vectors/0100000-V-0004.bin"
private noncomputable def vp0100000_5 : Blocks := edgeBlocks% "full/vectors/0100000-V-0005.bin"
private noncomputable def vp0100000_6 : Blocks := edgeBlocks% "full/vectors/0100000-V-0006.bin"
private noncomputable def vp0100000_7 : Blocks := edgeBlocks% "full/vectors/0100000-V-0007.bin"
private noncomputable def vp0100000_8 : Blocks := edgeBlocks% "full/vectors/0100000-V-0008.bin"
private noncomputable def vp0100000_9 : Blocks := edgeBlocks% "full/vectors/0100000-V-0009.bin"
private noncomputable def vp0100000_10 : Blocks := edgeBlocks% "full/vectors/0100000-V-0010.bin"
noncomputable def vp0100000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100000_0 vp0100000_1) (Blocks.join vp0100000_2 (Blocks.join vp0100000_3 vp0100000_4))) (Blocks.join (Blocks.join vp0100000_5 (Blocks.join vp0100000_6 vp0100000_7)) (Blocks.join vp0100000_8 (Blocks.join vp0100000_9 vp0100000_10))))
private theorem bp01000000 : Branch 0 (-2047761639/64000000 : ℚ) vp0100000 := by
  apply branch_left_normalized (c:=vp01000000) (k:=0) (m:=708) (by decide +kernel)
  rw [show 2*(-2047761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/32000000 : ℚ) by norm_num]
  exact coverp01000000
private noncomputable def ep01000001_0 : Blocks := edgeBlocks% "full/vectors/01000001-E-0000.bin"
private noncomputable def ep01000001_1 : Blocks := edgeBlocks% "full/vectors/01000001-E-0001.bin"
private noncomputable def ep01000001_2 : Blocks := edgeBlocks% "full/vectors/01000001-E-0002.bin"
private noncomputable def ep01000001_3 : Blocks := edgeBlocks% "full/vectors/01000001-E-0003.bin"
private noncomputable def ep01000001_4 : Blocks := edgeBlocks% "full/vectors/01000001-E-0004.bin"
private noncomputable def ep01000001_5 : Blocks := edgeBlocks% "full/vectors/01000001-E-0005.bin"
private noncomputable def ep01000001_6 : Blocks := edgeBlocks% "full/vectors/01000001-E-0006.bin"
private noncomputable def ep01000001_7 : Blocks := edgeBlocks% "full/vectors/01000001-E-0007.bin"
private noncomputable def ep01000001_8 : Blocks := edgeBlocks% "full/vectors/01000001-E-0008.bin"
private noncomputable def ep01000001_9 : Blocks := edgeBlocks% "full/vectors/01000001-E-0009.bin"
private noncomputable def ep01000001_10 : Blocks := edgeBlocks% "full/vectors/01000001-E-0010.bin"
noncomputable def ep01000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01000001_0 ep01000001_1) (Blocks.join ep01000001_2 (Blocks.join ep01000001_3 ep01000001_4))) (Blocks.join (Blocks.join ep01000001_5 (Blocks.join ep01000001_6 ep01000001_7)) (Blocks.join ep01000001_8 (Blocks.join ep01000001_9 ep01000001_10))))
private theorem idp01000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100000.list =
    C ((2:ℤ)^1565) * horner X vp01000001.list + horner X ep01000001.list := by
  exact edge_identity (B := (2:ℤ)^2214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000001 : Branch 1 (-2047761639/64000000 : ℚ) vp0100000 := by
  apply branch_checked idp01000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2079761639/32000000 : ℚ) by norm_num]
  exact coverp01000001
theorem coverp0100000 : Covers (-2047761639/64000000 : ℚ) vp0100000 := join_branches bp01000000 bp01000001
private noncomputable def vp010000_0 : Blocks := edgeBlocks% "full/vectors/010000-V-0000.bin"
private noncomputable def vp010000_1 : Blocks := edgeBlocks% "full/vectors/010000-V-0001.bin"
private noncomputable def vp010000_2 : Blocks := edgeBlocks% "full/vectors/010000-V-0002.bin"
private noncomputable def vp010000_3 : Blocks := edgeBlocks% "full/vectors/010000-V-0003.bin"
private noncomputable def vp010000_4 : Blocks := edgeBlocks% "full/vectors/010000-V-0004.bin"
private noncomputable def vp010000_5 : Blocks := edgeBlocks% "full/vectors/010000-V-0005.bin"
private noncomputable def vp010000_6 : Blocks := edgeBlocks% "full/vectors/010000-V-0006.bin"
private noncomputable def vp010000_7 : Blocks := edgeBlocks% "full/vectors/010000-V-0007.bin"
private noncomputable def vp010000_8 : Blocks := edgeBlocks% "full/vectors/010000-V-0008.bin"
private noncomputable def vp010000_9 : Blocks := edgeBlocks% "full/vectors/010000-V-0009.bin"
private noncomputable def vp010000_10 : Blocks := edgeBlocks% "full/vectors/010000-V-0010.bin"
private noncomputable def vp010000_11 : Blocks := edgeBlocks% "full/vectors/010000-V-0011.bin"
private noncomputable def vp010000_12 : Blocks := edgeBlocks% "full/vectors/010000-V-0012.bin"
private noncomputable def vp010000_13 : Blocks := edgeBlocks% "full/vectors/010000-V-0013.bin"
private noncomputable def vp010000_14 : Blocks := edgeBlocks% "full/vectors/010000-V-0014.bin"
private noncomputable def vp010000_15 : Blocks := edgeBlocks% "full/vectors/010000-V-0015.bin"
private noncomputable def vp010000_16 : Blocks := edgeBlocks% "full/vectors/010000-V-0016.bin"
private noncomputable def vp010000_17 : Blocks := edgeBlocks% "full/vectors/010000-V-0017.bin"
private noncomputable def vp010000_18 : Blocks := edgeBlocks% "full/vectors/010000-V-0018.bin"
private noncomputable def vp010000_19 : Blocks := edgeBlocks% "full/vectors/010000-V-0019.bin"
private noncomputable def vp010000_20 : Blocks := edgeBlocks% "full/vectors/010000-V-0020.bin"
noncomputable def vp010000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010000_0 vp010000_1) (Blocks.join vp010000_2 (Blocks.join vp010000_3 vp010000_4))) (Blocks.join (Blocks.join vp010000_5 vp010000_6) (Blocks.join vp010000_7 (Blocks.join vp010000_8 vp010000_9)))) (Blocks.join (Blocks.join (Blocks.join vp010000_10 vp010000_11) (Blocks.join vp010000_12 (Blocks.join vp010000_13 vp010000_14))) (Blocks.join (Blocks.join vp010000_15 (Blocks.join vp010000_16 vp010000_17)) (Blocks.join vp010000_18 (Blocks.join vp010000_19 vp010000_20)))))
private theorem bp0100000 : Branch 0 (-2047761639/128000000 : ℚ) vp010000 := by
  apply branch_left_normalized (c:=vp0100000) (k:=0) (m:=1382) (by decide +kernel)
  rw [show 2*(-2047761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/64000000 : ℚ) by norm_num]
  exact coverp0100000
private noncomputable def ep0100001_0 : Blocks := edgeBlocks% "full/vectors/0100001-E-0000.bin"
private noncomputable def ep0100001_1 : Blocks := edgeBlocks% "full/vectors/0100001-E-0001.bin"
private noncomputable def ep0100001_2 : Blocks := edgeBlocks% "full/vectors/0100001-E-0002.bin"
private noncomputable def ep0100001_3 : Blocks := edgeBlocks% "full/vectors/0100001-E-0003.bin"
private noncomputable def ep0100001_4 : Blocks := edgeBlocks% "full/vectors/0100001-E-0004.bin"
private noncomputable def ep0100001_5 : Blocks := edgeBlocks% "full/vectors/0100001-E-0005.bin"
private noncomputable def ep0100001_6 : Blocks := edgeBlocks% "full/vectors/0100001-E-0006.bin"
private noncomputable def ep0100001_7 : Blocks := edgeBlocks% "full/vectors/0100001-E-0007.bin"
private noncomputable def ep0100001_8 : Blocks := edgeBlocks% "full/vectors/0100001-E-0008.bin"
private noncomputable def ep0100001_9 : Blocks := edgeBlocks% "full/vectors/0100001-E-0009.bin"
private noncomputable def ep0100001_10 : Blocks := edgeBlocks% "full/vectors/0100001-E-0010.bin"
private noncomputable def ep0100001_11 : Blocks := edgeBlocks% "full/vectors/0100001-E-0011.bin"
private noncomputable def ep0100001_12 : Blocks := edgeBlocks% "full/vectors/0100001-E-0012.bin"
private noncomputable def ep0100001_13 : Blocks := edgeBlocks% "full/vectors/0100001-E-0013.bin"
private noncomputable def ep0100001_14 : Blocks := edgeBlocks% "full/vectors/0100001-E-0014.bin"
private noncomputable def ep0100001_15 : Blocks := edgeBlocks% "full/vectors/0100001-E-0015.bin"
private noncomputable def ep0100001_16 : Blocks := edgeBlocks% "full/vectors/0100001-E-0016.bin"
private noncomputable def ep0100001_17 : Blocks := edgeBlocks% "full/vectors/0100001-E-0017.bin"
private noncomputable def ep0100001_18 : Blocks := edgeBlocks% "full/vectors/0100001-E-0018.bin"
private noncomputable def ep0100001_19 : Blocks := edgeBlocks% "full/vectors/0100001-E-0019.bin"
private noncomputable def ep0100001_20 : Blocks := edgeBlocks% "full/vectors/0100001-E-0020.bin"
noncomputable def ep0100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0100001_0 ep0100001_1) (Blocks.join ep0100001_2 (Blocks.join ep0100001_3 ep0100001_4))) (Blocks.join (Blocks.join ep0100001_5 ep0100001_6) (Blocks.join ep0100001_7 (Blocks.join ep0100001_8 ep0100001_9)))) (Blocks.join (Blocks.join (Blocks.join ep0100001_10 ep0100001_11) (Blocks.join ep0100001_12 (Blocks.join ep0100001_13 ep0100001_14))) (Blocks.join (Blocks.join ep0100001_15 (Blocks.join ep0100001_16 ep0100001_17)) (Blocks.join ep0100001_18 (Blocks.join ep0100001_19 ep0100001_20)))))
private theorem idp0100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010000.list =
    C ((2:ℤ)^3052) * horner X vp0100001.list + horner X ep0100001.list := by
  exact edge_identity (B := (2:ℤ)^4238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100001 : Branch 1 (-2047761639/128000000 : ℚ) vp010000 := by
  apply branch_checked idp0100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2111761639/64000000 : ℚ) by norm_num]
  exact coverp0100001
theorem coverp010000 : Covers (-2047761639/128000000 : ℚ) vp010000 := join_branches bp0100000 bp0100001
private noncomputable def vp01000_0 : Blocks := edgeBlocks% "full/vectors/01000-V-0000.bin"
private noncomputable def vp01000_1 : Blocks := edgeBlocks% "full/vectors/01000-V-0001.bin"
private noncomputable def vp01000_2 : Blocks := edgeBlocks% "full/vectors/01000-V-0002.bin"
private noncomputable def vp01000_3 : Blocks := edgeBlocks% "full/vectors/01000-V-0003.bin"
private noncomputable def vp01000_4 : Blocks := edgeBlocks% "full/vectors/01000-V-0004.bin"
private noncomputable def vp01000_5 : Blocks := edgeBlocks% "full/vectors/01000-V-0005.bin"
private noncomputable def vp01000_6 : Blocks := edgeBlocks% "full/vectors/01000-V-0006.bin"
private noncomputable def vp01000_7 : Blocks := edgeBlocks% "full/vectors/01000-V-0007.bin"
private noncomputable def vp01000_8 : Blocks := edgeBlocks% "full/vectors/01000-V-0008.bin"
private noncomputable def vp01000_9 : Blocks := edgeBlocks% "full/vectors/01000-V-0009.bin"
private noncomputable def vp01000_10 : Blocks := edgeBlocks% "full/vectors/01000-V-0010.bin"
private noncomputable def vp01000_11 : Blocks := edgeBlocks% "full/vectors/01000-V-0011.bin"
private noncomputable def vp01000_12 : Blocks := edgeBlocks% "full/vectors/01000-V-0012.bin"
private noncomputable def vp01000_13 : Blocks := edgeBlocks% "full/vectors/01000-V-0013.bin"
private noncomputable def vp01000_14 : Blocks := edgeBlocks% "full/vectors/01000-V-0014.bin"
private noncomputable def vp01000_15 : Blocks := edgeBlocks% "full/vectors/01000-V-0015.bin"
private noncomputable def vp01000_16 : Blocks := edgeBlocks% "full/vectors/01000-V-0016.bin"
private noncomputable def vp01000_17 : Blocks := edgeBlocks% "full/vectors/01000-V-0017.bin"
private noncomputable def vp01000_18 : Blocks := edgeBlocks% "full/vectors/01000-V-0018.bin"
private noncomputable def vp01000_19 : Blocks := edgeBlocks% "full/vectors/01000-V-0019.bin"
private noncomputable def vp01000_20 : Blocks := edgeBlocks% "full/vectors/01000-V-0020.bin"
private noncomputable def vp01000_21 : Blocks := edgeBlocks% "full/vectors/01000-V-0021.bin"
private noncomputable def vp01000_22 : Blocks := edgeBlocks% "full/vectors/01000-V-0022.bin"
private noncomputable def vp01000_23 : Blocks := edgeBlocks% "full/vectors/01000-V-0023.bin"
private noncomputable def vp01000_24 : Blocks := edgeBlocks% "full/vectors/01000-V-0024.bin"
private noncomputable def vp01000_25 : Blocks := edgeBlocks% "full/vectors/01000-V-0025.bin"
private noncomputable def vp01000_26 : Blocks := edgeBlocks% "full/vectors/01000-V-0026.bin"
private noncomputable def vp01000_27 : Blocks := edgeBlocks% "full/vectors/01000-V-0027.bin"
private noncomputable def vp01000_28 : Blocks := edgeBlocks% "full/vectors/01000-V-0028.bin"
private noncomputable def vp01000_29 : Blocks := edgeBlocks% "full/vectors/01000-V-0029.bin"
private noncomputable def vp01000_30 : Blocks := edgeBlocks% "full/vectors/01000-V-0030.bin"
private noncomputable def vp01000_31 : Blocks := edgeBlocks% "full/vectors/01000-V-0031.bin"
private noncomputable def vp01000_32 : Blocks := edgeBlocks% "full/vectors/01000-V-0032.bin"
private noncomputable def vp01000_33 : Blocks := edgeBlocks% "full/vectors/01000-V-0033.bin"
private noncomputable def vp01000_34 : Blocks := edgeBlocks% "full/vectors/01000-V-0034.bin"
private noncomputable def vp01000_35 : Blocks := edgeBlocks% "full/vectors/01000-V-0035.bin"
private noncomputable def vp01000_36 : Blocks := edgeBlocks% "full/vectors/01000-V-0036.bin"
private noncomputable def vp01000_37 : Blocks := edgeBlocks% "full/vectors/01000-V-0037.bin"
private noncomputable def vp01000_38 : Blocks := edgeBlocks% "full/vectors/01000-V-0038.bin"
private noncomputable def vp01000_39 : Blocks := edgeBlocks% "full/vectors/01000-V-0039.bin"
noncomputable def vp01000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01000_0 vp01000_1) (Blocks.join vp01000_2 (Blocks.join vp01000_3 vp01000_4))) (Blocks.join (Blocks.join vp01000_5 vp01000_6) (Blocks.join vp01000_7 (Blocks.join vp01000_8 vp01000_9)))) (Blocks.join (Blocks.join (Blocks.join vp01000_10 vp01000_11) (Blocks.join vp01000_12 (Blocks.join vp01000_13 vp01000_14))) (Blocks.join (Blocks.join vp01000_15 vp01000_16) (Blocks.join vp01000_17 (Blocks.join vp01000_18 vp01000_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01000_20 vp01000_21) (Blocks.join vp01000_22 (Blocks.join vp01000_23 vp01000_24))) (Blocks.join (Blocks.join vp01000_25 vp01000_26) (Blocks.join vp01000_27 (Blocks.join vp01000_28 vp01000_29)))) (Blocks.join (Blocks.join (Blocks.join vp01000_30 vp01000_31) (Blocks.join vp01000_32 (Blocks.join vp01000_33 vp01000_34))) (Blocks.join (Blocks.join vp01000_35 vp01000_36) (Blocks.join vp01000_37 (Blocks.join vp01000_38 vp01000_39))))))
private theorem bp010000 : Branch 0 (-2047761639/256000000 : ℚ) vp01000 := by
  apply branch_left_normalized (c:=vp010000) (k:=0) (m:=2685) (by decide +kernel)
  rw [show 2*(-2047761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/128000000 : ℚ) by norm_num]
  exact coverp010000
private noncomputable def ep010001_0 : Blocks := edgeBlocks% "full/vectors/010001-E-0000.bin"
private noncomputable def ep010001_1 : Blocks := edgeBlocks% "full/vectors/010001-E-0001.bin"
private noncomputable def ep010001_2 : Blocks := edgeBlocks% "full/vectors/010001-E-0002.bin"
private noncomputable def ep010001_3 : Blocks := edgeBlocks% "full/vectors/010001-E-0003.bin"
private noncomputable def ep010001_4 : Blocks := edgeBlocks% "full/vectors/010001-E-0004.bin"
private noncomputable def ep010001_5 : Blocks := edgeBlocks% "full/vectors/010001-E-0005.bin"
private noncomputable def ep010001_6 : Blocks := edgeBlocks% "full/vectors/010001-E-0006.bin"
private noncomputable def ep010001_7 : Blocks := edgeBlocks% "full/vectors/010001-E-0007.bin"
private noncomputable def ep010001_8 : Blocks := edgeBlocks% "full/vectors/010001-E-0008.bin"
private noncomputable def ep010001_9 : Blocks := edgeBlocks% "full/vectors/010001-E-0009.bin"
private noncomputable def ep010001_10 : Blocks := edgeBlocks% "full/vectors/010001-E-0010.bin"
private noncomputable def ep010001_11 : Blocks := edgeBlocks% "full/vectors/010001-E-0011.bin"
private noncomputable def ep010001_12 : Blocks := edgeBlocks% "full/vectors/010001-E-0012.bin"
private noncomputable def ep010001_13 : Blocks := edgeBlocks% "full/vectors/010001-E-0013.bin"
private noncomputable def ep010001_14 : Blocks := edgeBlocks% "full/vectors/010001-E-0014.bin"
private noncomputable def ep010001_15 : Blocks := edgeBlocks% "full/vectors/010001-E-0015.bin"
private noncomputable def ep010001_16 : Blocks := edgeBlocks% "full/vectors/010001-E-0016.bin"
private noncomputable def ep010001_17 : Blocks := edgeBlocks% "full/vectors/010001-E-0017.bin"
private noncomputable def ep010001_18 : Blocks := edgeBlocks% "full/vectors/010001-E-0018.bin"
private noncomputable def ep010001_19 : Blocks := edgeBlocks% "full/vectors/010001-E-0019.bin"
private noncomputable def ep010001_20 : Blocks := edgeBlocks% "full/vectors/010001-E-0020.bin"
private noncomputable def ep010001_21 : Blocks := edgeBlocks% "full/vectors/010001-E-0021.bin"
private noncomputable def ep010001_22 : Blocks := edgeBlocks% "full/vectors/010001-E-0022.bin"
private noncomputable def ep010001_23 : Blocks := edgeBlocks% "full/vectors/010001-E-0023.bin"
private noncomputable def ep010001_24 : Blocks := edgeBlocks% "full/vectors/010001-E-0024.bin"
private noncomputable def ep010001_25 : Blocks := edgeBlocks% "full/vectors/010001-E-0025.bin"
private noncomputable def ep010001_26 : Blocks := edgeBlocks% "full/vectors/010001-E-0026.bin"
private noncomputable def ep010001_27 : Blocks := edgeBlocks% "full/vectors/010001-E-0027.bin"
private noncomputable def ep010001_28 : Blocks := edgeBlocks% "full/vectors/010001-E-0028.bin"
private noncomputable def ep010001_29 : Blocks := edgeBlocks% "full/vectors/010001-E-0029.bin"
private noncomputable def ep010001_30 : Blocks := edgeBlocks% "full/vectors/010001-E-0030.bin"
private noncomputable def ep010001_31 : Blocks := edgeBlocks% "full/vectors/010001-E-0031.bin"
private noncomputable def ep010001_32 : Blocks := edgeBlocks% "full/vectors/010001-E-0032.bin"
private noncomputable def ep010001_33 : Blocks := edgeBlocks% "full/vectors/010001-E-0033.bin"
private noncomputable def ep010001_34 : Blocks := edgeBlocks% "full/vectors/010001-E-0034.bin"
private noncomputable def ep010001_35 : Blocks := edgeBlocks% "full/vectors/010001-E-0035.bin"
private noncomputable def ep010001_36 : Blocks := edgeBlocks% "full/vectors/010001-E-0036.bin"
private noncomputable def ep010001_37 : Blocks := edgeBlocks% "full/vectors/010001-E-0037.bin"
private noncomputable def ep010001_38 : Blocks := edgeBlocks% "full/vectors/010001-E-0038.bin"
private noncomputable def ep010001_39 : Blocks := edgeBlocks% "full/vectors/010001-E-0039.bin"
noncomputable def ep010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010001_0 ep010001_1) (Blocks.join ep010001_2 (Blocks.join ep010001_3 ep010001_4))) (Blocks.join (Blocks.join ep010001_5 ep010001_6) (Blocks.join ep010001_7 (Blocks.join ep010001_8 ep010001_9)))) (Blocks.join (Blocks.join (Blocks.join ep010001_10 ep010001_11) (Blocks.join ep010001_12 (Blocks.join ep010001_13 ep010001_14))) (Blocks.join (Blocks.join ep010001_15 ep010001_16) (Blocks.join ep010001_17 (Blocks.join ep010001_18 ep010001_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010001_20 ep010001_21) (Blocks.join ep010001_22 (Blocks.join ep010001_23 ep010001_24))) (Blocks.join (Blocks.join ep010001_25 ep010001_26) (Blocks.join ep010001_27 (Blocks.join ep010001_28 ep010001_29)))) (Blocks.join (Blocks.join (Blocks.join ep010001_30 ep010001_31) (Blocks.join ep010001_32 (Blocks.join ep010001_33 ep010001_34))) (Blocks.join (Blocks.join ep010001_35 ep010001_36) (Blocks.join ep010001_37 (Blocks.join ep010001_38 ep010001_39))))))
private def ptsp010001 : List ℤ := [((2:ℤ)^2344+0),((2:ℤ)^2344+1),((2:ℤ)^2344+2),((2:ℤ)^2344+3)]
private theorem boundp010001 : 2^vp01000.size*absSum vp01000.list + ((2:ℤ)^5864*absSum vp010001.list+absSum ep010001.list) < (2:ℤ)^8081 := by decide +kernel
private theorem pointp010001_0 : fastHom 1 ((2:ℤ)^2344+0) vp01000 = ((2:ℤ)^5864)*vp010001.subst ((2:ℤ)^2344+0)+ep010001.subst ((2:ℤ)^2344+0) := by decide +kernel
private theorem pointp010001_1 : fastHom 1 ((2:ℤ)^2344+1) vp01000 = ((2:ℤ)^5864)*vp010001.subst ((2:ℤ)^2344+1)+ep010001.subst ((2:ℤ)^2344+1) := by decide +kernel
private theorem pointp010001_2 : fastHom 1 ((2:ℤ)^2344+2) vp01000 = ((2:ℤ)^5864)*vp010001.subst ((2:ℤ)^2344+2)+ep010001.subst ((2:ℤ)^2344+2) := by decide +kernel
private theorem pointp010001_3 : fastHom 1 ((2:ℤ)^2344+3) vp01000 = ((2:ℤ)^5864)*vp010001.subst ((2:ℤ)^2344+3)+ep010001.subst ((2:ℤ)^2344+3) := by decide +kernel
private theorem checkp010001 (x:ℤ) (hx:x ∈ ptsp010001) : fastHom 1 x vp01000 = ((2:ℤ)^5864)*vp010001.subst x+ep010001.subst x := by
  simp only [ptsp010001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp010001_0
  · exact pointp010001_1
  · exact pointp010001_2
  · exact pointp010001_3
private theorem idp010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000.list =
    C ((2:ℤ)^5864) * horner X vp010001.list + horner X ep010001.list := by
  apply edge_identity (B := (2:ℤ)^8081) (by decide) (by positivity) (by positivity) boundp010001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp010001 (by decide +kernel)
  · have h : ptsp010001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp010001.trans_le (by decide +kernel)
  · exact checkp010001
private theorem bp010001 : Branch 1 (-2047761639/256000000 : ℚ) vp01000 := by
  apply branch_checked idp010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-2175761639/128000000 : ℚ) by norm_num]
  exact coverp010001
theorem coverp01000 : Covers (-2047761639/256000000 : ℚ) vp01000 := join_branches bp010000 bp010001
end NextProof.EdgeFull

