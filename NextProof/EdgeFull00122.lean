import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00121

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp011000111111_0 : Blocks := edgeBlocks% "full/vectors/011000111111-V-0000.bin"
noncomputable def vp011000111111 : Blocks := vp011000111111_0
theorem coverp011000111111 : Covers (-3197761639/2000000 : ℚ) vp011000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp011000111110_0 : Blocks := edgeBlocks% "full/vectors/011000111110-V-0000.bin"
noncomputable def vp011000111110 : Blocks := vp011000111110_0
theorem coverp011000111110 : Covers (-3195761639/2000000 : ℚ) vp011000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100011111_0 : Blocks := edgeBlocks% "full/vectors/01100011111-V-0000.bin"
noncomputable def vp01100011111 : Blocks := vp01100011111_0
private theorem bp011000111110 : Branch 0 (-3195761639/4000000 : ℚ) vp01100011111 := by
  apply branch_left_normalized (c:=vp011000111110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3195761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3195761639/2000000 : ℚ) by norm_num]
  exact coverp011000111110
private noncomputable def ep011000111111_0 : Blocks := edgeBlocks% "full/vectors/011000111111-E-0000.bin"
noncomputable def ep011000111111 : Blocks := ep011000111111_0
private theorem idp011000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100011111.list =
    C ((2:ℤ)^99) * horner X vp011000111111.list + horner X ep011000111111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000111111 : Branch 1 (-3195761639/4000000 : ℚ) vp01100011111 := by
  apply branch_checked idp011000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3195761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3197761639/2000000 : ℚ) by norm_num]
  exact coverp011000111111
theorem coverp01100011111 : Covers (-3195761639/4000000 : ℚ) vp01100011111 := join_branches bp011000111110 bp011000111111
private noncomputable def vp01100011110_0 : Blocks := edgeBlocks% "full/vectors/01100011110-V-0000.bin"
noncomputable def vp01100011110 : Blocks := vp01100011110_0
theorem coverp01100011110 : Covers (-3191761639/4000000 : ℚ) vp01100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001111_0 : Blocks := edgeBlocks% "full/vectors/0110001111-V-0000.bin"
private noncomputable def vp0110001111_1 : Blocks := edgeBlocks% "full/vectors/0110001111-V-0001.bin"
noncomputable def vp0110001111 : Blocks := (Blocks.join vp0110001111_0 vp0110001111_1)
private theorem bp01100011110 : Branch 0 (-3191761639/8000000 : ℚ) vp0110001111 := by
  apply branch_left_normalized (c:=vp01100011110) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3191761639/4000000 : ℚ) by norm_num]
  exact coverp01100011110
private noncomputable def ep01100011111_0 : Blocks := edgeBlocks% "full/vectors/01100011111-E-0000.bin"
private noncomputable def ep01100011111_1 : Blocks := edgeBlocks% "full/vectors/01100011111-E-0001.bin"
noncomputable def ep01100011111 : Blocks := (Blocks.join ep01100011111_0 ep01100011111_1)
private theorem idp01100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001111.list =
    C ((2:ℤ)^179) * horner X vp01100011111.list + horner X ep01100011111.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100011111 : Branch 1 (-3191761639/8000000 : ℚ) vp0110001111 := by
  apply branch_checked idp01100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3195761639/4000000 : ℚ) by norm_num]
  exact coverp01100011111
theorem coverp0110001111 : Covers (-3191761639/8000000 : ℚ) vp0110001111 := join_branches bp01100011110 bp01100011111
private noncomputable def vp01100011101_0 : Blocks := edgeBlocks% "full/vectors/01100011101-V-0000.bin"
noncomputable def vp01100011101 : Blocks := vp01100011101_0
theorem coverp01100011101 : Covers (-3187761639/4000000 : ℚ) vp01100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp01100011100_0 : Blocks := edgeBlocks% "full/vectors/01100011100-V-0000.bin"
noncomputable def vp01100011100 : Blocks := vp01100011100_0
theorem coverp01100011100 : Covers (-3183761639/4000000 : ℚ) vp01100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001110_0 : Blocks := edgeBlocks% "full/vectors/0110001110-V-0000.bin"
private noncomputable def vp0110001110_1 : Blocks := edgeBlocks% "full/vectors/0110001110-V-0001.bin"
noncomputable def vp0110001110 : Blocks := (Blocks.join vp0110001110_0 vp0110001110_1)
private theorem bp01100011100 : Branch 0 (-3183761639/8000000 : ℚ) vp0110001110 := by
  apply branch_left_normalized (c:=vp01100011100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3183761639/4000000 : ℚ) by norm_num]
  exact coverp01100011100
private noncomputable def ep01100011101_0 : Blocks := edgeBlocks% "full/vectors/01100011101-E-0000.bin"
private noncomputable def ep01100011101_1 : Blocks := edgeBlocks% "full/vectors/01100011101-E-0001.bin"
noncomputable def ep01100011101 : Blocks := (Blocks.join ep01100011101_0 ep01100011101_1)
private theorem idp01100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001110.list =
    C ((2:ℤ)^179) * horner X vp01100011101.list + horner X ep01100011101.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100011101 : Branch 1 (-3183761639/8000000 : ℚ) vp0110001110 := by
  apply branch_checked idp01100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3187761639/4000000 : ℚ) by norm_num]
  exact coverp01100011101
theorem coverp0110001110 : Covers (-3183761639/8000000 : ℚ) vp0110001110 := join_branches bp01100011100 bp01100011101
private noncomputable def vp011000111_0 : Blocks := edgeBlocks% "full/vectors/011000111-V-0000.bin"
private noncomputable def vp011000111_1 : Blocks := edgeBlocks% "full/vectors/011000111-V-0001.bin"
private noncomputable def vp011000111_2 : Blocks := edgeBlocks% "full/vectors/011000111-V-0002.bin"
noncomputable def vp011000111 : Blocks := (Blocks.join vp011000111_0 (Blocks.join vp011000111_1 vp011000111_2))
private theorem bp0110001110 : Branch 0 (-3183761639/16000000 : ℚ) vp011000111 := by
  apply branch_left_normalized (c:=vp0110001110) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3183761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3183761639/8000000 : ℚ) by norm_num]
  exact coverp0110001110
private noncomputable def ep0110001111_0 : Blocks := edgeBlocks% "full/vectors/0110001111-E-0000.bin"
private noncomputable def ep0110001111_1 : Blocks := edgeBlocks% "full/vectors/0110001111-E-0001.bin"
private noncomputable def ep0110001111_2 : Blocks := edgeBlocks% "full/vectors/0110001111-E-0002.bin"
noncomputable def ep0110001111 : Blocks := (Blocks.join ep0110001111_0 (Blocks.join ep0110001111_1 ep0110001111_2))
private theorem idp0110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000111.list =
    C ((2:ℤ)^340) * horner X vp0110001111.list + horner X ep0110001111.list := by
  exact edge_identity (B := (2:ℤ)^537) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110001111 : Branch 1 (-3183761639/16000000 : ℚ) vp011000111 := by
  apply branch_checked idp0110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3183761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3191761639/8000000 : ℚ) by norm_num]
  exact coverp0110001111
theorem coverp011000111 : Covers (-3183761639/16000000 : ℚ) vp011000111 := join_branches bp0110001110 bp0110001111
private noncomputable def vp01100011011_0 : Blocks := edgeBlocks% "full/vectors/01100011011-V-0000.bin"
noncomputable def vp01100011011 : Blocks := vp01100011011_0
theorem coverp01100011011 : Covers (-3179761639/4000000 : ℚ) vp01100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp01100011010_0 : Blocks := edgeBlocks% "full/vectors/01100011010-V-0000.bin"
noncomputable def vp01100011010 : Blocks := vp01100011010_0
theorem coverp01100011010 : Covers (-3175761639/4000000 : ℚ) vp01100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001101_0 : Blocks := edgeBlocks% "full/vectors/0110001101-V-0000.bin"
private noncomputable def vp0110001101_1 : Blocks := edgeBlocks% "full/vectors/0110001101-V-0001.bin"
noncomputable def vp0110001101 : Blocks := (Blocks.join vp0110001101_0 vp0110001101_1)
private theorem bp01100011010 : Branch 0 (-3175761639/8000000 : ℚ) vp0110001101 := by
  apply branch_left_normalized (c:=vp01100011010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3175761639/4000000 : ℚ) by norm_num]
  exact coverp01100011010
private noncomputable def ep01100011011_0 : Blocks := edgeBlocks% "full/vectors/01100011011-E-0000.bin"
private noncomputable def ep01100011011_1 : Blocks := edgeBlocks% "full/vectors/01100011011-E-0001.bin"
noncomputable def ep01100011011 : Blocks := (Blocks.join ep01100011011_0 ep01100011011_1)
private theorem idp01100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001101.list =
    C ((2:ℤ)^180) * horner X vp01100011011.list + horner X ep01100011011.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100011011 : Branch 1 (-3175761639/8000000 : ℚ) vp0110001101 := by
  apply branch_checked idp01100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3179761639/4000000 : ℚ) by norm_num]
  exact coverp01100011011
theorem coverp0110001101 : Covers (-3175761639/8000000 : ℚ) vp0110001101 := join_branches bp01100011010 bp01100011011
private noncomputable def vp01100011001_0 : Blocks := edgeBlocks% "full/vectors/01100011001-V-0000.bin"
noncomputable def vp01100011001 : Blocks := vp01100011001_0
theorem coverp01100011001 : Covers (-3171761639/4000000 : ℚ) vp01100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp01100011000_0 : Blocks := edgeBlocks% "full/vectors/01100011000-V-0000.bin"
noncomputable def vp01100011000 : Blocks := vp01100011000_0
theorem coverp01100011000 : Covers (-3167761639/4000000 : ℚ) vp01100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001100_0 : Blocks := edgeBlocks% "full/vectors/0110001100-V-0000.bin"
private noncomputable def vp0110001100_1 : Blocks := edgeBlocks% "full/vectors/0110001100-V-0001.bin"
noncomputable def vp0110001100 : Blocks := (Blocks.join vp0110001100_0 vp0110001100_1)
private theorem bp01100011000 : Branch 0 (-3167761639/8000000 : ℚ) vp0110001100 := by
  apply branch_left_normalized (c:=vp01100011000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3167761639/4000000 : ℚ) by norm_num]
  exact coverp01100011000
private noncomputable def ep01100011001_0 : Blocks := edgeBlocks% "full/vectors/01100011001-E-0000.bin"
private noncomputable def ep01100011001_1 : Blocks := edgeBlocks% "full/vectors/01100011001-E-0001.bin"
noncomputable def ep01100011001 : Blocks := (Blocks.join ep01100011001_0 ep01100011001_1)
private theorem idp01100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001100.list =
    C ((2:ℤ)^179) * horner X vp01100011001.list + horner X ep01100011001.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100011001 : Branch 1 (-3167761639/8000000 : ℚ) vp0110001100 := by
  apply branch_checked idp01100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3171761639/4000000 : ℚ) by norm_num]
  exact coverp01100011001
theorem coverp0110001100 : Covers (-3167761639/8000000 : ℚ) vp0110001100 := join_branches bp01100011000 bp01100011001
private noncomputable def vp011000110_0 : Blocks := edgeBlocks% "full/vectors/011000110-V-0000.bin"
private noncomputable def vp011000110_1 : Blocks := edgeBlocks% "full/vectors/011000110-V-0001.bin"
private noncomputable def vp011000110_2 : Blocks := edgeBlocks% "full/vectors/011000110-V-0002.bin"
noncomputable def vp011000110 : Blocks := (Blocks.join vp011000110_0 (Blocks.join vp011000110_1 vp011000110_2))
private theorem bp0110001100 : Branch 0 (-3167761639/16000000 : ℚ) vp011000110 := by
  apply branch_left_normalized (c:=vp0110001100) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-3167761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3167761639/8000000 : ℚ) by norm_num]
  exact coverp0110001100
private noncomputable def ep0110001101_0 : Blocks := edgeBlocks% "full/vectors/0110001101-E-0000.bin"
private noncomputable def ep0110001101_1 : Blocks := edgeBlocks% "full/vectors/0110001101-E-0001.bin"
private noncomputable def ep0110001101_2 : Blocks := edgeBlocks% "full/vectors/0110001101-E-0002.bin"
noncomputable def ep0110001101 : Blocks := (Blocks.join ep0110001101_0 (Blocks.join ep0110001101_1 ep0110001101_2))
private theorem idp0110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000110.list =
    C ((2:ℤ)^342) * horner X vp0110001101.list + horner X ep0110001101.list := by
  exact edge_identity (B := (2:ℤ)^536) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110001101 : Branch 1 (-3167761639/16000000 : ℚ) vp011000110 := by
  apply branch_checked idp0110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3167761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3175761639/8000000 : ℚ) by norm_num]
  exact coverp0110001101
theorem coverp011000110 : Covers (-3167761639/16000000 : ℚ) vp011000110 := join_branches bp0110001100 bp0110001101
private noncomputable def vp01100011_0 : Blocks := edgeBlocks% "full/vectors/01100011-V-0000.bin"
private noncomputable def vp01100011_1 : Blocks := edgeBlocks% "full/vectors/01100011-V-0001.bin"
private noncomputable def vp01100011_2 : Blocks := edgeBlocks% "full/vectors/01100011-V-0002.bin"
private noncomputable def vp01100011_3 : Blocks := edgeBlocks% "full/vectors/01100011-V-0003.bin"
private noncomputable def vp01100011_4 : Blocks := edgeBlocks% "full/vectors/01100011-V-0004.bin"
noncomputable def vp01100011 : Blocks := (Blocks.join (Blocks.join vp01100011_0 vp01100011_1) (Blocks.join vp01100011_2 (Blocks.join vp01100011_3 vp01100011_4)))
private theorem bp011000110 : Branch 0 (-3167761639/32000000 : ℚ) vp01100011 := by
  apply branch_left_normalized (c:=vp011000110) (k:=0) (m:=295) (by decide +kernel)
  rw [show 2*(-3167761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3167761639/16000000 : ℚ) by norm_num]
  exact coverp011000110
private noncomputable def ep011000111_0 : Blocks := edgeBlocks% "full/vectors/011000111-E-0000.bin"
private noncomputable def ep011000111_1 : Blocks := edgeBlocks% "full/vectors/011000111-E-0001.bin"
private noncomputable def ep011000111_2 : Blocks := edgeBlocks% "full/vectors/011000111-E-0002.bin"
private noncomputable def ep011000111_3 : Blocks := edgeBlocks% "full/vectors/011000111-E-0003.bin"
private noncomputable def ep011000111_4 : Blocks := edgeBlocks% "full/vectors/011000111-E-0004.bin"
noncomputable def ep011000111 : Blocks := (Blocks.join (Blocks.join ep011000111_0 ep011000111_1) (Blocks.join ep011000111_2 (Blocks.join ep011000111_3 ep011000111_4)))
private theorem idp011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100011.list =
    C ((2:ℤ)^662) * horner X vp011000111.list + horner X ep011000111.list := by
  exact edge_identity (B := (2:ℤ)^959) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000111 : Branch 1 (-3167761639/32000000 : ℚ) vp01100011 := by
  apply branch_checked idp011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3167761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3183761639/16000000 : ℚ) by norm_num]
  exact coverp011000111
theorem coverp01100011 : Covers (-3167761639/32000000 : ℚ) vp01100011 := join_branches bp011000110 bp011000111
private noncomputable def vp01100010111_0 : Blocks := edgeBlocks% "full/vectors/01100010111-V-0000.bin"
noncomputable def vp01100010111 : Blocks := vp01100010111_0
theorem coverp01100010111 : Covers (-3163761639/4000000 : ℚ) vp01100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp01100010110_0 : Blocks := edgeBlocks% "full/vectors/01100010110-V-0000.bin"
noncomputable def vp01100010110 : Blocks := vp01100010110_0
theorem coverp01100010110 : Covers (-3159761639/4000000 : ℚ) vp01100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001011_0 : Blocks := edgeBlocks% "full/vectors/0110001011-V-0000.bin"
private noncomputable def vp0110001011_1 : Blocks := edgeBlocks% "full/vectors/0110001011-V-0001.bin"
noncomputable def vp0110001011 : Blocks := (Blocks.join vp0110001011_0 vp0110001011_1)
private theorem bp01100010110 : Branch 0 (-3159761639/8000000 : ℚ) vp0110001011 := by
  apply branch_left_normalized (c:=vp01100010110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3159761639/4000000 : ℚ) by norm_num]
  exact coverp01100010110
private noncomputable def ep01100010111_0 : Blocks := edgeBlocks% "full/vectors/01100010111-E-0000.bin"
private noncomputable def ep01100010111_1 : Blocks := edgeBlocks% "full/vectors/01100010111-E-0001.bin"
noncomputable def ep01100010111 : Blocks := (Blocks.join ep01100010111_0 ep01100010111_1)
private theorem idp01100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001011.list =
    C ((2:ℤ)^182) * horner X vp01100010111.list + horner X ep01100010111.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100010111 : Branch 1 (-3159761639/8000000 : ℚ) vp0110001011 := by
  apply branch_checked idp01100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3163761639/4000000 : ℚ) by norm_num]
  exact coverp01100010111
theorem coverp0110001011 : Covers (-3159761639/8000000 : ℚ) vp0110001011 := join_branches bp01100010110 bp01100010111
private noncomputable def vp01100010101_0 : Blocks := edgeBlocks% "full/vectors/01100010101-V-0000.bin"
noncomputable def vp01100010101 : Blocks := vp01100010101_0
theorem coverp01100010101 : Covers (-3155761639/4000000 : ℚ) vp01100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp01100010100_0 : Blocks := edgeBlocks% "full/vectors/01100010100-V-0000.bin"
noncomputable def vp01100010100 : Blocks := vp01100010100_0
theorem coverp01100010100 : Covers (-3151761639/4000000 : ℚ) vp01100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001010_0 : Blocks := edgeBlocks% "full/vectors/0110001010-V-0000.bin"
private noncomputable def vp0110001010_1 : Blocks := edgeBlocks% "full/vectors/0110001010-V-0001.bin"
noncomputable def vp0110001010 : Blocks := (Blocks.join vp0110001010_0 vp0110001010_1)
private theorem bp01100010100 : Branch 0 (-3151761639/8000000 : ℚ) vp0110001010 := by
  apply branch_left_normalized (c:=vp01100010100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3151761639/4000000 : ℚ) by norm_num]
  exact coverp01100010100
private noncomputable def ep01100010101_0 : Blocks := edgeBlocks% "full/vectors/01100010101-E-0000.bin"
private noncomputable def ep01100010101_1 : Blocks := edgeBlocks% "full/vectors/01100010101-E-0001.bin"
noncomputable def ep01100010101 : Blocks := (Blocks.join ep01100010101_0 ep01100010101_1)
private theorem idp01100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001010.list =
    C ((2:ℤ)^182) * horner X vp01100010101.list + horner X ep01100010101.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100010101 : Branch 1 (-3151761639/8000000 : ℚ) vp0110001010 := by
  apply branch_checked idp01100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3155761639/4000000 : ℚ) by norm_num]
  exact coverp01100010101
theorem coverp0110001010 : Covers (-3151761639/8000000 : ℚ) vp0110001010 := join_branches bp01100010100 bp01100010101
private noncomputable def vp011000101_0 : Blocks := edgeBlocks% "full/vectors/011000101-V-0000.bin"
private noncomputable def vp011000101_1 : Blocks := edgeBlocks% "full/vectors/011000101-V-0001.bin"
private noncomputable def vp011000101_2 : Blocks := edgeBlocks% "full/vectors/011000101-V-0002.bin"
noncomputable def vp011000101 : Blocks := (Blocks.join vp011000101_0 (Blocks.join vp011000101_1 vp011000101_2))
private theorem bp0110001010 : Branch 0 (-3151761639/16000000 : ℚ) vp011000101 := by
  apply branch_left_normalized (c:=vp0110001010) (k:=0) (m:=157) (by decide +kernel)
  rw [show 2*(-3151761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3151761639/8000000 : ℚ) by norm_num]
  exact coverp0110001010
private noncomputable def ep0110001011_0 : Blocks := edgeBlocks% "full/vectors/0110001011-E-0000.bin"
private noncomputable def ep0110001011_1 : Blocks := edgeBlocks% "full/vectors/0110001011-E-0001.bin"
private noncomputable def ep0110001011_2 : Blocks := edgeBlocks% "full/vectors/0110001011-E-0002.bin"
noncomputable def ep0110001011 : Blocks := (Blocks.join ep0110001011_0 (Blocks.join ep0110001011_1 ep0110001011_2))
private theorem idp0110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000101.list =
    C ((2:ℤ)^346) * horner X vp0110001011.list + horner X ep0110001011.list := by
  exact edge_identity (B := (2:ℤ)^541) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110001011 : Branch 1 (-3151761639/16000000 : ℚ) vp011000101 := by
  apply branch_checked idp0110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3151761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3159761639/8000000 : ℚ) by norm_num]
  exact coverp0110001011
theorem coverp011000101 : Covers (-3151761639/16000000 : ℚ) vp011000101 := join_branches bp0110001010 bp0110001011
private noncomputable def vp01100010011_0 : Blocks := edgeBlocks% "full/vectors/01100010011-V-0000.bin"
noncomputable def vp01100010011 : Blocks := vp01100010011_0
theorem coverp01100010011 : Covers (-3147761639/4000000 : ℚ) vp01100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp01100010010_0 : Blocks := edgeBlocks% "full/vectors/01100010010-V-0000.bin"
noncomputable def vp01100010010 : Blocks := vp01100010010_0
theorem coverp01100010010 : Covers (-3143761639/4000000 : ℚ) vp01100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110001001_0 : Blocks := edgeBlocks% "full/vectors/0110001001-V-0000.bin"
private noncomputable def vp0110001001_1 : Blocks := edgeBlocks% "full/vectors/0110001001-V-0001.bin"
noncomputable def vp0110001001 : Blocks := (Blocks.join vp0110001001_0 vp0110001001_1)
private theorem bp01100010010 : Branch 0 (-3143761639/8000000 : ℚ) vp0110001001 := by
  apply branch_left_normalized (c:=vp01100010010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3143761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3143761639/4000000 : ℚ) by norm_num]
  exact coverp01100010010
private noncomputable def ep01100010011_0 : Blocks := edgeBlocks% "full/vectors/01100010011-E-0000.bin"
private noncomputable def ep01100010011_1 : Blocks := edgeBlocks% "full/vectors/01100010011-E-0001.bin"
noncomputable def ep01100010011 : Blocks := (Blocks.join ep01100010011_0 ep01100010011_1)
private theorem idp01100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001001.list =
    C ((2:ℤ)^188) * horner X vp01100010011.list + horner X ep01100010011.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100010011 : Branch 1 (-3143761639/8000000 : ℚ) vp0110001001 := by
  apply branch_checked idp01100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3143761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3147761639/4000000 : ℚ) by norm_num]
  exact coverp01100010011
theorem coverp0110001001 : Covers (-3143761639/8000000 : ℚ) vp0110001001 := join_branches bp01100010010 bp01100010011
private noncomputable def vp011000100011_0 : Blocks := edgeBlocks% "full/vectors/011000100011-V-0000.bin"
noncomputable def vp011000100011 : Blocks := vp011000100011_0
theorem coverp011000100011 : Covers (-3141761639/2000000 : ℚ) vp011000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp011000100010_0 : Blocks := edgeBlocks% "full/vectors/011000100010-V-0000.bin"
noncomputable def vp011000100010 : Blocks := vp011000100010_0
theorem coverp011000100010 : Covers (-3139761639/2000000 : ℚ) vp011000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100010001_0 : Blocks := edgeBlocks% "full/vectors/01100010001-V-0000.bin"
noncomputable def vp01100010001 : Blocks := vp01100010001_0
private theorem bp011000100010 : Branch 0 (-3139761639/4000000 : ℚ) vp01100010001 := by
  apply branch_left_normalized (c:=vp011000100010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3139761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3139761639/2000000 : ℚ) by norm_num]
  exact coverp011000100010
private noncomputable def ep011000100011_0 : Blocks := edgeBlocks% "full/vectors/011000100011-E-0000.bin"
noncomputable def ep011000100011 : Blocks := ep011000100011_0
private theorem idp011000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100010001.list =
    C ((2:ℤ)^103) * horner X vp011000100011.list + horner X ep011000100011.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000100011 : Branch 1 (-3139761639/4000000 : ℚ) vp01100010001 := by
  apply branch_checked idp011000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3139761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3141761639/2000000 : ℚ) by norm_num]
  exact coverp011000100011
theorem coverp01100010001 : Covers (-3139761639/4000000 : ℚ) vp01100010001 := join_branches bp011000100010 bp011000100011
private noncomputable def vp011000100001_0 : Blocks := edgeBlocks% "full/vectors/011000100001-V-0000.bin"
noncomputable def vp011000100001 : Blocks := vp011000100001_0
theorem coverp011000100001 : Covers (-3137761639/2000000 : ℚ) vp011000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp011000100000_0 : Blocks := edgeBlocks% "full/vectors/011000100000-V-0000.bin"
noncomputable def vp011000100000 : Blocks := vp011000100000_0
theorem coverp011000100000 : Covers (-3135761639/2000000 : ℚ) vp011000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100010000_0 : Blocks := edgeBlocks% "full/vectors/01100010000-V-0000.bin"
noncomputable def vp01100010000 : Blocks := vp01100010000_0
private theorem bp011000100000 : Branch 0 (-3135761639/4000000 : ℚ) vp01100010000 := by
  apply branch_left_normalized (c:=vp011000100000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3135761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3135761639/2000000 : ℚ) by norm_num]
  exact coverp011000100000
private noncomputable def ep011000100001_0 : Blocks := edgeBlocks% "full/vectors/011000100001-E-0000.bin"
noncomputable def ep011000100001 : Blocks := ep011000100001_0
private theorem idp011000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100010000.list =
    C ((2:ℤ)^102) * horner X vp011000100001.list + horner X ep011000100001.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000100001 : Branch 1 (-3135761639/4000000 : ℚ) vp01100010000 := by
  apply branch_checked idp011000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3135761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3137761639/2000000 : ℚ) by norm_num]
  exact coverp011000100001
theorem coverp01100010000 : Covers (-3135761639/4000000 : ℚ) vp01100010000 := join_branches bp011000100000 bp011000100001
private noncomputable def vp0110001000_0 : Blocks := edgeBlocks% "full/vectors/0110001000-V-0000.bin"
private noncomputable def vp0110001000_1 : Blocks := edgeBlocks% "full/vectors/0110001000-V-0001.bin"
noncomputable def vp0110001000 : Blocks := (Blocks.join vp0110001000_0 vp0110001000_1)
private theorem bp01100010000 : Branch 0 (-3135761639/8000000 : ℚ) vp0110001000 := by
  apply branch_left_normalized (c:=vp01100010000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3135761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3135761639/4000000 : ℚ) by norm_num]
  exact coverp01100010000
private noncomputable def ep01100010001_0 : Blocks := edgeBlocks% "full/vectors/01100010001-E-0000.bin"
private noncomputable def ep01100010001_1 : Blocks := edgeBlocks% "full/vectors/01100010001-E-0001.bin"
noncomputable def ep01100010001 : Blocks := (Blocks.join ep01100010001_0 ep01100010001_1)
private theorem idp01100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001000.list =
    C ((2:ℤ)^183) * horner X vp01100010001.list + horner X ep01100010001.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100010001 : Branch 1 (-3135761639/8000000 : ℚ) vp0110001000 := by
  apply branch_checked idp01100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3135761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3139761639/4000000 : ℚ) by norm_num]
  exact coverp01100010001
theorem coverp0110001000 : Covers (-3135761639/8000000 : ℚ) vp0110001000 := join_branches bp01100010000 bp01100010001
private noncomputable def vp011000100_0 : Blocks := edgeBlocks% "full/vectors/011000100-V-0000.bin"
private noncomputable def vp011000100_1 : Blocks := edgeBlocks% "full/vectors/011000100-V-0001.bin"
private noncomputable def vp011000100_2 : Blocks := edgeBlocks% "full/vectors/011000100-V-0002.bin"
noncomputable def vp011000100 : Blocks := (Blocks.join vp011000100_0 (Blocks.join vp011000100_1 vp011000100_2))
private theorem bp0110001000 : Branch 0 (-3135761639/16000000 : ℚ) vp011000100 := by
  apply branch_left_normalized (c:=vp0110001000) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-3135761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3135761639/8000000 : ℚ) by norm_num]
  exact coverp0110001000
private noncomputable def ep0110001001_0 : Blocks := edgeBlocks% "full/vectors/0110001001-E-0000.bin"
private noncomputable def ep0110001001_1 : Blocks := edgeBlocks% "full/vectors/0110001001-E-0001.bin"
private noncomputable def ep0110001001_2 : Blocks := edgeBlocks% "full/vectors/0110001001-E-0002.bin"
noncomputable def ep0110001001 : Blocks := (Blocks.join ep0110001001_0 (Blocks.join ep0110001001_1 ep0110001001_2))
private theorem idp0110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000100.list =
    C ((2:ℤ)^348) * horner X vp0110001001.list + horner X ep0110001001.list := by
  exact edge_identity (B := (2:ℤ)^550) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110001001 : Branch 1 (-3135761639/16000000 : ℚ) vp011000100 := by
  apply branch_checked idp0110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3135761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3143761639/8000000 : ℚ) by norm_num]
  exact coverp0110001001
theorem coverp011000100 : Covers (-3135761639/16000000 : ℚ) vp011000100 := join_branches bp0110001000 bp0110001001
private noncomputable def vp01100010_0 : Blocks := edgeBlocks% "full/vectors/01100010-V-0000.bin"
private noncomputable def vp01100010_1 : Blocks := edgeBlocks% "full/vectors/01100010-V-0001.bin"
private noncomputable def vp01100010_2 : Blocks := edgeBlocks% "full/vectors/01100010-V-0002.bin"
private noncomputable def vp01100010_3 : Blocks := edgeBlocks% "full/vectors/01100010-V-0003.bin"
private noncomputable def vp01100010_4 : Blocks := edgeBlocks% "full/vectors/01100010-V-0004.bin"
noncomputable def vp01100010 : Blocks := (Blocks.join (Blocks.join vp01100010_0 vp01100010_1) (Blocks.join vp01100010_2 (Blocks.join vp01100010_3 vp01100010_4)))
private theorem bp011000100 : Branch 0 (-3135761639/32000000 : ℚ) vp01100010 := by
  apply branch_left_normalized (c:=vp011000100) (k:=0) (m:=301) (by decide +kernel)
  rw [show 2*(-3135761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3135761639/16000000 : ℚ) by norm_num]
  exact coverp011000100
private noncomputable def ep011000101_0 : Blocks := edgeBlocks% "full/vectors/011000101-E-0000.bin"
private noncomputable def ep011000101_1 : Blocks := edgeBlocks% "full/vectors/011000101-E-0001.bin"
private noncomputable def ep011000101_2 : Blocks := edgeBlocks% "full/vectors/011000101-E-0002.bin"
private noncomputable def ep011000101_3 : Blocks := edgeBlocks% "full/vectors/011000101-E-0003.bin"
private noncomputable def ep011000101_4 : Blocks := edgeBlocks% "full/vectors/011000101-E-0004.bin"
noncomputable def ep011000101 : Blocks := (Blocks.join (Blocks.join ep011000101_0 ep011000101_1) (Blocks.join ep011000101_2 (Blocks.join ep011000101_3 ep011000101_4)))
private theorem idp011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100010.list =
    C ((2:ℤ)^677) * horner X vp011000101.list + horner X ep011000101.list := by
  exact edge_identity (B := (2:ℤ)^977) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000101 : Branch 1 (-3135761639/32000000 : ℚ) vp01100010 := by
  apply branch_checked idp011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3135761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3151761639/16000000 : ℚ) by norm_num]
  exact coverp011000101
theorem coverp01100010 : Covers (-3135761639/32000000 : ℚ) vp01100010 := join_branches bp011000100 bp011000101
private noncomputable def vp0110001_0 : Blocks := edgeBlocks% "full/vectors/0110001-V-0000.bin"
private noncomputable def vp0110001_1 : Blocks := edgeBlocks% "full/vectors/0110001-V-0001.bin"
private noncomputable def vp0110001_2 : Blocks := edgeBlocks% "full/vectors/0110001-V-0002.bin"
private noncomputable def vp0110001_3 : Blocks := edgeBlocks% "full/vectors/0110001-V-0003.bin"
private noncomputable def vp0110001_4 : Blocks := edgeBlocks% "full/vectors/0110001-V-0004.bin"
private noncomputable def vp0110001_5 : Blocks := edgeBlocks% "full/vectors/0110001-V-0005.bin"
private noncomputable def vp0110001_6 : Blocks := edgeBlocks% "full/vectors/0110001-V-0006.bin"
private noncomputable def vp0110001_7 : Blocks := edgeBlocks% "full/vectors/0110001-V-0007.bin"
private noncomputable def vp0110001_8 : Blocks := edgeBlocks% "full/vectors/0110001-V-0008.bin"
noncomputable def vp0110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110001_0 vp0110001_1) (Blocks.join vp0110001_2 vp0110001_3)) (Blocks.join (Blocks.join vp0110001_4 vp0110001_5) (Blocks.join vp0110001_6 (Blocks.join vp0110001_7 vp0110001_8))))
private theorem bp01100010 : Branch 0 (-3135761639/64000000 : ℚ) vp0110001 := by
  apply branch_left_normalized (c:=vp01100010) (k:=0) (m:=579) (by decide +kernel)
  rw [show 2*(-3135761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3135761639/32000000 : ℚ) by norm_num]
  exact coverp01100010
private noncomputable def ep01100011_0 : Blocks := edgeBlocks% "full/vectors/01100011-E-0000.bin"
private noncomputable def ep01100011_1 : Blocks := edgeBlocks% "full/vectors/01100011-E-0001.bin"
private noncomputable def ep01100011_2 : Blocks := edgeBlocks% "full/vectors/01100011-E-0002.bin"
private noncomputable def ep01100011_3 : Blocks := edgeBlocks% "full/vectors/01100011-E-0003.bin"
private noncomputable def ep01100011_4 : Blocks := edgeBlocks% "full/vectors/01100011-E-0004.bin"
private noncomputable def ep01100011_5 : Blocks := edgeBlocks% "full/vectors/01100011-E-0005.bin"
private noncomputable def ep01100011_6 : Blocks := edgeBlocks% "full/vectors/01100011-E-0006.bin"
private noncomputable def ep01100011_7 : Blocks := edgeBlocks% "full/vectors/01100011-E-0007.bin"
private noncomputable def ep01100011_8 : Blocks := edgeBlocks% "full/vectors/01100011-E-0008.bin"
noncomputable def ep01100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01100011_0 ep01100011_1) (Blocks.join ep01100011_2 ep01100011_3)) (Blocks.join (Blocks.join ep01100011_4 ep01100011_5) (Blocks.join ep01100011_6 (Blocks.join ep01100011_7 ep01100011_8))))
private theorem idp01100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110001.list =
    C ((2:ℤ)^1320) * horner X vp01100011.list + horner X ep01100011.list := by
  exact edge_identity (B := (2:ℤ)^1820) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100011 : Branch 1 (-3135761639/64000000 : ℚ) vp0110001 := by
  apply branch_checked idp01100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3135761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3167761639/32000000 : ℚ) by norm_num]
  exact coverp01100011
theorem coverp0110001 : Covers (-3135761639/64000000 : ℚ) vp0110001 := join_branches bp01100010 bp01100011
private noncomputable def vp011000011111_0 : Blocks := edgeBlocks% "full/vectors/011000011111-V-0000.bin"
noncomputable def vp011000011111 : Blocks := vp011000011111_0
theorem coverp011000011111 : Covers (-3133761639/2000000 : ℚ) vp011000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp011000011110_0 : Blocks := edgeBlocks% "full/vectors/011000011110-V-0000.bin"
noncomputable def vp011000011110 : Blocks := vp011000011110_0
theorem coverp011000011110 : Covers (-3131761639/2000000 : ℚ) vp011000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001111_0 : Blocks := edgeBlocks% "full/vectors/01100001111-V-0000.bin"
noncomputable def vp01100001111 : Blocks := vp01100001111_0
private theorem bp011000011110 : Branch 0 (-3131761639/4000000 : ℚ) vp01100001111 := by
  apply branch_left_normalized (c:=vp011000011110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3131761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3131761639/2000000 : ℚ) by norm_num]
  exact coverp011000011110
private noncomputable def ep011000011111_0 : Blocks := edgeBlocks% "full/vectors/011000011111-E-0000.bin"
noncomputable def ep011000011111 : Blocks := ep011000011111_0
private theorem idp011000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001111.list =
    C ((2:ℤ)^102) * horner X vp011000011111.list + horner X ep011000011111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000011111 : Branch 1 (-3131761639/4000000 : ℚ) vp01100001111 := by
  apply branch_checked idp011000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3131761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3133761639/2000000 : ℚ) by norm_num]
  exact coverp011000011111
theorem coverp01100001111 : Covers (-3131761639/4000000 : ℚ) vp01100001111 := join_branches bp011000011110 bp011000011111
private noncomputable def vp011000011101_0 : Blocks := edgeBlocks% "full/vectors/011000011101-V-0000.bin"
noncomputable def vp011000011101 : Blocks := vp011000011101_0
theorem coverp011000011101 : Covers (-3129761639/2000000 : ℚ) vp011000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp011000011100_0 : Blocks := edgeBlocks% "full/vectors/011000011100-V-0000.bin"
noncomputable def vp011000011100 : Blocks := vp011000011100_0
theorem coverp011000011100 : Covers (-3127761639/2000000 : ℚ) vp011000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001110_0 : Blocks := edgeBlocks% "full/vectors/01100001110-V-0000.bin"
noncomputable def vp01100001110 : Blocks := vp01100001110_0
private theorem bp011000011100 : Branch 0 (-3127761639/4000000 : ℚ) vp01100001110 := by
  apply branch_left_normalized (c:=vp011000011100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3127761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3127761639/2000000 : ℚ) by norm_num]
  exact coverp011000011100
private noncomputable def ep011000011101_0 : Blocks := edgeBlocks% "full/vectors/011000011101-E-0000.bin"
noncomputable def ep011000011101 : Blocks := ep011000011101_0
private theorem idp011000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001110.list =
    C ((2:ℤ)^104) * horner X vp011000011101.list + horner X ep011000011101.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000011101 : Branch 1 (-3127761639/4000000 : ℚ) vp01100001110 := by
  apply branch_checked idp011000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3127761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3129761639/2000000 : ℚ) by norm_num]
  exact coverp011000011101
theorem coverp01100001110 : Covers (-3127761639/4000000 : ℚ) vp01100001110 := join_branches bp011000011100 bp011000011101
private noncomputable def vp0110000111_0 : Blocks := edgeBlocks% "full/vectors/0110000111-V-0000.bin"
private noncomputable def vp0110000111_1 : Blocks := edgeBlocks% "full/vectors/0110000111-V-0001.bin"
noncomputable def vp0110000111 : Blocks := (Blocks.join vp0110000111_0 vp0110000111_1)
private theorem bp01100001110 : Branch 0 (-3127761639/8000000 : ℚ) vp0110000111 := by
  apply branch_left_normalized (c:=vp01100001110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3127761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3127761639/4000000 : ℚ) by norm_num]
  exact coverp01100001110
private noncomputable def ep01100001111_0 : Blocks := edgeBlocks% "full/vectors/01100001111-E-0000.bin"
private noncomputable def ep01100001111_1 : Blocks := edgeBlocks% "full/vectors/01100001111-E-0001.bin"
noncomputable def ep01100001111 : Blocks := (Blocks.join ep01100001111_0 ep01100001111_1)
private theorem idp01100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000111.list =
    C ((2:ℤ)^188) * horner X vp01100001111.list + horner X ep01100001111.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100001111 : Branch 1 (-3127761639/8000000 : ℚ) vp0110000111 := by
  apply branch_checked idp01100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3127761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3131761639/4000000 : ℚ) by norm_num]
  exact coverp01100001111
theorem coverp0110000111 : Covers (-3127761639/8000000 : ℚ) vp0110000111 := join_branches bp01100001110 bp01100001111
private noncomputable def vp011000011011_0 : Blocks := edgeBlocks% "full/vectors/011000011011-V-0000.bin"
noncomputable def vp011000011011 : Blocks := vp011000011011_0
theorem coverp011000011011 : Covers (-3125761639/2000000 : ℚ) vp011000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp011000011010_0 : Blocks := edgeBlocks% "full/vectors/011000011010-V-0000.bin"
noncomputable def vp011000011010 : Blocks := vp011000011010_0
theorem coverp011000011010 : Covers (-3123761639/2000000 : ℚ) vp011000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001101_0 : Blocks := edgeBlocks% "full/vectors/01100001101-V-0000.bin"
noncomputable def vp01100001101 : Blocks := vp01100001101_0
private theorem bp011000011010 : Branch 0 (-3123761639/4000000 : ℚ) vp01100001101 := by
  apply branch_left_normalized (c:=vp011000011010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3123761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3123761639/2000000 : ℚ) by norm_num]
  exact coverp011000011010
private noncomputable def ep011000011011_0 : Blocks := edgeBlocks% "full/vectors/011000011011-E-0000.bin"
noncomputable def ep011000011011 : Blocks := ep011000011011_0
private theorem idp011000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001101.list =
    C ((2:ℤ)^103) * horner X vp011000011011.list + horner X ep011000011011.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000011011 : Branch 1 (-3123761639/4000000 : ℚ) vp01100001101 := by
  apply branch_checked idp011000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3123761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3125761639/2000000 : ℚ) by norm_num]
  exact coverp011000011011
theorem coverp01100001101 : Covers (-3123761639/4000000 : ℚ) vp01100001101 := join_branches bp011000011010 bp011000011011
private noncomputable def vp011000011001_0 : Blocks := edgeBlocks% "full/vectors/011000011001-V-0000.bin"
noncomputable def vp011000011001 : Blocks := vp011000011001_0
theorem coverp011000011001 : Covers (-3121761639/2000000 : ℚ) vp011000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp011000011000_0 : Blocks := edgeBlocks% "full/vectors/011000011000-V-0000.bin"
noncomputable def vp011000011000 : Blocks := vp011000011000_0
theorem coverp011000011000 : Covers (-3119761639/2000000 : ℚ) vp011000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001100_0 : Blocks := edgeBlocks% "full/vectors/01100001100-V-0000.bin"
noncomputable def vp01100001100 : Blocks := vp01100001100_0
private theorem bp011000011000 : Branch 0 (-3119761639/4000000 : ℚ) vp01100001100 := by
  apply branch_left_normalized (c:=vp011000011000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3119761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3119761639/2000000 : ℚ) by norm_num]
  exact coverp011000011000
private noncomputable def ep011000011001_0 : Blocks := edgeBlocks% "full/vectors/011000011001-E-0000.bin"
noncomputable def ep011000011001 : Blocks := ep011000011001_0
private theorem idp011000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001100.list =
    C ((2:ℤ)^102) * horner X vp011000011001.list + horner X ep011000011001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000011001 : Branch 1 (-3119761639/4000000 : ℚ) vp01100001100 := by
  apply branch_checked idp011000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3119761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3121761639/2000000 : ℚ) by norm_num]
  exact coverp011000011001
theorem coverp01100001100 : Covers (-3119761639/4000000 : ℚ) vp01100001100 := join_branches bp011000011000 bp011000011001
private noncomputable def vp0110000110_0 : Blocks := edgeBlocks% "full/vectors/0110000110-V-0000.bin"
private noncomputable def vp0110000110_1 : Blocks := edgeBlocks% "full/vectors/0110000110-V-0001.bin"
noncomputable def vp0110000110 : Blocks := (Blocks.join vp0110000110_0 vp0110000110_1)
private theorem bp01100001100 : Branch 0 (-3119761639/8000000 : ℚ) vp0110000110 := by
  apply branch_left_normalized (c:=vp01100001100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3119761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3119761639/4000000 : ℚ) by norm_num]
  exact coverp01100001100
private noncomputable def ep01100001101_0 : Blocks := edgeBlocks% "full/vectors/01100001101-E-0000.bin"
private noncomputable def ep01100001101_1 : Blocks := edgeBlocks% "full/vectors/01100001101-E-0001.bin"
noncomputable def ep01100001101 : Blocks := (Blocks.join ep01100001101_0 ep01100001101_1)
private theorem idp01100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000110.list =
    C ((2:ℤ)^186) * horner X vp01100001101.list + horner X ep01100001101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100001101 : Branch 1 (-3119761639/8000000 : ℚ) vp0110000110 := by
  apply branch_checked idp01100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3119761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3123761639/4000000 : ℚ) by norm_num]
  exact coverp01100001101
theorem coverp0110000110 : Covers (-3119761639/8000000 : ℚ) vp0110000110 := join_branches bp01100001100 bp01100001101
private noncomputable def vp011000011_0 : Blocks := edgeBlocks% "full/vectors/011000011-V-0000.bin"
private noncomputable def vp011000011_1 : Blocks := edgeBlocks% "full/vectors/011000011-V-0001.bin"
private noncomputable def vp011000011_2 : Blocks := edgeBlocks% "full/vectors/011000011-V-0002.bin"
noncomputable def vp011000011 : Blocks := (Blocks.join vp011000011_0 (Blocks.join vp011000011_1 vp011000011_2))
private theorem bp0110000110 : Branch 0 (-3119761639/16000000 : ℚ) vp011000011 := by
  apply branch_left_normalized (c:=vp0110000110) (k:=0) (m:=162) (by decide +kernel)
  rw [show 2*(-3119761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3119761639/8000000 : ℚ) by norm_num]
  exact coverp0110000110
private noncomputable def ep0110000111_0 : Blocks := edgeBlocks% "full/vectors/0110000111-E-0000.bin"
private noncomputable def ep0110000111_1 : Blocks := edgeBlocks% "full/vectors/0110000111-E-0001.bin"
private noncomputable def ep0110000111_2 : Blocks := edgeBlocks% "full/vectors/0110000111-E-0002.bin"
noncomputable def ep0110000111 : Blocks := (Blocks.join ep0110000111_0 (Blocks.join ep0110000111_1 ep0110000111_2))
private theorem idp0110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000011.list =
    C ((2:ℤ)^350) * horner X vp0110000111.list + horner X ep0110000111.list := by
  exact edge_identity (B := (2:ℤ)^554) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110000111 : Branch 1 (-3119761639/16000000 : ℚ) vp011000011 := by
  apply branch_checked idp0110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3119761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3127761639/8000000 : ℚ) by norm_num]
  exact coverp0110000111
theorem coverp011000011 : Covers (-3119761639/16000000 : ℚ) vp011000011 := join_branches bp0110000110 bp0110000111
private noncomputable def vp011000010111_0 : Blocks := edgeBlocks% "full/vectors/011000010111-V-0000.bin"
noncomputable def vp011000010111 : Blocks := vp011000010111_0
theorem coverp011000010111 : Covers (-3117761639/2000000 : ℚ) vp011000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp011000010110_0 : Blocks := edgeBlocks% "full/vectors/011000010110-V-0000.bin"
noncomputable def vp011000010110 : Blocks := vp011000010110_0
theorem coverp011000010110 : Covers (-3115761639/2000000 : ℚ) vp011000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001011_0 : Blocks := edgeBlocks% "full/vectors/01100001011-V-0000.bin"
noncomputable def vp01100001011 : Blocks := vp01100001011_0
private theorem bp011000010110 : Branch 0 (-3115761639/4000000 : ℚ) vp01100001011 := by
  apply branch_left_normalized (c:=vp011000010110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3115761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3115761639/2000000 : ℚ) by norm_num]
  exact coverp011000010110
private noncomputable def ep011000010111_0 : Blocks := edgeBlocks% "full/vectors/011000010111-E-0000.bin"
noncomputable def ep011000010111 : Blocks := ep011000010111_0
private theorem idp011000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001011.list =
    C ((2:ℤ)^103) * horner X vp011000010111.list + horner X ep011000010111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000010111 : Branch 1 (-3115761639/4000000 : ℚ) vp01100001011 := by
  apply branch_checked idp011000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3115761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3117761639/2000000 : ℚ) by norm_num]
  exact coverp011000010111
theorem coverp01100001011 : Covers (-3115761639/4000000 : ℚ) vp01100001011 := join_branches bp011000010110 bp011000010111
private noncomputable def vp011000010101_0 : Blocks := edgeBlocks% "full/vectors/011000010101-V-0000.bin"
noncomputable def vp011000010101 : Blocks := vp011000010101_0
theorem coverp011000010101 : Covers (-3113761639/2000000 : ℚ) vp011000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp011000010100_0 : Blocks := edgeBlocks% "full/vectors/011000010100-V-0000.bin"
noncomputable def vp011000010100 : Blocks := vp011000010100_0
theorem coverp011000010100 : Covers (-3111761639/2000000 : ℚ) vp011000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001010_0 : Blocks := edgeBlocks% "full/vectors/01100001010-V-0000.bin"
noncomputable def vp01100001010 : Blocks := vp01100001010_0
private theorem bp011000010100 : Branch 0 (-3111761639/4000000 : ℚ) vp01100001010 := by
  apply branch_left_normalized (c:=vp011000010100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3111761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3111761639/2000000 : ℚ) by norm_num]
  exact coverp011000010100
private noncomputable def ep011000010101_0 : Blocks := edgeBlocks% "full/vectors/011000010101-E-0000.bin"
noncomputable def ep011000010101 : Blocks := ep011000010101_0
private theorem idp011000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001010.list =
    C ((2:ℤ)^103) * horner X vp011000010101.list + horner X ep011000010101.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000010101 : Branch 1 (-3111761639/4000000 : ℚ) vp01100001010 := by
  apply branch_checked idp011000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3111761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3113761639/2000000 : ℚ) by norm_num]
  exact coverp011000010101
theorem coverp01100001010 : Covers (-3111761639/4000000 : ℚ) vp01100001010 := join_branches bp011000010100 bp011000010101
private noncomputable def vp0110000101_0 : Blocks := edgeBlocks% "full/vectors/0110000101-V-0000.bin"
private noncomputable def vp0110000101_1 : Blocks := edgeBlocks% "full/vectors/0110000101-V-0001.bin"
noncomputable def vp0110000101 : Blocks := (Blocks.join vp0110000101_0 vp0110000101_1)
private theorem bp01100001010 : Branch 0 (-3111761639/8000000 : ℚ) vp0110000101 := by
  apply branch_left_normalized (c:=vp01100001010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-3111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3111761639/4000000 : ℚ) by norm_num]
  exact coverp01100001010
private noncomputable def ep01100001011_0 : Blocks := edgeBlocks% "full/vectors/01100001011-E-0000.bin"
private noncomputable def ep01100001011_1 : Blocks := edgeBlocks% "full/vectors/01100001011-E-0001.bin"
noncomputable def ep01100001011 : Blocks := (Blocks.join ep01100001011_0 ep01100001011_1)
private theorem idp01100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000101.list =
    C ((2:ℤ)^186) * horner X vp01100001011.list + horner X ep01100001011.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100001011 : Branch 1 (-3111761639/8000000 : ℚ) vp0110000101 := by
  apply branch_checked idp01100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3115761639/4000000 : ℚ) by norm_num]
  exact coverp01100001011
theorem coverp0110000101 : Covers (-3111761639/8000000 : ℚ) vp0110000101 := join_branches bp01100001010 bp01100001011
private noncomputable def vp011000010011_0 : Blocks := edgeBlocks% "full/vectors/011000010011-V-0000.bin"
noncomputable def vp011000010011 : Blocks := vp011000010011_0
theorem coverp011000010011 : Covers (-3109761639/2000000 : ℚ) vp011000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp011000010010_0 : Blocks := edgeBlocks% "full/vectors/011000010010-V-0000.bin"
noncomputable def vp011000010010 : Blocks := vp011000010010_0
theorem coverp011000010010 : Covers (-3107761639/2000000 : ℚ) vp011000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001001_0 : Blocks := edgeBlocks% "full/vectors/01100001001-V-0000.bin"
noncomputable def vp01100001001 : Blocks := vp01100001001_0
private theorem bp011000010010 : Branch 0 (-3107761639/4000000 : ℚ) vp01100001001 := by
  apply branch_left_normalized (c:=vp011000010010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3107761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3107761639/2000000 : ℚ) by norm_num]
  exact coverp011000010010
private noncomputable def ep011000010011_0 : Blocks := edgeBlocks% "full/vectors/011000010011-E-0000.bin"
noncomputable def ep011000010011 : Blocks := ep011000010011_0
private theorem idp011000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001001.list =
    C ((2:ℤ)^104) * horner X vp011000010011.list + horner X ep011000010011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000010011 : Branch 1 (-3107761639/4000000 : ℚ) vp01100001001 := by
  apply branch_checked idp011000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3107761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3109761639/2000000 : ℚ) by norm_num]
  exact coverp011000010011
theorem coverp01100001001 : Covers (-3107761639/4000000 : ℚ) vp01100001001 := join_branches bp011000010010 bp011000010011
private noncomputable def vp011000010001_0 : Blocks := edgeBlocks% "full/vectors/011000010001-V-0000.bin"
noncomputable def vp011000010001 : Blocks := vp011000010001_0
theorem coverp011000010001 : Covers (-3105761639/2000000 : ℚ) vp011000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp011000010000_0 : Blocks := edgeBlocks% "full/vectors/011000010000-V-0000.bin"
noncomputable def vp011000010000 : Blocks := vp011000010000_0
theorem coverp011000010000 : Covers (-3103761639/2000000 : ℚ) vp011000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100001000_0 : Blocks := edgeBlocks% "full/vectors/01100001000-V-0000.bin"
noncomputable def vp01100001000 : Blocks := vp01100001000_0
private theorem bp011000010000 : Branch 0 (-3103761639/4000000 : ℚ) vp01100001000 := by
  apply branch_left_normalized (c:=vp011000010000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3103761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3103761639/2000000 : ℚ) by norm_num]
  exact coverp011000010000
private noncomputable def ep011000010001_0 : Blocks := edgeBlocks% "full/vectors/011000010001-E-0000.bin"
noncomputable def ep011000010001 : Blocks := ep011000010001_0
private theorem idp011000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001000.list =
    C ((2:ℤ)^105) * horner X vp011000010001.list + horner X ep011000010001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000010001 : Branch 1 (-3103761639/4000000 : ℚ) vp01100001000 := by
  apply branch_checked idp011000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3103761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3105761639/2000000 : ℚ) by norm_num]
  exact coverp011000010001
theorem coverp01100001000 : Covers (-3103761639/4000000 : ℚ) vp01100001000 := join_branches bp011000010000 bp011000010001
private noncomputable def vp0110000100_0 : Blocks := edgeBlocks% "full/vectors/0110000100-V-0000.bin"
private noncomputable def vp0110000100_1 : Blocks := edgeBlocks% "full/vectors/0110000100-V-0001.bin"
noncomputable def vp0110000100 : Blocks := (Blocks.join vp0110000100_0 vp0110000100_1)
private theorem bp01100001000 : Branch 0 (-3103761639/8000000 : ℚ) vp0110000100 := by
  apply branch_left_normalized (c:=vp01100001000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3103761639/4000000 : ℚ) by norm_num]
  exact coverp01100001000
private noncomputable def ep01100001001_0 : Blocks := edgeBlocks% "full/vectors/01100001001-E-0000.bin"
private noncomputable def ep01100001001_1 : Blocks := edgeBlocks% "full/vectors/01100001001-E-0001.bin"
noncomputable def ep01100001001 : Blocks := (Blocks.join ep01100001001_0 ep01100001001_1)
private theorem idp01100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000100.list =
    C ((2:ℤ)^187) * horner X vp01100001001.list + horner X ep01100001001.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100001001 : Branch 1 (-3103761639/8000000 : ℚ) vp0110000100 := by
  apply branch_checked idp01100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3107761639/4000000 : ℚ) by norm_num]
  exact coverp01100001001
theorem coverp0110000100 : Covers (-3103761639/8000000 : ℚ) vp0110000100 := join_branches bp01100001000 bp01100001001
private noncomputable def vp011000010_0 : Blocks := edgeBlocks% "full/vectors/011000010-V-0000.bin"
private noncomputable def vp011000010_1 : Blocks := edgeBlocks% "full/vectors/011000010-V-0001.bin"
private noncomputable def vp011000010_2 : Blocks := edgeBlocks% "full/vectors/011000010-V-0002.bin"
noncomputable def vp011000010 : Blocks := (Blocks.join vp011000010_0 (Blocks.join vp011000010_1 vp011000010_2))
private theorem bp0110000100 : Branch 0 (-3103761639/16000000 : ℚ) vp011000010 := by
  apply branch_left_normalized (c:=vp0110000100) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-3103761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3103761639/8000000 : ℚ) by norm_num]
  exact coverp0110000100
private noncomputable def ep0110000101_0 : Blocks := edgeBlocks% "full/vectors/0110000101-E-0000.bin"
private noncomputable def ep0110000101_1 : Blocks := edgeBlocks% "full/vectors/0110000101-E-0001.bin"
private noncomputable def ep0110000101_2 : Blocks := edgeBlocks% "full/vectors/0110000101-E-0002.bin"
noncomputable def ep0110000101 : Blocks := (Blocks.join ep0110000101_0 (Blocks.join ep0110000101_1 ep0110000101_2))
private theorem idp0110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000010.list =
    C ((2:ℤ)^352) * horner X vp0110000101.list + horner X ep0110000101.list := by
  exact edge_identity (B := (2:ℤ)^556) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110000101 : Branch 1 (-3103761639/16000000 : ℚ) vp011000010 := by
  apply branch_checked idp0110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3103761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3111761639/8000000 : ℚ) by norm_num]
  exact coverp0110000101
theorem coverp011000010 : Covers (-3103761639/16000000 : ℚ) vp011000010 := join_branches bp0110000100 bp0110000101
private noncomputable def vp01100001_0 : Blocks := edgeBlocks% "full/vectors/01100001-V-0000.bin"
private noncomputable def vp01100001_1 : Blocks := edgeBlocks% "full/vectors/01100001-V-0001.bin"
private noncomputable def vp01100001_2 : Blocks := edgeBlocks% "full/vectors/01100001-V-0002.bin"
private noncomputable def vp01100001_3 : Blocks := edgeBlocks% "full/vectors/01100001-V-0003.bin"
private noncomputable def vp01100001_4 : Blocks := edgeBlocks% "full/vectors/01100001-V-0004.bin"
noncomputable def vp01100001 : Blocks := (Blocks.join (Blocks.join vp01100001_0 vp01100001_1) (Blocks.join vp01100001_2 (Blocks.join vp01100001_3 vp01100001_4)))
private theorem bp011000010 : Branch 0 (-3103761639/32000000 : ℚ) vp01100001 := by
  apply branch_left_normalized (c:=vp011000010) (k:=0) (m:=304) (by decide +kernel)
  rw [show 2*(-3103761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3103761639/16000000 : ℚ) by norm_num]
  exact coverp011000010
private noncomputable def ep011000011_0 : Blocks := edgeBlocks% "full/vectors/011000011-E-0000.bin"
private noncomputable def ep011000011_1 : Blocks := edgeBlocks% "full/vectors/011000011-E-0001.bin"
private noncomputable def ep011000011_2 : Blocks := edgeBlocks% "full/vectors/011000011-E-0002.bin"
private noncomputable def ep011000011_3 : Blocks := edgeBlocks% "full/vectors/011000011-E-0003.bin"
private noncomputable def ep011000011_4 : Blocks := edgeBlocks% "full/vectors/011000011-E-0004.bin"
noncomputable def ep011000011 : Blocks := (Blocks.join (Blocks.join ep011000011_0 ep011000011_1) (Blocks.join ep011000011_2 (Blocks.join ep011000011_3 ep011000011_4)))
private theorem idp011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100001.list =
    C ((2:ℤ)^677) * horner X vp011000011.list + horner X ep011000011.list := by
  exact edge_identity (B := (2:ℤ)^985) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000011 : Branch 1 (-3103761639/32000000 : ℚ) vp01100001 := by
  apply branch_checked idp011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3103761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3119761639/16000000 : ℚ) by norm_num]
  exact coverp011000011
theorem coverp01100001 : Covers (-3103761639/32000000 : ℚ) vp01100001 := join_branches bp011000010 bp011000011
private noncomputable def vp011000001111_0 : Blocks := edgeBlocks% "full/vectors/011000001111-V-0000.bin"
noncomputable def vp011000001111 : Blocks := vp011000001111_0
theorem coverp011000001111 : Covers (-3101761639/2000000 : ℚ) vp011000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp011000001110_0 : Blocks := edgeBlocks% "full/vectors/011000001110-V-0000.bin"
noncomputable def vp011000001110 : Blocks := vp011000001110_0
theorem coverp011000001110 : Covers (-3099761639/2000000 : ℚ) vp011000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000111_0 : Blocks := edgeBlocks% "full/vectors/01100000111-V-0000.bin"
noncomputable def vp01100000111 : Blocks := vp01100000111_0
private theorem bp011000001110 : Branch 0 (-3099761639/4000000 : ℚ) vp01100000111 := by
  apply branch_left_normalized (c:=vp011000001110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3099761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3099761639/2000000 : ℚ) by norm_num]
  exact coverp011000001110
private noncomputable def ep011000001111_0 : Blocks := edgeBlocks% "full/vectors/011000001111-E-0000.bin"
noncomputable def ep011000001111 : Blocks := ep011000001111_0
private theorem idp011000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000111.list =
    C ((2:ℤ)^104) * horner X vp011000001111.list + horner X ep011000001111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000001111 : Branch 1 (-3099761639/4000000 : ℚ) vp01100000111 := by
  apply branch_checked idp011000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3099761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3101761639/2000000 : ℚ) by norm_num]
  exact coverp011000001111
theorem coverp01100000111 : Covers (-3099761639/4000000 : ℚ) vp01100000111 := join_branches bp011000001110 bp011000001111
private noncomputable def vp011000001101_0 : Blocks := edgeBlocks% "full/vectors/011000001101-V-0000.bin"
noncomputable def vp011000001101 : Blocks := vp011000001101_0
theorem coverp011000001101 : Covers (-3097761639/2000000 : ℚ) vp011000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp011000001100_0 : Blocks := edgeBlocks% "full/vectors/011000001100-V-0000.bin"
noncomputable def vp011000001100 : Blocks := vp011000001100_0
theorem coverp011000001100 : Covers (-3095761639/2000000 : ℚ) vp011000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000110_0 : Blocks := edgeBlocks% "full/vectors/01100000110-V-0000.bin"
noncomputable def vp01100000110 : Blocks := vp01100000110_0
private theorem bp011000001100 : Branch 0 (-3095761639/4000000 : ℚ) vp01100000110 := by
  apply branch_left_normalized (c:=vp011000001100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3095761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3095761639/2000000 : ℚ) by norm_num]
  exact coverp011000001100
private noncomputable def ep011000001101_0 : Blocks := edgeBlocks% "full/vectors/011000001101-E-0000.bin"
noncomputable def ep011000001101 : Blocks := ep011000001101_0
private theorem idp011000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000110.list =
    C ((2:ℤ)^105) * horner X vp011000001101.list + horner X ep011000001101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000001101 : Branch 1 (-3095761639/4000000 : ℚ) vp01100000110 := by
  apply branch_checked idp011000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3095761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3097761639/2000000 : ℚ) by norm_num]
  exact coverp011000001101
theorem coverp01100000110 : Covers (-3095761639/4000000 : ℚ) vp01100000110 := join_branches bp011000001100 bp011000001101
private noncomputable def vp0110000011_0 : Blocks := edgeBlocks% "full/vectors/0110000011-V-0000.bin"
private noncomputable def vp0110000011_1 : Blocks := edgeBlocks% "full/vectors/0110000011-V-0001.bin"
noncomputable def vp0110000011 : Blocks := (Blocks.join vp0110000011_0 vp0110000011_1)
private theorem bp01100000110 : Branch 0 (-3095761639/8000000 : ℚ) vp0110000011 := by
  apply branch_left_normalized (c:=vp01100000110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3095761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3095761639/4000000 : ℚ) by norm_num]
  exact coverp01100000110
private noncomputable def ep01100000111_0 : Blocks := edgeBlocks% "full/vectors/01100000111-E-0000.bin"
private noncomputable def ep01100000111_1 : Blocks := edgeBlocks% "full/vectors/01100000111-E-0001.bin"
noncomputable def ep01100000111 : Blocks := (Blocks.join ep01100000111_0 ep01100000111_1)
private theorem idp01100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000011.list =
    C ((2:ℤ)^187) * horner X vp01100000111.list + horner X ep01100000111.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100000111 : Branch 1 (-3095761639/8000000 : ℚ) vp0110000011 := by
  apply branch_checked idp01100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3095761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3099761639/4000000 : ℚ) by norm_num]
  exact coverp01100000111
theorem coverp0110000011 : Covers (-3095761639/8000000 : ℚ) vp0110000011 := join_branches bp01100000110 bp01100000111
private noncomputable def vp011000001011_0 : Blocks := edgeBlocks% "full/vectors/011000001011-V-0000.bin"
noncomputable def vp011000001011 : Blocks := vp011000001011_0
theorem coverp011000001011 : Covers (-3093761639/2000000 : ℚ) vp011000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp011000001010_0 : Blocks := edgeBlocks% "full/vectors/011000001010-V-0000.bin"
noncomputable def vp011000001010 : Blocks := vp011000001010_0
theorem coverp011000001010 : Covers (-3091761639/2000000 : ℚ) vp011000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000101_0 : Blocks := edgeBlocks% "full/vectors/01100000101-V-0000.bin"
noncomputable def vp01100000101 : Blocks := vp01100000101_0
private theorem bp011000001010 : Branch 0 (-3091761639/4000000 : ℚ) vp01100000101 := by
  apply branch_left_normalized (c:=vp011000001010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3091761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3091761639/2000000 : ℚ) by norm_num]
  exact coverp011000001010
private noncomputable def ep011000001011_0 : Blocks := edgeBlocks% "full/vectors/011000001011-E-0000.bin"
noncomputable def ep011000001011 : Blocks := ep011000001011_0
private theorem idp011000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000101.list =
    C ((2:ℤ)^104) * horner X vp011000001011.list + horner X ep011000001011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000001011 : Branch 1 (-3091761639/4000000 : ℚ) vp01100000101 := by
  apply branch_checked idp011000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3091761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3093761639/2000000 : ℚ) by norm_num]
  exact coverp011000001011
theorem coverp01100000101 : Covers (-3091761639/4000000 : ℚ) vp01100000101 := join_branches bp011000001010 bp011000001011
private noncomputable def vp011000001001_0 : Blocks := edgeBlocks% "full/vectors/011000001001-V-0000.bin"
noncomputable def vp011000001001 : Blocks := vp011000001001_0
theorem coverp011000001001 : Covers (-3089761639/2000000 : ℚ) vp011000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp011000001000_0 : Blocks := edgeBlocks% "full/vectors/011000001000-V-0000.bin"
noncomputable def vp011000001000 : Blocks := vp011000001000_0
theorem coverp011000001000 : Covers (-3087761639/2000000 : ℚ) vp011000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000100_0 : Blocks := edgeBlocks% "full/vectors/01100000100-V-0000.bin"
noncomputable def vp01100000100 : Blocks := vp01100000100_0
private theorem bp011000001000 : Branch 0 (-3087761639/4000000 : ℚ) vp01100000100 := by
  apply branch_left_normalized (c:=vp011000001000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3087761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3087761639/2000000 : ℚ) by norm_num]
  exact coverp011000001000
private noncomputable def ep011000001001_0 : Blocks := edgeBlocks% "full/vectors/011000001001-E-0000.bin"
noncomputable def ep011000001001 : Blocks := ep011000001001_0
private theorem idp011000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000100.list =
    C ((2:ℤ)^105) * horner X vp011000001001.list + horner X ep011000001001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000001001 : Branch 1 (-3087761639/4000000 : ℚ) vp01100000100 := by
  apply branch_checked idp011000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3087761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3089761639/2000000 : ℚ) by norm_num]
  exact coverp011000001001
theorem coverp01100000100 : Covers (-3087761639/4000000 : ℚ) vp01100000100 := join_branches bp011000001000 bp011000001001
private noncomputable def vp0110000010_0 : Blocks := edgeBlocks% "full/vectors/0110000010-V-0000.bin"
private noncomputable def vp0110000010_1 : Blocks := edgeBlocks% "full/vectors/0110000010-V-0001.bin"
noncomputable def vp0110000010 : Blocks := (Blocks.join vp0110000010_0 vp0110000010_1)
private theorem bp01100000100 : Branch 0 (-3087761639/8000000 : ℚ) vp0110000010 := by
  apply branch_left_normalized (c:=vp01100000100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3087761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3087761639/4000000 : ℚ) by norm_num]
  exact coverp01100000100
private noncomputable def ep01100000101_0 : Blocks := edgeBlocks% "full/vectors/01100000101-E-0000.bin"
private noncomputable def ep01100000101_1 : Blocks := edgeBlocks% "full/vectors/01100000101-E-0001.bin"
noncomputable def ep01100000101 : Blocks := (Blocks.join ep01100000101_0 ep01100000101_1)
private theorem idp01100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000010.list =
    C ((2:ℤ)^187) * horner X vp01100000101.list + horner X ep01100000101.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100000101 : Branch 1 (-3087761639/8000000 : ℚ) vp0110000010 := by
  apply branch_checked idp01100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3087761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3091761639/4000000 : ℚ) by norm_num]
  exact coverp01100000101
theorem coverp0110000010 : Covers (-3087761639/8000000 : ℚ) vp0110000010 := join_branches bp01100000100 bp01100000101
private noncomputable def vp011000001_0 : Blocks := edgeBlocks% "full/vectors/011000001-V-0000.bin"
private noncomputable def vp011000001_1 : Blocks := edgeBlocks% "full/vectors/011000001-V-0001.bin"
private noncomputable def vp011000001_2 : Blocks := edgeBlocks% "full/vectors/011000001-V-0002.bin"
noncomputable def vp011000001 : Blocks := (Blocks.join vp011000001_0 (Blocks.join vp011000001_1 vp011000001_2))
private theorem bp0110000010 : Branch 0 (-3087761639/16000000 : ℚ) vp011000001 := by
  apply branch_left_normalized (c:=vp0110000010) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-3087761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3087761639/8000000 : ℚ) by norm_num]
  exact coverp0110000010
private noncomputable def ep0110000011_0 : Blocks := edgeBlocks% "full/vectors/0110000011-E-0000.bin"
private noncomputable def ep0110000011_1 : Blocks := edgeBlocks% "full/vectors/0110000011-E-0001.bin"
private noncomputable def ep0110000011_2 : Blocks := edgeBlocks% "full/vectors/0110000011-E-0002.bin"
noncomputable def ep0110000011 : Blocks := (Blocks.join ep0110000011_0 (Blocks.join ep0110000011_1 ep0110000011_2))
private theorem idp0110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000001.list =
    C ((2:ℤ)^351) * horner X vp0110000011.list + horner X ep0110000011.list := by
  exact edge_identity (B := (2:ℤ)^556) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110000011 : Branch 1 (-3087761639/16000000 : ℚ) vp011000001 := by
  apply branch_checked idp0110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3087761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3095761639/8000000 : ℚ) by norm_num]
  exact coverp0110000011
theorem coverp011000001 : Covers (-3087761639/16000000 : ℚ) vp011000001 := join_branches bp0110000010 bp0110000011
private noncomputable def vp011000000111_0 : Blocks := edgeBlocks% "full/vectors/011000000111-V-0000.bin"
noncomputable def vp011000000111 : Blocks := vp011000000111_0
theorem coverp011000000111 : Covers (-3085761639/2000000 : ℚ) vp011000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp011000000110_0 : Blocks := edgeBlocks% "full/vectors/011000000110-V-0000.bin"
noncomputable def vp011000000110 : Blocks := vp011000000110_0
theorem coverp011000000110 : Covers (-3083761639/2000000 : ℚ) vp011000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000011_0 : Blocks := edgeBlocks% "full/vectors/01100000011-V-0000.bin"
noncomputable def vp01100000011 : Blocks := vp01100000011_0
private theorem bp011000000110 : Branch 0 (-3083761639/4000000 : ℚ) vp01100000011 := by
  apply branch_left_normalized (c:=vp011000000110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3083761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3083761639/2000000 : ℚ) by norm_num]
  exact coverp011000000110
private noncomputable def ep011000000111_0 : Blocks := edgeBlocks% "full/vectors/011000000111-E-0000.bin"
noncomputable def ep011000000111 : Blocks := ep011000000111_0
private theorem idp011000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000011.list =
    C ((2:ℤ)^105) * horner X vp011000000111.list + horner X ep011000000111.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000000111 : Branch 1 (-3083761639/4000000 : ℚ) vp01100000011 := by
  apply branch_checked idp011000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3083761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3085761639/2000000 : ℚ) by norm_num]
  exact coverp011000000111
theorem coverp01100000011 : Covers (-3083761639/4000000 : ℚ) vp01100000011 := join_branches bp011000000110 bp011000000111
private noncomputable def vp011000000101_0 : Blocks := edgeBlocks% "full/vectors/011000000101-V-0000.bin"
noncomputable def vp011000000101 : Blocks := vp011000000101_0
theorem coverp011000000101 : Covers (-3081761639/2000000 : ℚ) vp011000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp011000000100_0 : Blocks := edgeBlocks% "full/vectors/011000000100-V-0000.bin"
noncomputable def vp011000000100 : Blocks := vp011000000100_0
theorem coverp011000000100 : Covers (-3079761639/2000000 : ℚ) vp011000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000010_0 : Blocks := edgeBlocks% "full/vectors/01100000010-V-0000.bin"
noncomputable def vp01100000010 : Blocks := vp01100000010_0
private theorem bp011000000100 : Branch 0 (-3079761639/4000000 : ℚ) vp01100000010 := by
  apply branch_left_normalized (c:=vp011000000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3079761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3079761639/2000000 : ℚ) by norm_num]
  exact coverp011000000100
private noncomputable def ep011000000101_0 : Blocks := edgeBlocks% "full/vectors/011000000101-E-0000.bin"
noncomputable def ep011000000101 : Blocks := ep011000000101_0
private theorem idp011000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000010.list =
    C ((2:ℤ)^104) * horner X vp011000000101.list + horner X ep011000000101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000000101 : Branch 1 (-3079761639/4000000 : ℚ) vp01100000010 := by
  apply branch_checked idp011000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3079761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3081761639/2000000 : ℚ) by norm_num]
  exact coverp011000000101
theorem coverp01100000010 : Covers (-3079761639/4000000 : ℚ) vp01100000010 := join_branches bp011000000100 bp011000000101
private noncomputable def vp0110000001_0 : Blocks := edgeBlocks% "full/vectors/0110000001-V-0000.bin"
private noncomputable def vp0110000001_1 : Blocks := edgeBlocks% "full/vectors/0110000001-V-0001.bin"
noncomputable def vp0110000001 : Blocks := (Blocks.join vp0110000001_0 vp0110000001_1)
private theorem bp01100000010 : Branch 0 (-3079761639/8000000 : ℚ) vp0110000001 := by
  apply branch_left_normalized (c:=vp01100000010) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3079761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3079761639/4000000 : ℚ) by norm_num]
  exact coverp01100000010
private noncomputable def ep01100000011_0 : Blocks := edgeBlocks% "full/vectors/01100000011-E-0000.bin"
private noncomputable def ep01100000011_1 : Blocks := edgeBlocks% "full/vectors/01100000011-E-0001.bin"
noncomputable def ep01100000011 : Blocks := (Blocks.join ep01100000011_0 ep01100000011_1)
private theorem idp01100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000001.list =
    C ((2:ℤ)^187) * horner X vp01100000011.list + horner X ep01100000011.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100000011 : Branch 1 (-3079761639/8000000 : ℚ) vp0110000001 := by
  apply branch_checked idp01100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3079761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3083761639/4000000 : ℚ) by norm_num]
  exact coverp01100000011
theorem coverp0110000001 : Covers (-3079761639/8000000 : ℚ) vp0110000001 := join_branches bp01100000010 bp01100000011
private noncomputable def vp011000000011_0 : Blocks := edgeBlocks% "full/vectors/011000000011-V-0000.bin"
noncomputable def vp011000000011 : Blocks := vp011000000011_0
theorem coverp011000000011 : Covers (-3077761639/2000000 : ℚ) vp011000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp011000000010_0 : Blocks := edgeBlocks% "full/vectors/011000000010-V-0000.bin"
noncomputable def vp011000000010 : Blocks := vp011000000010_0
theorem coverp011000000010 : Covers (-3075761639/2000000 : ℚ) vp011000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000001_0 : Blocks := edgeBlocks% "full/vectors/01100000001-V-0000.bin"
noncomputable def vp01100000001 : Blocks := vp01100000001_0
private theorem bp011000000010 : Branch 0 (-3075761639/4000000 : ℚ) vp01100000001 := by
  apply branch_left_normalized (c:=vp011000000010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3075761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3075761639/2000000 : ℚ) by norm_num]
  exact coverp011000000010
private noncomputable def ep011000000011_0 : Blocks := edgeBlocks% "full/vectors/011000000011-E-0000.bin"
noncomputable def ep011000000011 : Blocks := ep011000000011_0
private theorem idp011000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000001.list =
    C ((2:ℤ)^104) * horner X vp011000000011.list + horner X ep011000000011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000000011 : Branch 1 (-3075761639/4000000 : ℚ) vp01100000001 := by
  apply branch_checked idp011000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3075761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3077761639/2000000 : ℚ) by norm_num]
  exact coverp011000000011
theorem coverp01100000001 : Covers (-3075761639/4000000 : ℚ) vp01100000001 := join_branches bp011000000010 bp011000000011
private noncomputable def vp011000000001_0 : Blocks := edgeBlocks% "full/vectors/011000000001-V-0000.bin"
noncomputable def vp011000000001 : Blocks := vp011000000001_0
theorem coverp011000000001 : Covers (-3073761639/2000000 : ℚ) vp011000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp011000000000_0 : Blocks := edgeBlocks% "full/vectors/011000000000-V-0000.bin"
noncomputable def vp011000000000 : Blocks := vp011000000000_0
theorem coverp011000000000 : Covers (-3071761639/2000000 : ℚ) vp011000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100000000_0 : Blocks := edgeBlocks% "full/vectors/01100000000-V-0000.bin"
noncomputable def vp01100000000 : Blocks := vp01100000000_0
private theorem bp011000000000 : Branch 0 (-3071761639/4000000 : ℚ) vp01100000000 := by
  apply branch_left_normalized (c:=vp011000000000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3071761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/2000000 : ℚ) by norm_num]
  exact coverp011000000000
private noncomputable def ep011000000001_0 : Blocks := edgeBlocks% "full/vectors/011000000001-E-0000.bin"
noncomputable def ep011000000001 : Blocks := ep011000000001_0
private theorem idp011000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000000.list =
    C ((2:ℤ)^103) * horner X vp011000000001.list + horner X ep011000000001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000000001 : Branch 1 (-3071761639/4000000 : ℚ) vp01100000000 := by
  apply branch_checked idp011000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3073761639/2000000 : ℚ) by norm_num]
  exact coverp011000000001
theorem coverp01100000000 : Covers (-3071761639/4000000 : ℚ) vp01100000000 := join_branches bp011000000000 bp011000000001
private noncomputable def vp0110000000_0 : Blocks := edgeBlocks% "full/vectors/0110000000-V-0000.bin"
private noncomputable def vp0110000000_1 : Blocks := edgeBlocks% "full/vectors/0110000000-V-0001.bin"
noncomputable def vp0110000000 : Blocks := (Blocks.join vp0110000000_0 vp0110000000_1)
private theorem bp01100000000 : Branch 0 (-3071761639/8000000 : ℚ) vp0110000000 := by
  apply branch_left_normalized (c:=vp01100000000) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-3071761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/4000000 : ℚ) by norm_num]
  exact coverp01100000000
private noncomputable def ep01100000001_0 : Blocks := edgeBlocks% "full/vectors/01100000001-E-0000.bin"
private noncomputable def ep01100000001_1 : Blocks := edgeBlocks% "full/vectors/01100000001-E-0001.bin"
noncomputable def ep01100000001 : Blocks := (Blocks.join ep01100000001_0 ep01100000001_1)
private theorem idp01100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000000.list =
    C ((2:ℤ)^187) * horner X vp01100000001.list + horner X ep01100000001.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100000001 : Branch 1 (-3071761639/8000000 : ℚ) vp0110000000 := by
  apply branch_checked idp01100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3075761639/4000000 : ℚ) by norm_num]
  exact coverp01100000001
theorem coverp0110000000 : Covers (-3071761639/8000000 : ℚ) vp0110000000 := join_branches bp01100000000 bp01100000001
private noncomputable def vp011000000_0 : Blocks := edgeBlocks% "full/vectors/011000000-V-0000.bin"
private noncomputable def vp011000000_1 : Blocks := edgeBlocks% "full/vectors/011000000-V-0001.bin"
private noncomputable def vp011000000_2 : Blocks := edgeBlocks% "full/vectors/011000000-V-0002.bin"
noncomputable def vp011000000 : Blocks := (Blocks.join vp011000000_0 (Blocks.join vp011000000_1 vp011000000_2))
private theorem bp0110000000 : Branch 0 (-3071761639/16000000 : ℚ) vp011000000 := by
  apply branch_left_normalized (c:=vp0110000000) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-3071761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/8000000 : ℚ) by norm_num]
  exact coverp0110000000
private noncomputable def ep0110000001_0 : Blocks := edgeBlocks% "full/vectors/0110000001-E-0000.bin"
private noncomputable def ep0110000001_1 : Blocks := edgeBlocks% "full/vectors/0110000001-E-0001.bin"
private noncomputable def ep0110000001_2 : Blocks := edgeBlocks% "full/vectors/0110000001-E-0002.bin"
noncomputable def ep0110000001 : Blocks := (Blocks.join ep0110000001_0 (Blocks.join ep0110000001_1 ep0110000001_2))
private theorem idp0110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000000.list =
    C ((2:ℤ)^351) * horner X vp0110000001.list + horner X ep0110000001.list := by
  exact edge_identity (B := (2:ℤ)^556) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110000001 : Branch 1 (-3071761639/16000000 : ℚ) vp011000000 := by
  apply branch_checked idp0110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3079761639/8000000 : ℚ) by norm_num]
  exact coverp0110000001
theorem coverp011000000 : Covers (-3071761639/16000000 : ℚ) vp011000000 := join_branches bp0110000000 bp0110000001
private noncomputable def vp01100000_0 : Blocks := edgeBlocks% "full/vectors/01100000-V-0000.bin"
private noncomputable def vp01100000_1 : Blocks := edgeBlocks% "full/vectors/01100000-V-0001.bin"
private noncomputable def vp01100000_2 : Blocks := edgeBlocks% "full/vectors/01100000-V-0002.bin"
private noncomputable def vp01100000_3 : Blocks := edgeBlocks% "full/vectors/01100000-V-0003.bin"
private noncomputable def vp01100000_4 : Blocks := edgeBlocks% "full/vectors/01100000-V-0004.bin"
noncomputable def vp01100000 : Blocks := (Blocks.join (Blocks.join vp01100000_0 vp01100000_1) (Blocks.join vp01100000_2 (Blocks.join vp01100000_3 vp01100000_4)))
private theorem bp011000000 : Branch 0 (-3071761639/32000000 : ℚ) vp01100000 := by
  apply branch_left_normalized (c:=vp011000000) (k:=0) (m:=304) (by decide +kernel)
  rw [show 2*(-3071761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/16000000 : ℚ) by norm_num]
  exact coverp011000000
private noncomputable def ep011000001_0 : Blocks := edgeBlocks% "full/vectors/011000001-E-0000.bin"
private noncomputable def ep011000001_1 : Blocks := edgeBlocks% "full/vectors/011000001-E-0001.bin"
private noncomputable def ep011000001_2 : Blocks := edgeBlocks% "full/vectors/011000001-E-0002.bin"
private noncomputable def ep011000001_3 : Blocks := edgeBlocks% "full/vectors/011000001-E-0003.bin"
private noncomputable def ep011000001_4 : Blocks := edgeBlocks% "full/vectors/011000001-E-0004.bin"
noncomputable def ep011000001 : Blocks := (Blocks.join (Blocks.join ep011000001_0 ep011000001_1) (Blocks.join ep011000001_2 (Blocks.join ep011000001_3 ep011000001_4)))
private theorem idp011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100000.list =
    C ((2:ℤ)^678) * horner X vp011000001.list + horner X ep011000001.list := by
  exact edge_identity (B := (2:ℤ)^987) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011000001 : Branch 1 (-3071761639/32000000 : ℚ) vp01100000 := by
  apply branch_checked idp011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3087761639/16000000 : ℚ) by norm_num]
  exact coverp011000001
theorem coverp01100000 : Covers (-3071761639/32000000 : ℚ) vp01100000 := join_branches bp011000000 bp011000001
private noncomputable def vp0110000_0 : Blocks := edgeBlocks% "full/vectors/0110000-V-0000.bin"
private noncomputable def vp0110000_1 : Blocks := edgeBlocks% "full/vectors/0110000-V-0001.bin"
private noncomputable def vp0110000_2 : Blocks := edgeBlocks% "full/vectors/0110000-V-0002.bin"
private noncomputable def vp0110000_3 : Blocks := edgeBlocks% "full/vectors/0110000-V-0003.bin"
private noncomputable def vp0110000_4 : Blocks := edgeBlocks% "full/vectors/0110000-V-0004.bin"
private noncomputable def vp0110000_5 : Blocks := edgeBlocks% "full/vectors/0110000-V-0005.bin"
private noncomputable def vp0110000_6 : Blocks := edgeBlocks% "full/vectors/0110000-V-0006.bin"
private noncomputable def vp0110000_7 : Blocks := edgeBlocks% "full/vectors/0110000-V-0007.bin"
private noncomputable def vp0110000_8 : Blocks := edgeBlocks% "full/vectors/0110000-V-0008.bin"
noncomputable def vp0110000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110000_0 vp0110000_1) (Blocks.join vp0110000_2 vp0110000_3)) (Blocks.join (Blocks.join vp0110000_4 vp0110000_5) (Blocks.join vp0110000_6 (Blocks.join vp0110000_7 vp0110000_8))))
private theorem bp01100000 : Branch 0 (-3071761639/64000000 : ℚ) vp0110000 := by
  apply branch_left_normalized (c:=vp01100000) (k:=0) (m:=585) (by decide +kernel)
  rw [show 2*(-3071761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/32000000 : ℚ) by norm_num]
  exact coverp01100000
private noncomputable def ep01100001_0 : Blocks := edgeBlocks% "full/vectors/01100001-E-0000.bin"
private noncomputable def ep01100001_1 : Blocks := edgeBlocks% "full/vectors/01100001-E-0001.bin"
private noncomputable def ep01100001_2 : Blocks := edgeBlocks% "full/vectors/01100001-E-0002.bin"
private noncomputable def ep01100001_3 : Blocks := edgeBlocks% "full/vectors/01100001-E-0003.bin"
private noncomputable def ep01100001_4 : Blocks := edgeBlocks% "full/vectors/01100001-E-0004.bin"
private noncomputable def ep01100001_5 : Blocks := edgeBlocks% "full/vectors/01100001-E-0005.bin"
private noncomputable def ep01100001_6 : Blocks := edgeBlocks% "full/vectors/01100001-E-0006.bin"
private noncomputable def ep01100001_7 : Blocks := edgeBlocks% "full/vectors/01100001-E-0007.bin"
private noncomputable def ep01100001_8 : Blocks := edgeBlocks% "full/vectors/01100001-E-0008.bin"
noncomputable def ep01100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01100001_0 ep01100001_1) (Blocks.join ep01100001_2 ep01100001_3)) (Blocks.join (Blocks.join ep01100001_4 ep01100001_5) (Blocks.join ep01100001_6 (Blocks.join ep01100001_7 ep01100001_8))))
private theorem idp01100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110000.list =
    C ((2:ℤ)^1324) * horner X vp01100001.list + horner X ep01100001.list := by
  exact edge_identity (B := (2:ℤ)^1840) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100001 : Branch 1 (-3071761639/64000000 : ℚ) vp0110000 := by
  apply branch_checked idp01100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3103761639/32000000 : ℚ) by norm_num]
  exact coverp01100001
theorem coverp0110000 : Covers (-3071761639/64000000 : ℚ) vp0110000 := join_branches bp01100000 bp01100001
private noncomputable def vp011000_0 : Blocks := edgeBlocks% "full/vectors/011000-V-0000.bin"
private noncomputable def vp011000_1 : Blocks := edgeBlocks% "full/vectors/011000-V-0001.bin"
private noncomputable def vp011000_2 : Blocks := edgeBlocks% "full/vectors/011000-V-0002.bin"
private noncomputable def vp011000_3 : Blocks := edgeBlocks% "full/vectors/011000-V-0003.bin"
private noncomputable def vp011000_4 : Blocks := edgeBlocks% "full/vectors/011000-V-0004.bin"
private noncomputable def vp011000_5 : Blocks := edgeBlocks% "full/vectors/011000-V-0005.bin"
private noncomputable def vp011000_6 : Blocks := edgeBlocks% "full/vectors/011000-V-0006.bin"
private noncomputable def vp011000_7 : Blocks := edgeBlocks% "full/vectors/011000-V-0007.bin"
private noncomputable def vp011000_8 : Blocks := edgeBlocks% "full/vectors/011000-V-0008.bin"
private noncomputable def vp011000_9 : Blocks := edgeBlocks% "full/vectors/011000-V-0009.bin"
private noncomputable def vp011000_10 : Blocks := edgeBlocks% "full/vectors/011000-V-0010.bin"
private noncomputable def vp011000_11 : Blocks := edgeBlocks% "full/vectors/011000-V-0011.bin"
private noncomputable def vp011000_12 : Blocks := edgeBlocks% "full/vectors/011000-V-0012.bin"
private noncomputable def vp011000_13 : Blocks := edgeBlocks% "full/vectors/011000-V-0013.bin"
private noncomputable def vp011000_14 : Blocks := edgeBlocks% "full/vectors/011000-V-0014.bin"
private noncomputable def vp011000_15 : Blocks := edgeBlocks% "full/vectors/011000-V-0015.bin"
private noncomputable def vp011000_16 : Blocks := edgeBlocks% "full/vectors/011000-V-0016.bin"
private noncomputable def vp011000_17 : Blocks := edgeBlocks% "full/vectors/011000-V-0017.bin"
noncomputable def vp011000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011000_0 vp011000_1) (Blocks.join vp011000_2 vp011000_3)) (Blocks.join (Blocks.join vp011000_4 vp011000_5) (Blocks.join vp011000_6 (Blocks.join vp011000_7 vp011000_8)))) (Blocks.join (Blocks.join (Blocks.join vp011000_9 vp011000_10) (Blocks.join vp011000_11 vp011000_12)) (Blocks.join (Blocks.join vp011000_13 vp011000_14) (Blocks.join vp011000_15 (Blocks.join vp011000_16 vp011000_17)))))
private theorem bp0110000 : Branch 0 (-3071761639/128000000 : ℚ) vp011000 := by
  apply branch_left_normalized (c:=vp0110000) (k:=0) (m:=1139) (by decide +kernel)
  rw [show 2*(-3071761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/64000000 : ℚ) by norm_num]
  exact coverp0110000
private noncomputable def ep0110001_0 : Blocks := edgeBlocks% "full/vectors/0110001-E-0000.bin"
private noncomputable def ep0110001_1 : Blocks := edgeBlocks% "full/vectors/0110001-E-0001.bin"
private noncomputable def ep0110001_2 : Blocks := edgeBlocks% "full/vectors/0110001-E-0002.bin"
private noncomputable def ep0110001_3 : Blocks := edgeBlocks% "full/vectors/0110001-E-0003.bin"
private noncomputable def ep0110001_4 : Blocks := edgeBlocks% "full/vectors/0110001-E-0004.bin"
private noncomputable def ep0110001_5 : Blocks := edgeBlocks% "full/vectors/0110001-E-0005.bin"
private noncomputable def ep0110001_6 : Blocks := edgeBlocks% "full/vectors/0110001-E-0006.bin"
private noncomputable def ep0110001_7 : Blocks := edgeBlocks% "full/vectors/0110001-E-0007.bin"
private noncomputable def ep0110001_8 : Blocks := edgeBlocks% "full/vectors/0110001-E-0008.bin"
private noncomputable def ep0110001_9 : Blocks := edgeBlocks% "full/vectors/0110001-E-0009.bin"
private noncomputable def ep0110001_10 : Blocks := edgeBlocks% "full/vectors/0110001-E-0010.bin"
private noncomputable def ep0110001_11 : Blocks := edgeBlocks% "full/vectors/0110001-E-0011.bin"
private noncomputable def ep0110001_12 : Blocks := edgeBlocks% "full/vectors/0110001-E-0012.bin"
private noncomputable def ep0110001_13 : Blocks := edgeBlocks% "full/vectors/0110001-E-0013.bin"
private noncomputable def ep0110001_14 : Blocks := edgeBlocks% "full/vectors/0110001-E-0014.bin"
private noncomputable def ep0110001_15 : Blocks := edgeBlocks% "full/vectors/0110001-E-0015.bin"
private noncomputable def ep0110001_16 : Blocks := edgeBlocks% "full/vectors/0110001-E-0016.bin"
private noncomputable def ep0110001_17 : Blocks := edgeBlocks% "full/vectors/0110001-E-0017.bin"
noncomputable def ep0110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0110001_0 ep0110001_1) (Blocks.join ep0110001_2 ep0110001_3)) (Blocks.join (Blocks.join ep0110001_4 ep0110001_5) (Blocks.join ep0110001_6 (Blocks.join ep0110001_7 ep0110001_8)))) (Blocks.join (Blocks.join (Blocks.join ep0110001_9 ep0110001_10) (Blocks.join ep0110001_11 ep0110001_12)) (Blocks.join (Blocks.join ep0110001_13 ep0110001_14) (Blocks.join ep0110001_15 (Blocks.join ep0110001_16 ep0110001_17)))))
private theorem idp0110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011000.list =
    C ((2:ℤ)^2588) * horner X vp0110001.list + horner X ep0110001.list := by
  exact edge_identity (B := (2:ℤ)^3509) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110001 : Branch 1 (-3071761639/128000000 : ℚ) vp011000 := by
  apply branch_checked idp0110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3135761639/64000000 : ℚ) by norm_num]
  exact coverp0110001
theorem coverp011000 : Covers (-3071761639/128000000 : ℚ) vp011000 := join_branches bp0110000 bp0110001
private noncomputable def vp01100_0 : Blocks := edgeBlocks% "full/vectors/01100-V-0000.bin"
private noncomputable def vp01100_1 : Blocks := edgeBlocks% "full/vectors/01100-V-0001.bin"
private noncomputable def vp01100_2 : Blocks := edgeBlocks% "full/vectors/01100-V-0002.bin"
private noncomputable def vp01100_3 : Blocks := edgeBlocks% "full/vectors/01100-V-0003.bin"
private noncomputable def vp01100_4 : Blocks := edgeBlocks% "full/vectors/01100-V-0004.bin"
private noncomputable def vp01100_5 : Blocks := edgeBlocks% "full/vectors/01100-V-0005.bin"
private noncomputable def vp01100_6 : Blocks := edgeBlocks% "full/vectors/01100-V-0006.bin"
private noncomputable def vp01100_7 : Blocks := edgeBlocks% "full/vectors/01100-V-0007.bin"
private noncomputable def vp01100_8 : Blocks := edgeBlocks% "full/vectors/01100-V-0008.bin"
private noncomputable def vp01100_9 : Blocks := edgeBlocks% "full/vectors/01100-V-0009.bin"
private noncomputable def vp01100_10 : Blocks := edgeBlocks% "full/vectors/01100-V-0010.bin"
private noncomputable def vp01100_11 : Blocks := edgeBlocks% "full/vectors/01100-V-0011.bin"
private noncomputable def vp01100_12 : Blocks := edgeBlocks% "full/vectors/01100-V-0012.bin"
private noncomputable def vp01100_13 : Blocks := edgeBlocks% "full/vectors/01100-V-0013.bin"
private noncomputable def vp01100_14 : Blocks := edgeBlocks% "full/vectors/01100-V-0014.bin"
private noncomputable def vp01100_15 : Blocks := edgeBlocks% "full/vectors/01100-V-0015.bin"
private noncomputable def vp01100_16 : Blocks := edgeBlocks% "full/vectors/01100-V-0016.bin"
private noncomputable def vp01100_17 : Blocks := edgeBlocks% "full/vectors/01100-V-0017.bin"
private noncomputable def vp01100_18 : Blocks := edgeBlocks% "full/vectors/01100-V-0018.bin"
private noncomputable def vp01100_19 : Blocks := edgeBlocks% "full/vectors/01100-V-0019.bin"
private noncomputable def vp01100_20 : Blocks := edgeBlocks% "full/vectors/01100-V-0020.bin"
private noncomputable def vp01100_21 : Blocks := edgeBlocks% "full/vectors/01100-V-0021.bin"
private noncomputable def vp01100_22 : Blocks := edgeBlocks% "full/vectors/01100-V-0022.bin"
private noncomputable def vp01100_23 : Blocks := edgeBlocks% "full/vectors/01100-V-0023.bin"
private noncomputable def vp01100_24 : Blocks := edgeBlocks% "full/vectors/01100-V-0024.bin"
private noncomputable def vp01100_25 : Blocks := edgeBlocks% "full/vectors/01100-V-0025.bin"
private noncomputable def vp01100_26 : Blocks := edgeBlocks% "full/vectors/01100-V-0026.bin"
private noncomputable def vp01100_27 : Blocks := edgeBlocks% "full/vectors/01100-V-0027.bin"
private noncomputable def vp01100_28 : Blocks := edgeBlocks% "full/vectors/01100-V-0028.bin"
private noncomputable def vp01100_29 : Blocks := edgeBlocks% "full/vectors/01100-V-0029.bin"
private noncomputable def vp01100_30 : Blocks := edgeBlocks% "full/vectors/01100-V-0030.bin"
private noncomputable def vp01100_31 : Blocks := edgeBlocks% "full/vectors/01100-V-0031.bin"
private noncomputable def vp01100_32 : Blocks := edgeBlocks% "full/vectors/01100-V-0032.bin"
private noncomputable def vp01100_33 : Blocks := edgeBlocks% "full/vectors/01100-V-0033.bin"
noncomputable def vp01100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01100_0 vp01100_1) (Blocks.join vp01100_2 vp01100_3)) (Blocks.join (Blocks.join vp01100_4 vp01100_5) (Blocks.join vp01100_6 vp01100_7))) (Blocks.join (Blocks.join (Blocks.join vp01100_8 vp01100_9) (Blocks.join vp01100_10 vp01100_11)) (Blocks.join (Blocks.join vp01100_12 vp01100_13) (Blocks.join vp01100_14 (Blocks.join vp01100_15 vp01100_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01100_17 vp01100_18) (Blocks.join vp01100_19 vp01100_20)) (Blocks.join (Blocks.join vp01100_21 vp01100_22) (Blocks.join vp01100_23 vp01100_24))) (Blocks.join (Blocks.join (Blocks.join vp01100_25 vp01100_26) (Blocks.join vp01100_27 vp01100_28)) (Blocks.join (Blocks.join vp01100_29 vp01100_30) (Blocks.join vp01100_31 (Blocks.join vp01100_32 vp01100_33))))))
private theorem bp011000 : Branch 0 (-3071761639/256000000 : ℚ) vp01100 := by
  apply branch_left_normalized (c:=vp011000) (k:=0) (m:=2216) (by decide +kernel)
  rw [show 2*(-3071761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/128000000 : ℚ) by norm_num]
  exact coverp011000
private noncomputable def ep011001_0 : Blocks := edgeBlocks% "full/vectors/011001-E-0000.bin"
private noncomputable def ep011001_1 : Blocks := edgeBlocks% "full/vectors/011001-E-0001.bin"
private noncomputable def ep011001_2 : Blocks := edgeBlocks% "full/vectors/011001-E-0002.bin"
private noncomputable def ep011001_3 : Blocks := edgeBlocks% "full/vectors/011001-E-0003.bin"
private noncomputable def ep011001_4 : Blocks := edgeBlocks% "full/vectors/011001-E-0004.bin"
private noncomputable def ep011001_5 : Blocks := edgeBlocks% "full/vectors/011001-E-0005.bin"
private noncomputable def ep011001_6 : Blocks := edgeBlocks% "full/vectors/011001-E-0006.bin"
private noncomputable def ep011001_7 : Blocks := edgeBlocks% "full/vectors/011001-E-0007.bin"
private noncomputable def ep011001_8 : Blocks := edgeBlocks% "full/vectors/011001-E-0008.bin"
private noncomputable def ep011001_9 : Blocks := edgeBlocks% "full/vectors/011001-E-0009.bin"
private noncomputable def ep011001_10 : Blocks := edgeBlocks% "full/vectors/011001-E-0010.bin"
private noncomputable def ep011001_11 : Blocks := edgeBlocks% "full/vectors/011001-E-0011.bin"
private noncomputable def ep011001_12 : Blocks := edgeBlocks% "full/vectors/011001-E-0012.bin"
private noncomputable def ep011001_13 : Blocks := edgeBlocks% "full/vectors/011001-E-0013.bin"
private noncomputable def ep011001_14 : Blocks := edgeBlocks% "full/vectors/011001-E-0014.bin"
private noncomputable def ep011001_15 : Blocks := edgeBlocks% "full/vectors/011001-E-0015.bin"
private noncomputable def ep011001_16 : Blocks := edgeBlocks% "full/vectors/011001-E-0016.bin"
private noncomputable def ep011001_17 : Blocks := edgeBlocks% "full/vectors/011001-E-0017.bin"
private noncomputable def ep011001_18 : Blocks := edgeBlocks% "full/vectors/011001-E-0018.bin"
private noncomputable def ep011001_19 : Blocks := edgeBlocks% "full/vectors/011001-E-0019.bin"
private noncomputable def ep011001_20 : Blocks := edgeBlocks% "full/vectors/011001-E-0020.bin"
private noncomputable def ep011001_21 : Blocks := edgeBlocks% "full/vectors/011001-E-0021.bin"
private noncomputable def ep011001_22 : Blocks := edgeBlocks% "full/vectors/011001-E-0022.bin"
private noncomputable def ep011001_23 : Blocks := edgeBlocks% "full/vectors/011001-E-0023.bin"
private noncomputable def ep011001_24 : Blocks := edgeBlocks% "full/vectors/011001-E-0024.bin"
private noncomputable def ep011001_25 : Blocks := edgeBlocks% "full/vectors/011001-E-0025.bin"
private noncomputable def ep011001_26 : Blocks := edgeBlocks% "full/vectors/011001-E-0026.bin"
private noncomputable def ep011001_27 : Blocks := edgeBlocks% "full/vectors/011001-E-0027.bin"
private noncomputable def ep011001_28 : Blocks := edgeBlocks% "full/vectors/011001-E-0028.bin"
private noncomputable def ep011001_29 : Blocks := edgeBlocks% "full/vectors/011001-E-0029.bin"
private noncomputable def ep011001_30 : Blocks := edgeBlocks% "full/vectors/011001-E-0030.bin"
private noncomputable def ep011001_31 : Blocks := edgeBlocks% "full/vectors/011001-E-0031.bin"
private noncomputable def ep011001_32 : Blocks := edgeBlocks% "full/vectors/011001-E-0032.bin"
private noncomputable def ep011001_33 : Blocks := edgeBlocks% "full/vectors/011001-E-0033.bin"
noncomputable def ep011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011001_0 ep011001_1) (Blocks.join ep011001_2 ep011001_3)) (Blocks.join (Blocks.join ep011001_4 ep011001_5) (Blocks.join ep011001_6 ep011001_7))) (Blocks.join (Blocks.join (Blocks.join ep011001_8 ep011001_9) (Blocks.join ep011001_10 ep011001_11)) (Blocks.join (Blocks.join ep011001_12 ep011001_13) (Blocks.join ep011001_14 (Blocks.join ep011001_15 ep011001_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011001_17 ep011001_18) (Blocks.join ep011001_19 ep011001_20)) (Blocks.join (Blocks.join ep011001_21 ep011001_22) (Blocks.join ep011001_23 ep011001_24))) (Blocks.join (Blocks.join (Blocks.join ep011001_25 ep011001_26) (Blocks.join ep011001_27 ep011001_28)) (Blocks.join (Blocks.join ep011001_29 ep011001_30) (Blocks.join ep011001_31 (Blocks.join ep011001_32 ep011001_33))))))
private def ptsp011001 : List ℤ := [((2:ℤ)^2819+0),((2:ℤ)^2819+1),((2:ℤ)^2819+2)]
private theorem boundp011001 : 2^vp01100.size*absSum vp01100.list + ((2:ℤ)^4995*absSum vp011001.list+absSum ep011001.list) < (2:ℤ)^6709 := by decide +kernel
private theorem pointp011001_0 : fastHom 1 ((2:ℤ)^2819+0) vp01100 = ((2:ℤ)^4995)*vp011001.subst ((2:ℤ)^2819+0)+ep011001.subst ((2:ℤ)^2819+0) := by decide +kernel
private theorem pointp011001_1 : fastHom 1 ((2:ℤ)^2819+1) vp01100 = ((2:ℤ)^4995)*vp011001.subst ((2:ℤ)^2819+1)+ep011001.subst ((2:ℤ)^2819+1) := by decide +kernel
private theorem pointp011001_2 : fastHom 1 ((2:ℤ)^2819+2) vp01100 = ((2:ℤ)^4995)*vp011001.subst ((2:ℤ)^2819+2)+ep011001.subst ((2:ℤ)^2819+2) := by decide +kernel
private theorem checkp011001 (x:ℤ) (hx:x ∈ ptsp011001) : fastHom 1 x vp01100 = ((2:ℤ)^4995)*vp011001.subst x+ep011001.subst x := by
  simp only [ptsp011001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp011001_0
  · exact pointp011001_1
  · exact pointp011001_2
private theorem idp011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100.list =
    C ((2:ℤ)^4995) * horner X vp011001.list + horner X ep011001.list := by
  apply edge_identity (B := (2:ℤ)^6709) (by decide) (by positivity) (by positivity) boundp011001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp011001 (by decide +kernel)
  · have h : ptsp011001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp011001.trans_le (by decide +kernel)
  · exact checkp011001
private theorem bp011001 : Branch 1 (-3071761639/256000000 : ℚ) vp01100 := by
  apply branch_checked idp011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-3199761639/128000000 : ℚ) by norm_num]
  exact coverp011001
theorem coverp01100 : Covers (-3071761639/256000000 : ℚ) vp01100 := join_branches bp011000 bp011001
end NextProof.EdgeFull

