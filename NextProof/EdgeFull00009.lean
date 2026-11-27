import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111111-V-0000.bin"
noncomputable def vp0000000000101111111 : Blocks := vp0000000000101111111_0
theorem coverp0000000000101111111 : Covers (-5746014/15625 : ℚ) vp0000000000101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111110-V-0000.bin"
noncomputable def vp0000000000101111110 : Blocks := vp0000000000101111110_0
theorem coverp0000000000101111110 : Covers (-5730389/15625 : ℚ) vp0000000000101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111111-V-0000.bin"
noncomputable def vp000000000010111111 : Blocks := vp000000000010111111_0
private theorem bp0000000000101111110 : Branch 0 (-5730389/31250 : ℚ) vp000000000010111111 := by
  apply branch_left_normalized (c:=vp0000000000101111110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-5730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5730389/15625 : ℚ) by norm_num]
  exact coverp0000000000101111110
private noncomputable def ep0000000000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111111-E-0000.bin"
noncomputable def ep0000000000101111111 : Blocks := ep0000000000101111111_0
private theorem idp0000000000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111111.list =
    C ((2:ℤ)^26) * horner X vp0000000000101111111.list + horner X ep0000000000101111111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111111 : Branch 1 (-5730389/31250 : ℚ) vp000000000010111111 := by
  apply branch_checked idp0000000000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5746014/15625 : ℚ) by norm_num]
  exact coverp0000000000101111111
theorem coverp000000000010111111 : Covers (-5730389/31250 : ℚ) vp000000000010111111 := join_branches bp0000000000101111110 bp0000000000101111111
private noncomputable def vp000000000010111110_0 : Blocks := edgeBlocks% "full/vectors/000000000010111110-V-0000.bin"
noncomputable def vp000000000010111110 : Blocks := vp000000000010111110_0
theorem coverp000000000010111110 : Covers (-5699139/31250 : ℚ) vp000000000010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011111-V-0000.bin"
noncomputable def vp00000000001011111 : Blocks := vp00000000001011111_0
private theorem bp000000000010111110 : Branch 0 (-5699139/62500 : ℚ) vp00000000001011111 := by
  apply branch_left_normalized (c:=vp000000000010111110) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-5699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5699139/31250 : ℚ) by norm_num]
  exact coverp000000000010111110
private noncomputable def ep000000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111111-E-0000.bin"
noncomputable def ep000000000010111111 : Blocks := ep000000000010111111_0
private theorem idp000000000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011111.list =
    C ((2:ℤ)^42) * horner X vp000000000010111111.list + horner X ep000000000010111111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111111 : Branch 1 (-5699139/62500 : ℚ) vp00000000001011111 := by
  apply branch_checked idp000000000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5730389/31250 : ℚ) by norm_num]
  exact coverp000000000010111111
theorem coverp00000000001011111 : Covers (-5699139/62500 : ℚ) vp00000000001011111 := join_branches bp000000000010111110 bp000000000010111111
private noncomputable def vp0000000000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111011-V-0000.bin"
noncomputable def vp0000000000101111011 : Blocks := vp0000000000101111011_0
theorem coverp0000000000101111011 : Covers (-5683514/15625 : ℚ) vp0000000000101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011110101_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110101-V-0000.bin"
noncomputable def vp00000000001011110101 : Blocks := vp00000000001011110101_0
theorem coverp00000000001011110101 : Covers (-11351403/15625 : ℚ) vp00000000001011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111101001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101001-V-0000.bin"
noncomputable def vp000000000010111101001 : Blocks := vp000000000010111101001_0
theorem coverp000000000010111101001 : Covers (-22687181/15625 : ℚ) vp000000000010111101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101111010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010001-V-0000.bin"
noncomputable def vp0000000000101111010001 : Blocks := vp0000000000101111010001_0
theorem coverp0000000000101111010001 : Covers (-45358737/15625 : ℚ) vp0000000000101111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111101000011_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000011-V-0000.bin"
noncomputable def vp000000000010111101000011 : Blocks := vp000000000010111101000011_0
theorem coverp000000000010111101000011 : Covers (-181419323/15625 : ℚ) vp000000000010111101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111101000010_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000010-V-0000.bin"
noncomputable def vp000000000010111101000010 : Blocks := vp000000000010111101000010_0
theorem coverp000000000010111101000010 : Covers (-181403698/15625 : ℚ) vp000000000010111101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011110100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110100001-V-0000.bin"
noncomputable def vp00000000001011110100001 : Blocks := vp00000000001011110100001_0
private theorem bp000000000010111101000010 : Branch 0 (-90701849/15625 : ℚ) vp00000000001011110100001 := by
  apply branch_left_normalized (c:=vp000000000010111101000010) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-90701849/15625 : ℚ) - ((0:ℤ):ℚ) = (-181403698/15625 : ℚ) by norm_num]
  exact coverp000000000010111101000010
private noncomputable def ep000000000010111101000011_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000011-E-0000.bin"
noncomputable def ep000000000010111101000011 : Blocks := ep000000000010111101000011_0
private theorem idp000000000010111101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011110100001.list =
    C ((2:ℤ)^11) * horner X vp000000000010111101000011.list + horner X ep000000000010111101000011.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111101000011 : Branch 1 (-90701849/15625 : ℚ) vp00000000001011110100001 := by
  apply branch_checked idp000000000010111101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-90701849/15625 : ℚ) - ((1:ℤ):ℚ) = (-181419323/15625 : ℚ) by norm_num]
  exact coverp000000000010111101000011
theorem coverp00000000001011110100001 : Covers (-90701849/15625 : ℚ) vp00000000001011110100001 := join_branches bp000000000010111101000010 bp000000000010111101000011
private noncomputable def vp0000000000101111010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010000011-V-0000.bin"
noncomputable def vp0000000000101111010000011 : Blocks := vp0000000000101111010000011_0
theorem coverp0000000000101111010000011 : Covers (-362791771/15625 : ℚ) vp0000000000101111010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101111010000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010000010-V-0000.bin"
noncomputable def vp0000000000101111010000010 : Blocks := vp0000000000101111010000010_0
theorem coverp0000000000101111010000010 : Covers (-362776146/15625 : ℚ) vp0000000000101111010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111101000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000001-V-0000.bin"
noncomputable def vp000000000010111101000001 : Blocks := vp000000000010111101000001_0
private theorem bp0000000000101111010000010 : Branch 0 (-181388073/15625 : ℚ) vp000000000010111101000001 := by
  apply branch_left_normalized (c:=vp0000000000101111010000010) (k:=0) (m:=7) (by decide +kernel)
  rw [show 2*(-181388073/15625 : ℚ) - ((0:ℤ):ℚ) = (-362776146/15625 : ℚ) by norm_num]
  exact coverp0000000000101111010000010
private noncomputable def ep0000000000101111010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010000011-E-0000.bin"
noncomputable def ep0000000000101111010000011 : Blocks := ep0000000000101111010000011_0
private theorem idp0000000000101111010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111101000001.list =
    C ((2:ℤ)^9) * horner X vp0000000000101111010000011.list + horner X ep0000000000101111010000011.list := by
  exact edge_identity (B := (2:ℤ)^112) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111010000011 : Branch 1 (-181388073/15625 : ℚ) vp000000000010111101000001 := by
  apply branch_checked idp0000000000101111010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-181388073/15625 : ℚ) - ((1:ℤ):ℚ) = (-362791771/15625 : ℚ) by norm_num]
  exact coverp0000000000101111010000011
theorem coverp000000000010111101000001 : Covers (-181388073/15625 : ℚ) vp000000000010111101000001 := join_branches bp0000000000101111010000010 bp0000000000101111010000011
private noncomputable def vp000000000010111101000000_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000000-V-0000.bin"
noncomputable def vp000000000010111101000000 : Blocks := vp000000000010111101000000_0
theorem coverp000000000010111101000000 : Covers (-181372448/15625 : ℚ) vp000000000010111101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011110100000_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110100000-V-0000.bin"
noncomputable def vp00000000001011110100000 : Blocks := vp00000000001011110100000_0
private theorem bp000000000010111101000000 : Branch 0 (-90686224/15625 : ℚ) vp00000000001011110100000 := by
  apply branch_left_normalized (c:=vp000000000010111101000000) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-90686224/15625 : ℚ) - ((0:ℤ):ℚ) = (-181372448/15625 : ℚ) by norm_num]
  exact coverp000000000010111101000000
private noncomputable def ep000000000010111101000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000001-E-0000.bin"
noncomputable def ep000000000010111101000001 : Blocks := ep000000000010111101000001_0
private theorem idp000000000010111101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011110100000.list =
    C ((2:ℤ)^10) * horner X vp000000000010111101000001.list + horner X ep000000000010111101000001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111101000001 : Branch 1 (-90686224/15625 : ℚ) vp00000000001011110100000 := by
  apply branch_checked idp000000000010111101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-90686224/15625 : ℚ) - ((1:ℤ):ℚ) = (-181388073/15625 : ℚ) by norm_num]
  exact coverp000000000010111101000001
theorem coverp00000000001011110100000 : Covers (-90686224/15625 : ℚ) vp00000000001011110100000 := join_branches bp000000000010111101000000 bp000000000010111101000001
private noncomputable def vp0000000000101111010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010000-V-0000.bin"
noncomputable def vp0000000000101111010000 : Blocks := vp0000000000101111010000_0
private theorem bp00000000001011110100000 : Branch 0 (-45343112/15625 : ℚ) vp0000000000101111010000 := by
  apply branch_left_normalized (c:=vp00000000001011110100000) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-45343112/15625 : ℚ) - ((0:ℤ):ℚ) = (-90686224/15625 : ℚ) by norm_num]
  exact coverp00000000001011110100000
private noncomputable def ep00000000001011110100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110100001-E-0000.bin"
noncomputable def ep00000000001011110100001 : Blocks := ep00000000001011110100001_0
private theorem idp00000000001011110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101111010000.list =
    C ((2:ℤ)^12) * horner X vp00000000001011110100001.list + horner X ep00000000001011110100001.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011110100001 : Branch 1 (-45343112/15625 : ℚ) vp0000000000101111010000 := by
  apply branch_checked idp00000000001011110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-45343112/15625 : ℚ) - ((1:ℤ):ℚ) = (-90701849/15625 : ℚ) by norm_num]
  exact coverp00000000001011110100001
theorem coverp0000000000101111010000 : Covers (-45343112/15625 : ℚ) vp0000000000101111010000 := join_branches bp00000000001011110100000 bp00000000001011110100001
private noncomputable def vp000000000010111101000_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101000-V-0000.bin"
noncomputable def vp000000000010111101000 : Blocks := vp000000000010111101000_0
private theorem bp0000000000101111010000 : Branch 0 (-22671556/15625 : ℚ) vp000000000010111101000 := by
  apply branch_left_normalized (c:=vp0000000000101111010000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-22671556/15625 : ℚ) - ((0:ℤ):ℚ) = (-45343112/15625 : ℚ) by norm_num]
  exact coverp0000000000101111010000
private noncomputable def ep0000000000101111010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010001-E-0000.bin"
noncomputable def ep0000000000101111010001 : Blocks := ep0000000000101111010001_0
private theorem idp0000000000101111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111101000.list =
    C ((2:ℤ)^14) * horner X vp0000000000101111010001.list + horner X ep0000000000101111010001.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111010001 : Branch 1 (-22671556/15625 : ℚ) vp000000000010111101000 := by
  apply branch_checked idp0000000000101111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-22671556/15625 : ℚ) - ((1:ℤ):ℚ) = (-45358737/15625 : ℚ) by norm_num]
  exact coverp0000000000101111010001
theorem coverp000000000010111101000 : Covers (-22671556/15625 : ℚ) vp000000000010111101000 := join_branches bp0000000000101111010000 bp0000000000101111010001
private noncomputable def vp00000000001011110100_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110100-V-0000.bin"
noncomputable def vp00000000001011110100 : Blocks := vp00000000001011110100_0
private theorem bp000000000010111101000 : Branch 0 (-11335778/15625 : ℚ) vp00000000001011110100 := by
  apply branch_left_normalized (c:=vp000000000010111101000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11335778/15625 : ℚ) - ((0:ℤ):ℚ) = (-22671556/15625 : ℚ) by norm_num]
  exact coverp000000000010111101000
private noncomputable def ep000000000010111101001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101001-E-0000.bin"
noncomputable def ep000000000010111101001 : Blocks := ep000000000010111101001_0
private theorem idp000000000010111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011110100.list =
    C ((2:ℤ)^17) * horner X vp000000000010111101001.list + horner X ep000000000010111101001.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111101001 : Branch 1 (-11335778/15625 : ℚ) vp00000000001011110100 := by
  apply branch_checked idp000000000010111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-11335778/15625 : ℚ) - ((1:ℤ):ℚ) = (-22687181/15625 : ℚ) by norm_num]
  exact coverp000000000010111101001
theorem coverp00000000001011110100 : Covers (-11335778/15625 : ℚ) vp00000000001011110100 := join_branches bp000000000010111101000 bp000000000010111101001
private noncomputable def vp0000000000101111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111010-V-0000.bin"
noncomputable def vp0000000000101111010 : Blocks := vp0000000000101111010_0
private theorem bp00000000001011110100 : Branch 0 (-5667889/15625 : ℚ) vp0000000000101111010 := by
  apply branch_left_normalized (c:=vp00000000001011110100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5667889/15625 : ℚ) - ((0:ℤ):ℚ) = (-11335778/15625 : ℚ) by norm_num]
  exact coverp00000000001011110100
private noncomputable def ep00000000001011110101_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110101-E-0000.bin"
noncomputable def ep00000000001011110101 : Blocks := ep00000000001011110101_0
private theorem idp00000000001011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101111010.list =
    C ((2:ℤ)^21) * horner X vp00000000001011110101.list + horner X ep00000000001011110101.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011110101 : Branch 1 (-5667889/15625 : ℚ) vp0000000000101111010 := by
  apply branch_checked idp00000000001011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5667889/15625 : ℚ) - ((1:ℤ):ℚ) = (-11351403/15625 : ℚ) by norm_num]
  exact coverp00000000001011110101
theorem coverp0000000000101111010 : Covers (-5667889/15625 : ℚ) vp0000000000101111010 := join_branches bp00000000001011110100 bp00000000001011110101
private noncomputable def vp000000000010111101_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101-V-0000.bin"
noncomputable def vp000000000010111101 : Blocks := vp000000000010111101_0
private theorem bp0000000000101111010 : Branch 0 (-5667889/31250 : ℚ) vp000000000010111101 := by
  apply branch_left_normalized (c:=vp0000000000101111010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-5667889/31250 : ℚ) - ((0:ℤ):ℚ) = (-5667889/15625 : ℚ) by norm_num]
  exact coverp0000000000101111010
private noncomputable def ep0000000000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111011-E-0000.bin"
noncomputable def ep0000000000101111011 : Blocks := ep0000000000101111011_0
private theorem idp0000000000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111101.list =
    C ((2:ℤ)^30) * horner X vp0000000000101111011.list + horner X ep0000000000101111011.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111011 : Branch 1 (-5667889/31250 : ℚ) vp000000000010111101 := by
  apply branch_checked idp0000000000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5667889/31250 : ℚ) - ((1:ℤ):ℚ) = (-5683514/15625 : ℚ) by norm_num]
  exact coverp0000000000101111011
theorem coverp000000000010111101 : Covers (-5667889/31250 : ℚ) vp000000000010111101 := join_branches bp0000000000101111010 bp0000000000101111011
private noncomputable def vp00000000001011110011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110011111-V-0000.bin"
noncomputable def vp00000000001011110011111 : Blocks := vp00000000001011110011111_0
theorem coverp00000000001011110011111 : Covers (-90670599/15625 : ℚ) vp00000000001011110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011110011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110011110-V-0000.bin"
noncomputable def vp00000000001011110011110 : Blocks := vp00000000001011110011110_0
theorem coverp00000000001011110011110 : Covers (-90654974/15625 : ℚ) vp00000000001011110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111001111-V-0000.bin"
noncomputable def vp0000000000101111001111 : Blocks := vp0000000000101111001111_0
private theorem bp00000000001011110011110 : Branch 0 (-45327487/15625 : ℚ) vp0000000000101111001111 := by
  apply branch_left_normalized (c:=vp00000000001011110011110) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-45327487/15625 : ℚ) - ((0:ℤ):ℚ) = (-90654974/15625 : ℚ) by norm_num]
  exact coverp00000000001011110011110
private noncomputable def ep00000000001011110011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110011111-E-0000.bin"
noncomputable def ep00000000001011110011111 : Blocks := ep00000000001011110011111_0
private theorem idp00000000001011110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101111001111.list =
    C ((2:ℤ)^11) * horner X vp00000000001011110011111.list + horner X ep00000000001011110011111.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011110011111 : Branch 1 (-45327487/15625 : ℚ) vp0000000000101111001111 := by
  apply branch_checked idp00000000001011110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-45327487/15625 : ℚ) - ((1:ℤ):ℚ) = (-90670599/15625 : ℚ) by norm_num]
  exact coverp00000000001011110011111
theorem coverp0000000000101111001111 : Covers (-45327487/15625 : ℚ) vp0000000000101111001111 := join_branches bp00000000001011110011110 bp00000000001011110011111
private noncomputable def vp0000000000101111001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111001110-V-0000.bin"
noncomputable def vp0000000000101111001110 : Blocks := vp0000000000101111001110_0
theorem coverp0000000000101111001110 : Covers (-45311862/15625 : ℚ) vp0000000000101111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111100111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111100111-V-0000.bin"
noncomputable def vp000000000010111100111 : Blocks := vp000000000010111100111_0
private theorem bp0000000000101111001110 : Branch 0 (-22655931/15625 : ℚ) vp000000000010111100111 := by
  apply branch_left_normalized (c:=vp0000000000101111001110) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-22655931/15625 : ℚ) - ((0:ℤ):ℚ) = (-45311862/15625 : ℚ) by norm_num]
  exact coverp0000000000101111001110
private noncomputable def ep0000000000101111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111001111-E-0000.bin"
noncomputable def ep0000000000101111001111 : Blocks := ep0000000000101111001111_0
private theorem idp0000000000101111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111100111.list =
    C ((2:ℤ)^13) * horner X vp0000000000101111001111.list + horner X ep0000000000101111001111.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111001111 : Branch 1 (-22655931/15625 : ℚ) vp000000000010111100111 := by
  apply branch_checked idp0000000000101111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-22655931/15625 : ℚ) - ((1:ℤ):ℚ) = (-45327487/15625 : ℚ) by norm_num]
  exact coverp0000000000101111001111
theorem coverp000000000010111100111 : Covers (-22655931/15625 : ℚ) vp000000000010111100111 := join_branches bp0000000000101111001110 bp0000000000101111001111
private noncomputable def vp000000000010111100110_0 : Blocks := edgeBlocks% "full/vectors/000000000010111100110-V-0000.bin"
noncomputable def vp000000000010111100110 : Blocks := vp000000000010111100110_0
theorem coverp000000000010111100110 : Covers (-22640306/15625 : ℚ) vp000000000010111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011110011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110011-V-0000.bin"
noncomputable def vp00000000001011110011 : Blocks := vp00000000001011110011_0
private theorem bp000000000010111100110 : Branch 0 (-11320153/15625 : ℚ) vp00000000001011110011 := by
  apply branch_left_normalized (c:=vp000000000010111100110) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-11320153/15625 : ℚ) - ((0:ℤ):ℚ) = (-22640306/15625 : ℚ) by norm_num]
  exact coverp000000000010111100110
private noncomputable def ep000000000010111100111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111100111-E-0000.bin"
noncomputable def ep000000000010111100111 : Blocks := ep000000000010111100111_0
private theorem idp000000000010111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011110011.list =
    C ((2:ℤ)^16) * horner X vp000000000010111100111.list + horner X ep000000000010111100111.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111100111 : Branch 1 (-11320153/15625 : ℚ) vp00000000001011110011 := by
  apply branch_checked idp000000000010111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-11320153/15625 : ℚ) - ((1:ℤ):ℚ) = (-22655931/15625 : ℚ) by norm_num]
  exact coverp000000000010111100111
theorem coverp00000000001011110011 : Covers (-11320153/15625 : ℚ) vp00000000001011110011 := join_branches bp000000000010111100110 bp000000000010111100111
private noncomputable def vp00000000001011110010_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110010-V-0000.bin"
noncomputable def vp00000000001011110010 : Blocks := vp00000000001011110010_0
theorem coverp00000000001011110010 : Covers (-11304528/15625 : ℚ) vp00000000001011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111001-V-0000.bin"
noncomputable def vp0000000000101111001 : Blocks := vp0000000000101111001_0
private theorem bp00000000001011110010 : Branch 0 (-5652264/15625 : ℚ) vp0000000000101111001 := by
  apply branch_left_normalized (c:=vp00000000001011110010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5652264/15625 : ℚ) - ((0:ℤ):ℚ) = (-11304528/15625 : ℚ) by norm_num]
  exact coverp00000000001011110010
private noncomputable def ep00000000001011110011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110011-E-0000.bin"
noncomputable def ep00000000001011110011 : Blocks := ep00000000001011110011_0
private theorem idp00000000001011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101111001.list =
    C ((2:ℤ)^20) * horner X vp00000000001011110011.list + horner X ep00000000001011110011.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011110011 : Branch 1 (-5652264/15625 : ℚ) vp0000000000101111001 := by
  apply branch_checked idp00000000001011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5652264/15625 : ℚ) - ((1:ℤ):ℚ) = (-11320153/15625 : ℚ) by norm_num]
  exact coverp00000000001011110011
theorem coverp0000000000101111001 : Covers (-5652264/15625 : ℚ) vp0000000000101111001 := join_branches bp00000000001011110010 bp00000000001011110011
private noncomputable def vp0000000000101111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111000-V-0000.bin"
noncomputable def vp0000000000101111000 : Blocks := vp0000000000101111000_0
theorem coverp0000000000101111000 : Covers (-5636639/15625 : ℚ) vp0000000000101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111100_0 : Blocks := edgeBlocks% "full/vectors/000000000010111100-V-0000.bin"
noncomputable def vp000000000010111100 : Blocks := vp000000000010111100_0
private theorem bp0000000000101111000 : Branch 0 (-5636639/31250 : ℚ) vp000000000010111100 := by
  apply branch_left_normalized (c:=vp0000000000101111000) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-5636639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5636639/15625 : ℚ) by norm_num]
  exact coverp0000000000101111000
private noncomputable def ep0000000000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111001-E-0000.bin"
noncomputable def ep0000000000101111001 : Blocks := ep0000000000101111001_0
private theorem idp0000000000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111100.list =
    C ((2:ℤ)^26) * horner X vp0000000000101111001.list + horner X ep0000000000101111001.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111001 : Branch 1 (-5636639/31250 : ℚ) vp000000000010111100 := by
  apply branch_checked idp0000000000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5636639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5652264/15625 : ℚ) by norm_num]
  exact coverp0000000000101111001
theorem coverp000000000010111100 : Covers (-5636639/31250 : ℚ) vp000000000010111100 := join_branches bp0000000000101111000 bp0000000000101111001
private noncomputable def vp00000000001011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001011110-V-0000.bin"
noncomputable def vp00000000001011110 : Blocks := vp00000000001011110_0
private theorem bp000000000010111100 : Branch 0 (-5636639/62500 : ℚ) vp00000000001011110 := by
  apply branch_left_normalized (c:=vp000000000010111100) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-5636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5636639/31250 : ℚ) by norm_num]
  exact coverp000000000010111100
private noncomputable def ep000000000010111101_0 : Blocks := edgeBlocks% "full/vectors/000000000010111101-E-0000.bin"
noncomputable def ep000000000010111101 : Blocks := ep000000000010111101_0
private theorem idp000000000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011110.list =
    C ((2:ℤ)^41) * horner X vp000000000010111101.list + horner X ep000000000010111101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111101 : Branch 1 (-5636639/62500 : ℚ) vp00000000001011110 := by
  apply branch_checked idp000000000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5667889/31250 : ℚ) by norm_num]
  exact coverp000000000010111101
theorem coverp00000000001011110 : Covers (-5636639/62500 : ℚ) vp00000000001011110 := join_branches bp000000000010111100 bp000000000010111101
private noncomputable def vp0000000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111-V-0000.bin"
noncomputable def vp0000000000101111 : Blocks := vp0000000000101111_0
private theorem bp00000000001011110 : Branch 0 (-5636639/125000 : ℚ) vp0000000000101111 := by
  apply branch_left_normalized (c:=vp00000000001011110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-5636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5636639/62500 : ℚ) by norm_num]
  exact coverp00000000001011110
private noncomputable def ep00000000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011111-E-0000.bin"
noncomputable def ep00000000001011111 : Blocks := ep00000000001011111_0
private theorem idp00000000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101111.list =
    C ((2:ℤ)^70) * horner X vp00000000001011111.list + horner X ep00000000001011111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011111 : Branch 1 (-5636639/125000 : ℚ) vp0000000000101111 := by
  apply branch_checked idp00000000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5699139/62500 : ℚ) by norm_num]
  exact coverp00000000001011111
theorem coverp0000000000101111 : Covers (-5636639/125000 : ℚ) vp0000000000101111 := join_branches bp00000000001011110 bp00000000001011111
private noncomputable def vp000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000000010111011-V-0000.bin"
noncomputable def vp000000000010111011 : Blocks := vp000000000010111011_0
theorem coverp000000000010111011 : Covers (-5605389/31250 : ℚ) vp000000000010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111010_0 : Blocks := edgeBlocks% "full/vectors/000000000010111010-V-0000.bin"
noncomputable def vp000000000010111010 : Blocks := vp000000000010111010_0
theorem coverp000000000010111010 : Covers (-5574139/31250 : ℚ) vp000000000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001011101-V-0000.bin"
noncomputable def vp00000000001011101 : Blocks := vp00000000001011101_0
private theorem bp000000000010111010 : Branch 0 (-5574139/62500 : ℚ) vp00000000001011101 := by
  apply branch_left_normalized (c:=vp000000000010111010) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-5574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5574139/31250 : ℚ) by norm_num]
  exact coverp000000000010111010
private noncomputable def ep000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000000010111011-E-0000.bin"
noncomputable def ep000000000010111011 : Blocks := ep000000000010111011_0
private theorem idp000000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011101.list =
    C ((2:ℤ)^42) * horner X vp000000000010111011.list + horner X ep000000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111011 : Branch 1 (-5574139/62500 : ℚ) vp00000000001011101 := by
  apply branch_checked idp000000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5605389/31250 : ℚ) by norm_num]
  exact coverp000000000010111011
theorem coverp00000000001011101 : Covers (-5574139/62500 : ℚ) vp00000000001011101 := join_branches bp000000000010111010 bp000000000010111011
private noncomputable def vp000000000010111001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111001-V-0000.bin"
noncomputable def vp000000000010111001 : Blocks := vp000000000010111001_0
theorem coverp000000000010111001 : Covers (-5542889/31250 : ℚ) vp000000000010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110001-V-0000.bin"
noncomputable def vp0000000000101110001 : Blocks := vp0000000000101110001_0
theorem coverp0000000000101110001 : Covers (-5527264/15625 : ℚ) vp0000000000101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011100001-V-0000.bin"
noncomputable def vp00000000001011100001 : Blocks := vp00000000001011100001_0
theorem coverp00000000001011100001 : Covers (-11038903/15625 : ℚ) vp00000000001011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110000011-V-0000.bin"
noncomputable def vp0000000000101110000011 : Blocks := vp0000000000101110000011_0
theorem coverp0000000000101110000011 : Covers (-44139987/15625 : ℚ) vp0000000000101110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101110000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110000010-V-0000.bin"
noncomputable def vp0000000000101110000010 : Blocks := vp0000000000101110000010_0
theorem coverp0000000000101110000010 : Covers (-44124362/15625 : ℚ) vp0000000000101110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010111000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111000001-V-0000.bin"
noncomputable def vp000000000010111000001 : Blocks := vp000000000010111000001_0
private theorem bp0000000000101110000010 : Branch 0 (-22062181/15625 : ℚ) vp000000000010111000001 := by
  apply branch_left_normalized (c:=vp0000000000101110000010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-22062181/15625 : ℚ) - ((0:ℤ):ℚ) = (-44124362/15625 : ℚ) by norm_num]
  exact coverp0000000000101110000010
private noncomputable def ep0000000000101110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110000011-E-0000.bin"
noncomputable def ep0000000000101110000011 : Blocks := ep0000000000101110000011_0
private theorem idp0000000000101110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111000001.list =
    C ((2:ℤ)^14) * horner X vp0000000000101110000011.list + horner X ep0000000000101110000011.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101110000011 : Branch 1 (-22062181/15625 : ℚ) vp000000000010111000001 := by
  apply branch_checked idp0000000000101110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-22062181/15625 : ℚ) - ((1:ℤ):ℚ) = (-44139987/15625 : ℚ) by norm_num]
  exact coverp0000000000101110000011
theorem coverp000000000010111000001 : Covers (-22062181/15625 : ℚ) vp000000000010111000001 := join_branches bp0000000000101110000010 bp0000000000101110000011
private noncomputable def vp000000000010111000000_0 : Blocks := edgeBlocks% "full/vectors/000000000010111000000-V-0000.bin"
noncomputable def vp000000000010111000000 : Blocks := vp000000000010111000000_0
theorem coverp000000000010111000000 : Covers (-22046556/15625 : ℚ) vp000000000010111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011100000_0 : Blocks := edgeBlocks% "full/vectors/00000000001011100000-V-0000.bin"
noncomputable def vp00000000001011100000 : Blocks := vp00000000001011100000_0
private theorem bp000000000010111000000 : Branch 0 (-11023278/15625 : ℚ) vp00000000001011100000 := by
  apply branch_left_normalized (c:=vp000000000010111000000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11023278/15625 : ℚ) - ((0:ℤ):ℚ) = (-22046556/15625 : ℚ) by norm_num]
  exact coverp000000000010111000000
private noncomputable def ep000000000010111000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111000001-E-0000.bin"
noncomputable def ep000000000010111000001 : Blocks := ep000000000010111000001_0
private theorem idp000000000010111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011100000.list =
    C ((2:ℤ)^17) * horner X vp000000000010111000001.list + horner X ep000000000010111000001.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111000001 : Branch 1 (-11023278/15625 : ℚ) vp00000000001011100000 := by
  apply branch_checked idp000000000010111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-11023278/15625 : ℚ) - ((1:ℤ):ℚ) = (-22062181/15625 : ℚ) by norm_num]
  exact coverp000000000010111000001
theorem coverp00000000001011100000 : Covers (-11023278/15625 : ℚ) vp00000000001011100000 := join_branches bp000000000010111000000 bp000000000010111000001
private noncomputable def vp0000000000101110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110000-V-0000.bin"
noncomputable def vp0000000000101110000 : Blocks := vp0000000000101110000_0
private theorem bp00000000001011100000 : Branch 0 (-5511639/15625 : ℚ) vp0000000000101110000 := by
  apply branch_left_normalized (c:=vp00000000001011100000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5511639/15625 : ℚ) - ((0:ℤ):ℚ) = (-11023278/15625 : ℚ) by norm_num]
  exact coverp00000000001011100000
private noncomputable def ep00000000001011100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011100001-E-0000.bin"
noncomputable def ep00000000001011100001 : Blocks := ep00000000001011100001_0
private theorem idp00000000001011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101110000.list =
    C ((2:ℤ)^22) * horner X vp00000000001011100001.list + horner X ep00000000001011100001.list := by
  exact edge_identity (B := (2:ℤ)^136) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011100001 : Branch 1 (-5511639/15625 : ℚ) vp0000000000101110000 := by
  apply branch_checked idp00000000001011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5511639/15625 : ℚ) - ((1:ℤ):ℚ) = (-11038903/15625 : ℚ) by norm_num]
  exact coverp00000000001011100001
theorem coverp0000000000101110000 : Covers (-5511639/15625 : ℚ) vp0000000000101110000 := join_branches bp00000000001011100000 bp00000000001011100001
private noncomputable def vp000000000010111000_0 : Blocks := edgeBlocks% "full/vectors/000000000010111000-V-0000.bin"
noncomputable def vp000000000010111000 : Blocks := vp000000000010111000_0
private theorem bp0000000000101110000 : Branch 0 (-5511639/31250 : ℚ) vp000000000010111000 := by
  apply branch_left_normalized (c:=vp0000000000101110000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5511639/15625 : ℚ) by norm_num]
  exact coverp0000000000101110000
private noncomputable def ep0000000000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110001-E-0000.bin"
noncomputable def ep0000000000101110001 : Blocks := ep0000000000101110001_0
private theorem idp0000000000101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111000.list =
    C ((2:ℤ)^33) * horner X vp0000000000101110001.list + horner X ep0000000000101110001.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101110001 : Branch 1 (-5511639/31250 : ℚ) vp000000000010111000 := by
  apply branch_checked idp0000000000101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5527264/15625 : ℚ) by norm_num]
  exact coverp0000000000101110001
theorem coverp000000000010111000 : Covers (-5511639/31250 : ℚ) vp000000000010111000 := join_branches bp0000000000101110000 bp0000000000101110001
private noncomputable def vp00000000001011100_0 : Blocks := edgeBlocks% "full/vectors/00000000001011100-V-0000.bin"
noncomputable def vp00000000001011100 : Blocks := vp00000000001011100_0
private theorem bp000000000010111000 : Branch 0 (-5511639/62500 : ℚ) vp00000000001011100 := by
  apply branch_left_normalized (c:=vp000000000010111000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-5511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5511639/31250 : ℚ) by norm_num]
  exact coverp000000000010111000
private noncomputable def ep000000000010111001_0 : Blocks := edgeBlocks% "full/vectors/000000000010111001-E-0000.bin"
noncomputable def ep000000000010111001 : Blocks := ep000000000010111001_0
private theorem idp000000000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011100.list =
    C ((2:ℤ)^50) * horner X vp000000000010111001.list + horner X ep000000000010111001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111001 : Branch 1 (-5511639/62500 : ℚ) vp00000000001011100 := by
  apply branch_checked idp000000000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5542889/31250 : ℚ) by norm_num]
  exact coverp000000000010111001
theorem coverp00000000001011100 : Covers (-5511639/62500 : ℚ) vp00000000001011100 := join_branches bp000000000010111000 bp000000000010111001
private noncomputable def vp0000000000101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101110-V-0000.bin"
noncomputable def vp0000000000101110 : Blocks := vp0000000000101110_0
private theorem bp00000000001011100 : Branch 0 (-5511639/125000 : ℚ) vp0000000000101110 := by
  apply branch_left_normalized (c:=vp00000000001011100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-5511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5511639/62500 : ℚ) by norm_num]
  exact coverp00000000001011100
private noncomputable def ep00000000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001011101-E-0000.bin"
noncomputable def ep00000000001011101 : Blocks := ep00000000001011101_0
private theorem idp00000000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101110.list =
    C ((2:ℤ)^81) * horner X vp00000000001011101.list + horner X ep00000000001011101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011101 : Branch 1 (-5511639/125000 : ℚ) vp0000000000101110 := by
  apply branch_checked idp00000000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5574139/62500 : ℚ) by norm_num]
  exact coverp00000000001011101
theorem coverp0000000000101110 : Covers (-5511639/125000 : ℚ) vp0000000000101110 := join_branches bp00000000001011100 bp00000000001011101
private noncomputable def vp000000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111-V-0000.bin"
noncomputable def vp000000000010111 : Blocks := vp000000000010111_0
private theorem bp0000000000101110 : Branch 0 (-5511639/250000 : ℚ) vp000000000010111 := by
  apply branch_left_normalized (c:=vp0000000000101110) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-5511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-5511639/125000 : ℚ) by norm_num]
  exact coverp0000000000101110
private noncomputable def ep0000000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101111-E-0000.bin"
noncomputable def ep0000000000101111 : Blocks := ep0000000000101111_0
private theorem idp0000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010111.list =
    C ((2:ℤ)^135) * horner X vp0000000000101111.list + horner X ep0000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101111 : Branch 1 (-5511639/250000 : ℚ) vp000000000010111 := by
  apply branch_checked idp0000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-5636639/125000 : ℚ) by norm_num]
  exact coverp0000000000101111
theorem coverp000000000010111 : Covers (-5511639/250000 : ℚ) vp000000000010111 := join_branches bp0000000000101110 bp0000000000101111
private noncomputable def vp00000000001011011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011111-V-0000.bin"
noncomputable def vp00000000001011011111 : Blocks := vp00000000001011011111_0
theorem coverp00000000001011011111 : Covers (-11007653/15625 : ℚ) vp00000000001011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011110-V-0000.bin"
noncomputable def vp00000000001011011110 : Blocks := vp00000000001011011110_0
theorem coverp00000000001011011110 : Covers (-10992028/15625 : ℚ) vp00000000001011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101111-V-0000.bin"
noncomputable def vp0000000000101101111 : Blocks := vp0000000000101101111_0
private theorem bp00000000001011011110 : Branch 0 (-5496014/15625 : ℚ) vp0000000000101101111 := by
  apply branch_left_normalized (c:=vp00000000001011011110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5496014/15625 : ℚ) - ((0:ℤ):ℚ) = (-10992028/15625 : ℚ) by norm_num]
  exact coverp00000000001011011110
private noncomputable def ep00000000001011011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011111-E-0000.bin"
noncomputable def ep00000000001011011111 : Blocks := ep00000000001011011111_0
private theorem idp00000000001011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101101111.list =
    C ((2:ℤ)^22) * horner X vp00000000001011011111.list + horner X ep00000000001011011111.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011011111 : Branch 1 (-5496014/15625 : ℚ) vp0000000000101101111 := by
  apply branch_checked idp00000000001011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5496014/15625 : ℚ) - ((1:ℤ):ℚ) = (-11007653/15625 : ℚ) by norm_num]
  exact coverp00000000001011011111
theorem coverp0000000000101101111 : Covers (-5496014/15625 : ℚ) vp0000000000101101111 := join_branches bp00000000001011011110 bp00000000001011011111
private noncomputable def vp0000000000101101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101110-V-0000.bin"
noncomputable def vp0000000000101101110 : Blocks := vp0000000000101101110_0
theorem coverp0000000000101101110 : Covers (-5480389/15625 : ℚ) vp0000000000101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110111-V-0000.bin"
noncomputable def vp000000000010110111 : Blocks := vp000000000010110111_0
private theorem bp0000000000101101110 : Branch 0 (-5480389/31250 : ℚ) vp000000000010110111 := by
  apply branch_left_normalized (c:=vp0000000000101101110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5480389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5480389/15625 : ℚ) by norm_num]
  exact coverp0000000000101101110
private noncomputable def ep0000000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101111-E-0000.bin"
noncomputable def ep0000000000101101111 : Blocks := ep0000000000101101111_0
private theorem idp0000000000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110111.list =
    C ((2:ℤ)^32) * horner X vp0000000000101101111.list + horner X ep0000000000101101111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101101111 : Branch 1 (-5480389/31250 : ℚ) vp000000000010110111 := by
  apply branch_checked idp0000000000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5480389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5496014/15625 : ℚ) by norm_num]
  exact coverp0000000000101101111
theorem coverp000000000010110111 : Covers (-5480389/31250 : ℚ) vp000000000010110111 := join_branches bp0000000000101101110 bp0000000000101101111
private noncomputable def vp0000000000101101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101111-V-0000.bin"
noncomputable def vp0000000000101101101111 : Blocks := vp0000000000101101101111_0
theorem coverp0000000000101101101111 : Covers (-43827487/15625 : ℚ) vp0000000000101101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101101101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101110-V-0000.bin"
noncomputable def vp0000000000101101101110 : Blocks := vp0000000000101101101110_0
theorem coverp0000000000101101101110 : Covers (-43811862/15625 : ℚ) vp0000000000101101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110110111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110111-V-0000.bin"
noncomputable def vp000000000010110110111 : Blocks := vp000000000010110110111_0
private theorem bp0000000000101101101110 : Branch 0 (-21905931/15625 : ℚ) vp000000000010110110111 := by
  apply branch_left_normalized (c:=vp0000000000101101101110) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-21905931/15625 : ℚ) - ((0:ℤ):ℚ) = (-43811862/15625 : ℚ) by norm_num]
  exact coverp0000000000101101101110
private noncomputable def ep0000000000101101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101111-E-0000.bin"
noncomputable def ep0000000000101101101111 : Blocks := ep0000000000101101101111_0
private theorem idp0000000000101101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110110111.list =
    C ((2:ℤ)^14) * horner X vp0000000000101101101111.list + horner X ep0000000000101101101111.list := by
  exact edge_identity (B := (2:ℤ)^120) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101101101111 : Branch 1 (-21905931/15625 : ℚ) vp000000000010110110111 := by
  apply branch_checked idp0000000000101101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-21905931/15625 : ℚ) - ((1:ℤ):ℚ) = (-43827487/15625 : ℚ) by norm_num]
  exact coverp0000000000101101101111
theorem coverp000000000010110110111 : Covers (-21905931/15625 : ℚ) vp000000000010110110111 := join_branches bp0000000000101101101110 bp0000000000101101101111
private noncomputable def vp0000000000101101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101101-V-0000.bin"
noncomputable def vp0000000000101101101101 : Blocks := vp0000000000101101101101_0
theorem coverp0000000000101101101101 : Covers (-43796237/15625 : ℚ) vp0000000000101101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101101101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101100-V-0000.bin"
noncomputable def vp0000000000101101101100 : Blocks := vp0000000000101101101100_0
theorem coverp0000000000101101101100 : Covers (-43780612/15625 : ℚ) vp0000000000101101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110110110_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110110-V-0000.bin"
noncomputable def vp000000000010110110110 : Blocks := vp000000000010110110110_0
private theorem bp0000000000101101101100 : Branch 0 (-21890306/15625 : ℚ) vp000000000010110110110 := by
  apply branch_left_normalized (c:=vp0000000000101101101100) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-21890306/15625 : ℚ) - ((0:ℤ):ℚ) = (-43780612/15625 : ℚ) by norm_num]
  exact coverp0000000000101101101100
private noncomputable def ep0000000000101101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101101-E-0000.bin"
noncomputable def ep0000000000101101101101 : Blocks := ep0000000000101101101101_0
private theorem idp0000000000101101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110110110.list =
    C ((2:ℤ)^14) * horner X vp0000000000101101101101.list + horner X ep0000000000101101101101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101101101101 : Branch 1 (-21890306/15625 : ℚ) vp000000000010110110110 := by
  apply branch_checked idp0000000000101101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-21890306/15625 : ℚ) - ((1:ℤ):ℚ) = (-43796237/15625 : ℚ) by norm_num]
  exact coverp0000000000101101101101
theorem coverp000000000010110110110 : Covers (-21890306/15625 : ℚ) vp000000000010110110110 := join_branches bp0000000000101101101100 bp0000000000101101101101
private noncomputable def vp00000000001011011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011011-V-0000.bin"
noncomputable def vp00000000001011011011 : Blocks := vp00000000001011011011_0
private theorem bp000000000010110110110 : Branch 0 (-10945153/15625 : ℚ) vp00000000001011011011 := by
  apply branch_left_normalized (c:=vp000000000010110110110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-10945153/15625 : ℚ) - ((0:ℤ):ℚ) = (-21890306/15625 : ℚ) by norm_num]
  exact coverp000000000010110110110
private noncomputable def ep000000000010110110111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110111-E-0000.bin"
noncomputable def ep000000000010110110111 : Blocks := ep000000000010110110111_0
private theorem idp000000000010110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011011011.list =
    C ((2:ℤ)^17) * horner X vp000000000010110110111.list + horner X ep000000000010110110111.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110110111 : Branch 1 (-10945153/15625 : ℚ) vp00000000001011011011 := by
  apply branch_checked idp000000000010110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-10945153/15625 : ℚ) - ((1:ℤ):ℚ) = (-21905931/15625 : ℚ) by norm_num]
  exact coverp000000000010110110111
theorem coverp00000000001011011011 : Covers (-10945153/15625 : ℚ) vp00000000001011011011 := join_branches bp000000000010110110110 bp000000000010110110111
private noncomputable def vp000000000010110110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110101-V-0000.bin"
noncomputable def vp000000000010110110101 : Blocks := vp000000000010110110101_0
theorem coverp000000000010110110101 : Covers (-21874681/15625 : ℚ) vp000000000010110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110110100_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110100-V-0000.bin"
noncomputable def vp000000000010110110100 : Blocks := vp000000000010110110100_0
theorem coverp000000000010110110100 : Covers (-21859056/15625 : ℚ) vp000000000010110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011011010_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011010-V-0000.bin"
noncomputable def vp00000000001011011010 : Blocks := vp00000000001011011010_0
private theorem bp000000000010110110100 : Branch 0 (-10929528/15625 : ℚ) vp00000000001011011010 := by
  apply branch_left_normalized (c:=vp000000000010110110100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-10929528/15625 : ℚ) - ((0:ℤ):ℚ) = (-21859056/15625 : ℚ) by norm_num]
  exact coverp000000000010110110100
private noncomputable def ep000000000010110110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110101-E-0000.bin"
noncomputable def ep000000000010110110101 : Blocks := ep000000000010110110101_0
private theorem idp000000000010110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011011010.list =
    C ((2:ℤ)^17) * horner X vp000000000010110110101.list + horner X ep000000000010110110101.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110110101 : Branch 1 (-10929528/15625 : ℚ) vp00000000001011011010 := by
  apply branch_checked idp000000000010110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-10929528/15625 : ℚ) - ((1:ℤ):ℚ) = (-21874681/15625 : ℚ) by norm_num]
  exact coverp000000000010110110101
theorem coverp00000000001011011010 : Covers (-10929528/15625 : ℚ) vp00000000001011011010 := join_branches bp000000000010110110100 bp000000000010110110101
private noncomputable def vp0000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101-V-0000.bin"
noncomputable def vp0000000000101101101 : Blocks := vp0000000000101101101_0
private theorem bp00000000001011011010 : Branch 0 (-5464764/15625 : ℚ) vp0000000000101101101 := by
  apply branch_left_normalized (c:=vp00000000001011011010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5464764/15625 : ℚ) - ((0:ℤ):ℚ) = (-10929528/15625 : ℚ) by norm_num]
  exact coverp00000000001011011010
private noncomputable def ep00000000001011011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011011-E-0000.bin"
noncomputable def ep00000000001011011011 : Blocks := ep00000000001011011011_0
private theorem idp00000000001011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101101101.list =
    C ((2:ℤ)^21) * horner X vp00000000001011011011.list + horner X ep00000000001011011011.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011011011 : Branch 1 (-5464764/15625 : ℚ) vp0000000000101101101 := by
  apply branch_checked idp00000000001011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5464764/15625 : ℚ) - ((1:ℤ):ℚ) = (-10945153/15625 : ℚ) by norm_num]
  exact coverp00000000001011011011
theorem coverp0000000000101101101 : Covers (-5464764/15625 : ℚ) vp0000000000101101101 := join_branches bp00000000001011011010 bp00000000001011011011
private noncomputable def vp0000000000101101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101100-V-0000.bin"
noncomputable def vp0000000000101101100 : Blocks := vp0000000000101101100_0
theorem coverp0000000000101101100 : Covers (-5449139/15625 : ℚ) vp0000000000101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110110_0 : Blocks := edgeBlocks% "full/vectors/000000000010110110-V-0000.bin"
noncomputable def vp000000000010110110 : Blocks := vp000000000010110110_0
private theorem bp0000000000101101100 : Branch 0 (-5449139/31250 : ℚ) vp000000000010110110 := by
  apply branch_left_normalized (c:=vp0000000000101101100) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-5449139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5449139/15625 : ℚ) by norm_num]
  exact coverp0000000000101101100
private noncomputable def ep0000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101101-E-0000.bin"
noncomputable def ep0000000000101101101 : Blocks := ep0000000000101101101_0
private theorem idp0000000000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110110.list =
    C ((2:ℤ)^29) * horner X vp0000000000101101101.list + horner X ep0000000000101101101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101101101 : Branch 1 (-5449139/31250 : ℚ) vp000000000010110110 := by
  apply branch_checked idp0000000000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5449139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5464764/15625 : ℚ) by norm_num]
  exact coverp0000000000101101101
theorem coverp000000000010110110 : Covers (-5449139/31250 : ℚ) vp000000000010110110 := join_branches bp0000000000101101100 bp0000000000101101101
private noncomputable def vp00000000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011-V-0000.bin"
noncomputable def vp00000000001011011 : Blocks := vp00000000001011011_0
private theorem bp000000000010110110 : Branch 0 (-5449139/62500 : ℚ) vp00000000001011011 := by
  apply branch_left_normalized (c:=vp000000000010110110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-5449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5449139/31250 : ℚ) by norm_num]
  exact coverp000000000010110110
private noncomputable def ep000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110111-E-0000.bin"
noncomputable def ep000000000010110111 : Blocks := ep000000000010110111_0
private theorem idp000000000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011011.list =
    C ((2:ℤ)^43) * horner X vp000000000010110111.list + horner X ep000000000010110111.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110111 : Branch 1 (-5449139/62500 : ℚ) vp00000000001011011 := by
  apply branch_checked idp000000000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5480389/31250 : ℚ) by norm_num]
  exact coverp000000000010110111
theorem coverp00000000001011011 : Covers (-5449139/62500 : ℚ) vp00000000001011011 := join_branches bp000000000010110110 bp000000000010110111
private noncomputable def vp000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110101-V-0000.bin"
noncomputable def vp000000000010110101 : Blocks := vp000000000010110101_0
theorem coverp000000000010110101 : Covers (-5417889/31250 : ℚ) vp000000000010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110100_0 : Blocks := edgeBlocks% "full/vectors/000000000010110100-V-0000.bin"
noncomputable def vp000000000010110100 : Blocks := vp000000000010110100_0
theorem coverp000000000010110100 : Covers (-5386639/31250 : ℚ) vp000000000010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011010_0 : Blocks := edgeBlocks% "full/vectors/00000000001011010-V-0000.bin"
noncomputable def vp00000000001011010 : Blocks := vp00000000001011010_0
private theorem bp000000000010110100 : Branch 0 (-5386639/62500 : ℚ) vp00000000001011010 := by
  apply branch_left_normalized (c:=vp000000000010110100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-5386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5386639/31250 : ℚ) by norm_num]
  exact coverp000000000010110100
private noncomputable def ep000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110101-E-0000.bin"
noncomputable def ep000000000010110101 : Blocks := ep000000000010110101_0
private theorem idp000000000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011010.list =
    C ((2:ℤ)^52) * horner X vp000000000010110101.list + horner X ep000000000010110101.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110101 : Branch 1 (-5386639/62500 : ℚ) vp00000000001011010 := by
  apply branch_checked idp000000000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5417889/31250 : ℚ) by norm_num]
  exact coverp000000000010110101
theorem coverp00000000001011010 : Covers (-5386639/62500 : ℚ) vp00000000001011010 := join_branches bp000000000010110100 bp000000000010110101
private noncomputable def vp0000000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101-V-0000.bin"
noncomputable def vp0000000000101101 : Blocks := vp0000000000101101_0
private theorem bp00000000001011010 : Branch 0 (-5386639/125000 : ℚ) vp0000000000101101 := by
  apply branch_left_normalized (c:=vp00000000001011010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-5386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5386639/62500 : ℚ) by norm_num]
  exact coverp00000000001011010
private noncomputable def ep00000000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011011-E-0000.bin"
noncomputable def ep00000000001011011 : Blocks := ep00000000001011011_0
private theorem idp00000000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101101.list =
    C ((2:ℤ)^80) * horner X vp00000000001011011.list + horner X ep00000000001011011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011011 : Branch 1 (-5386639/125000 : ℚ) vp0000000000101101 := by
  apply branch_checked idp00000000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5449139/62500 : ℚ) by norm_num]
  exact coverp00000000001011011
theorem coverp0000000000101101 : Covers (-5386639/125000 : ℚ) vp0000000000101101 := join_branches bp00000000001011010 bp00000000001011011
private noncomputable def vp0000000000101100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100111111-V-0000.bin"
noncomputable def vp0000000000101100111111 : Blocks := vp0000000000101100111111_0
theorem coverp0000000000101100111111 : Covers (-43077487/15625 : ℚ) vp0000000000101100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101100111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100111110-V-0000.bin"
noncomputable def vp0000000000101100111110 : Blocks := vp0000000000101100111110_0
theorem coverp0000000000101100111110 : Covers (-43061862/15625 : ℚ) vp0000000000101100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110011111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110011111-V-0000.bin"
noncomputable def vp000000000010110011111 : Blocks := vp000000000010110011111_0
private theorem bp0000000000101100111110 : Branch 0 (-21530931/15625 : ℚ) vp000000000010110011111 := by
  apply branch_left_normalized (c:=vp0000000000101100111110) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-21530931/15625 : ℚ) - ((0:ℤ):ℚ) = (-43061862/15625 : ℚ) by norm_num]
  exact coverp0000000000101100111110
private noncomputable def ep0000000000101100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100111111-E-0000.bin"
noncomputable def ep0000000000101100111111 : Blocks := ep0000000000101100111111_0
private theorem idp0000000000101100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110011111.list =
    C ((2:ℤ)^14) * horner X vp0000000000101100111111.list + horner X ep0000000000101100111111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101100111111 : Branch 1 (-21530931/15625 : ℚ) vp000000000010110011111 := by
  apply branch_checked idp0000000000101100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-21530931/15625 : ℚ) - ((1:ℤ):ℚ) = (-43077487/15625 : ℚ) by norm_num]
  exact coverp0000000000101100111111
theorem coverp000000000010110011111 : Covers (-21530931/15625 : ℚ) vp000000000010110011111 := join_branches bp0000000000101100111110 bp0000000000101100111111
private noncomputable def vp000000000010110011110_0 : Blocks := edgeBlocks% "full/vectors/000000000010110011110-V-0000.bin"
noncomputable def vp000000000010110011110 : Blocks := vp000000000010110011110_0
theorem coverp000000000010110011110 : Covers (-21515306/15625 : ℚ) vp000000000010110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001111-V-0000.bin"
noncomputable def vp00000000001011001111 : Blocks := vp00000000001011001111_0
private theorem bp000000000010110011110 : Branch 0 (-10757653/15625 : ℚ) vp00000000001011001111 := by
  apply branch_left_normalized (c:=vp000000000010110011110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-10757653/15625 : ℚ) - ((0:ℤ):ℚ) = (-21515306/15625 : ℚ) by norm_num]
  exact coverp000000000010110011110
private noncomputable def ep000000000010110011111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110011111-E-0000.bin"
noncomputable def ep000000000010110011111 : Blocks := ep000000000010110011111_0
private theorem idp000000000010110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011001111.list =
    C ((2:ℤ)^17) * horner X vp000000000010110011111.list + horner X ep000000000010110011111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110011111 : Branch 1 (-10757653/15625 : ℚ) vp00000000001011001111 := by
  apply branch_checked idp000000000010110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-10757653/15625 : ℚ) - ((1:ℤ):ℚ) = (-21530931/15625 : ℚ) by norm_num]
  exact coverp000000000010110011111
theorem coverp00000000001011001111 : Covers (-10757653/15625 : ℚ) vp00000000001011001111 := join_branches bp000000000010110011110 bp000000000010110011111
private noncomputable def vp00000000001011001110_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001110-V-0000.bin"
noncomputable def vp00000000001011001110 : Blocks := vp00000000001011001110_0
theorem coverp00000000001011001110 : Covers (-10742028/15625 : ℚ) vp00000000001011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100111-V-0000.bin"
noncomputable def vp0000000000101100111 : Blocks := vp0000000000101100111_0
private theorem bp00000000001011001110 : Branch 0 (-5371014/15625 : ℚ) vp0000000000101100111 := by
  apply branch_left_normalized (c:=vp00000000001011001110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5371014/15625 : ℚ) - ((0:ℤ):ℚ) = (-10742028/15625 : ℚ) by norm_num]
  exact coverp00000000001011001110
private noncomputable def ep00000000001011001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001111-E-0000.bin"
noncomputable def ep00000000001011001111 : Blocks := ep00000000001011001111_0
private theorem idp00000000001011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101100111.list =
    C ((2:ℤ)^22) * horner X vp00000000001011001111.list + horner X ep00000000001011001111.list := by
  exact edge_identity (B := (2:ℤ)^134) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011001111 : Branch 1 (-5371014/15625 : ℚ) vp0000000000101100111 := by
  apply branch_checked idp00000000001011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5371014/15625 : ℚ) - ((1:ℤ):ℚ) = (-10757653/15625 : ℚ) by norm_num]
  exact coverp00000000001011001111
theorem coverp0000000000101100111 : Covers (-5371014/15625 : ℚ) vp0000000000101100111 := join_branches bp00000000001011001110 bp00000000001011001111
private noncomputable def vp0000000000101100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100110-V-0000.bin"
noncomputable def vp0000000000101100110 : Blocks := vp0000000000101100110_0
theorem coverp0000000000101100110 : Covers (-5355389/15625 : ℚ) vp0000000000101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000000010110011-V-0000.bin"
noncomputable def vp000000000010110011 : Blocks := vp000000000010110011_0
private theorem bp0000000000101100110 : Branch 0 (-5355389/31250 : ℚ) vp000000000010110011 := by
  apply branch_left_normalized (c:=vp0000000000101100110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5355389/15625 : ℚ) by norm_num]
  exact coverp0000000000101100110
private noncomputable def ep0000000000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100111-E-0000.bin"
noncomputable def ep0000000000101100111 : Blocks := ep0000000000101100111_0
private theorem idp0000000000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110011.list =
    C ((2:ℤ)^31) * horner X vp0000000000101100111.list + horner X ep0000000000101100111.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101100111 : Branch 1 (-5355389/31250 : ℚ) vp000000000010110011 := by
  apply branch_checked idp0000000000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5371014/15625 : ℚ) by norm_num]
  exact coverp0000000000101100111
theorem coverp000000000010110011 : Covers (-5355389/31250 : ℚ) vp000000000010110011 := join_branches bp0000000000101100110 bp0000000000101100111
private noncomputable def vp00000000001011001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001011-V-0000.bin"
noncomputable def vp00000000001011001011 : Blocks := vp00000000001011001011_0
theorem coverp00000000001011001011 : Covers (-10695153/15625 : ℚ) vp00000000001011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110010101-V-0000.bin"
noncomputable def vp000000000010110010101 : Blocks := vp000000000010110010101_0
theorem coverp000000000010110010101 : Covers (-21374681/15625 : ℚ) vp000000000010110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110010100_0 : Blocks := edgeBlocks% "full/vectors/000000000010110010100-V-0000.bin"
noncomputable def vp000000000010110010100 : Blocks := vp000000000010110010100_0
theorem coverp000000000010110010100 : Covers (-21359056/15625 : ℚ) vp000000000010110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011001010_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001010-V-0000.bin"
noncomputable def vp00000000001011001010 : Blocks := vp00000000001011001010_0
private theorem bp000000000010110010100 : Branch 0 (-10679528/15625 : ℚ) vp00000000001011001010 := by
  apply branch_left_normalized (c:=vp000000000010110010100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-10679528/15625 : ℚ) - ((0:ℤ):ℚ) = (-21359056/15625 : ℚ) by norm_num]
  exact coverp000000000010110010100
private noncomputable def ep000000000010110010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010110010101-E-0000.bin"
noncomputable def ep000000000010110010101 : Blocks := ep000000000010110010101_0
private theorem idp000000000010110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011001010.list =
    C ((2:ℤ)^17) * horner X vp000000000010110010101.list + horner X ep000000000010110010101.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110010101 : Branch 1 (-10679528/15625 : ℚ) vp00000000001011001010 := by
  apply branch_checked idp000000000010110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-10679528/15625 : ℚ) - ((1:ℤ):ℚ) = (-21374681/15625 : ℚ) by norm_num]
  exact coverp000000000010110010101
theorem coverp00000000001011001010 : Covers (-10679528/15625 : ℚ) vp00000000001011001010 := join_branches bp000000000010110010100 bp000000000010110010101
private noncomputable def vp0000000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100101-V-0000.bin"
noncomputable def vp0000000000101100101 : Blocks := vp0000000000101100101_0
private theorem bp00000000001011001010 : Branch 0 (-5339764/15625 : ℚ) vp0000000000101100101 := by
  apply branch_left_normalized (c:=vp00000000001011001010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5339764/15625 : ℚ) - ((0:ℤ):ℚ) = (-10679528/15625 : ℚ) by norm_num]
  exact coverp00000000001011001010
private noncomputable def ep00000000001011001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001011-E-0000.bin"
noncomputable def ep00000000001011001011 : Blocks := ep00000000001011001011_0
private theorem idp00000000001011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101100101.list =
    C ((2:ℤ)^22) * horner X vp00000000001011001011.list + horner X ep00000000001011001011.list := by
  exact edge_identity (B := (2:ℤ)^134) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011001011 : Branch 1 (-5339764/15625 : ℚ) vp0000000000101100101 := by
  apply branch_checked idp00000000001011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5339764/15625 : ℚ) - ((1:ℤ):ℚ) = (-10695153/15625 : ℚ) by norm_num]
  exact coverp00000000001011001011
theorem coverp0000000000101100101 : Covers (-5339764/15625 : ℚ) vp0000000000101100101 := join_branches bp00000000001011001010 bp00000000001011001011
private noncomputable def vp00000000001011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001001-V-0000.bin"
noncomputable def vp00000000001011001001 : Blocks := vp00000000001011001001_0
theorem coverp00000000001011001001 : Covers (-10663903/15625 : ℚ) vp00000000001011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011001000_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001000-V-0000.bin"
noncomputable def vp00000000001011001000 : Blocks := vp00000000001011001000_0
theorem coverp00000000001011001000 : Covers (-10648278/15625 : ℚ) vp00000000001011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100100-V-0000.bin"
noncomputable def vp0000000000101100100 : Blocks := vp0000000000101100100_0
private theorem bp00000000001011001000 : Branch 0 (-5324139/15625 : ℚ) vp0000000000101100100 := by
  apply branch_left_normalized (c:=vp00000000001011001000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5324139/15625 : ℚ) - ((0:ℤ):ℚ) = (-10648278/15625 : ℚ) by norm_num]
  exact coverp00000000001011001000
private noncomputable def ep00000000001011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001001-E-0000.bin"
noncomputable def ep00000000001011001001 : Blocks := ep00000000001011001001_0
private theorem idp00000000001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101100100.list =
    C ((2:ℤ)^21) * horner X vp00000000001011001001.list + horner X ep00000000001011001001.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011001001 : Branch 1 (-5324139/15625 : ℚ) vp0000000000101100100 := by
  apply branch_checked idp00000000001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5324139/15625 : ℚ) - ((1:ℤ):ℚ) = (-10663903/15625 : ℚ) by norm_num]
  exact coverp00000000001011001001
theorem coverp0000000000101100100 : Covers (-5324139/15625 : ℚ) vp0000000000101100100 := join_branches bp00000000001011001000 bp00000000001011001001
private noncomputable def vp000000000010110010_0 : Blocks := edgeBlocks% "full/vectors/000000000010110010-V-0000.bin"
noncomputable def vp000000000010110010 : Blocks := vp000000000010110010_0
private theorem bp0000000000101100100 : Branch 0 (-5324139/31250 : ℚ) vp000000000010110010 := by
  apply branch_left_normalized (c:=vp0000000000101100100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-5324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5324139/15625 : ℚ) by norm_num]
  exact coverp0000000000101100100
private noncomputable def ep0000000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100101-E-0000.bin"
noncomputable def ep0000000000101100101 : Blocks := ep0000000000101100101_0
private theorem idp0000000000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110010.list =
    C ((2:ℤ)^30) * horner X vp0000000000101100101.list + horner X ep0000000000101100101.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101100101 : Branch 1 (-5324139/31250 : ℚ) vp000000000010110010 := by
  apply branch_checked idp0000000000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5339764/15625 : ℚ) by norm_num]
  exact coverp0000000000101100101
theorem coverp000000000010110010 : Covers (-5324139/31250 : ℚ) vp000000000010110010 := join_branches bp0000000000101100100 bp0000000000101100101
private noncomputable def vp00000000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001-V-0000.bin"
noncomputable def vp00000000001011001 : Blocks := vp00000000001011001_0
private theorem bp000000000010110010 : Branch 0 (-5324139/62500 : ℚ) vp00000000001011001 := by
  apply branch_left_normalized (c:=vp000000000010110010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-5324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5324139/31250 : ℚ) by norm_num]
  exact coverp000000000010110010
private noncomputable def ep000000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000000010110011-E-0000.bin"
noncomputable def ep000000000010110011 : Blocks := ep000000000010110011_0
private theorem idp000000000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011001.list =
    C ((2:ℤ)^45) * horner X vp000000000010110011.list + horner X ep000000000010110011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110011 : Branch 1 (-5324139/62500 : ℚ) vp00000000001011001 := by
  apply branch_checked idp000000000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5355389/31250 : ℚ) by norm_num]
  exact coverp000000000010110011
theorem coverp00000000001011001 : Covers (-5324139/62500 : ℚ) vp00000000001011001 := join_branches bp000000000010110010 bp000000000010110011
private noncomputable def vp000000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000000010110001-V-0000.bin"
noncomputable def vp000000000010110001 : Blocks := vp000000000010110001_0
theorem coverp000000000010110001 : Covers (-5292889/31250 : ℚ) vp000000000010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110000111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110000111-V-0000.bin"
noncomputable def vp000000000010110000111 : Blocks := vp000000000010110000111_0
theorem coverp000000000010110000111 : Covers (-21155931/15625 : ℚ) vp000000000010110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110000110_0 : Blocks := edgeBlocks% "full/vectors/000000000010110000110-V-0000.bin"
noncomputable def vp000000000010110000110 : Blocks := vp000000000010110000110_0
theorem coverp000000000010110000110 : Covers (-21140306/15625 : ℚ) vp000000000010110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011000011-V-0000.bin"
noncomputable def vp00000000001011000011 : Blocks := vp00000000001011000011_0
private theorem bp000000000010110000110 : Branch 0 (-10570153/15625 : ℚ) vp00000000001011000011 := by
  apply branch_left_normalized (c:=vp000000000010110000110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-10570153/15625 : ℚ) - ((0:ℤ):ℚ) = (-21140306/15625 : ℚ) by norm_num]
  exact coverp000000000010110000110
private noncomputable def ep000000000010110000111_0 : Blocks := edgeBlocks% "full/vectors/000000000010110000111-E-0000.bin"
noncomputable def ep000000000010110000111 : Blocks := ep000000000010110000111_0
private theorem idp000000000010110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011000011.list =
    C ((2:ℤ)^17) * horner X vp000000000010110000111.list + horner X ep000000000010110000111.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110000111 : Branch 1 (-10570153/15625 : ℚ) vp00000000001011000011 := by
  apply branch_checked idp000000000010110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-10570153/15625 : ℚ) - ((1:ℤ):ℚ) = (-21155931/15625 : ℚ) by norm_num]
  exact coverp000000000010110000111
theorem coverp00000000001011000011 : Covers (-10570153/15625 : ℚ) vp00000000001011000011 := join_branches bp000000000010110000110 bp000000000010110000111
private noncomputable def vp00000000001011000010_0 : Blocks := edgeBlocks% "full/vectors/00000000001011000010-V-0000.bin"
noncomputable def vp00000000001011000010 : Blocks := vp00000000001011000010_0
theorem coverp00000000001011000010 : Covers (-10554528/15625 : ℚ) vp00000000001011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100001-V-0000.bin"
noncomputable def vp0000000000101100001 : Blocks := vp0000000000101100001_0
private theorem bp00000000001011000010 : Branch 0 (-5277264/15625 : ℚ) vp0000000000101100001 := by
  apply branch_left_normalized (c:=vp00000000001011000010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5277264/15625 : ℚ) - ((0:ℤ):ℚ) = (-10554528/15625 : ℚ) by norm_num]
  exact coverp00000000001011000010
private noncomputable def ep00000000001011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011000011-E-0000.bin"
noncomputable def ep00000000001011000011 : Blocks := ep00000000001011000011_0
private theorem idp00000000001011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101100001.list =
    C ((2:ℤ)^22) * horner X vp00000000001011000011.list + horner X ep00000000001011000011.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011000011 : Branch 1 (-5277264/15625 : ℚ) vp0000000000101100001 := by
  apply branch_checked idp00000000001011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5277264/15625 : ℚ) - ((1:ℤ):ℚ) = (-10570153/15625 : ℚ) by norm_num]
  exact coverp00000000001011000011
theorem coverp0000000000101100001 : Covers (-5277264/15625 : ℚ) vp0000000000101100001 := join_branches bp00000000001011000010 bp00000000001011000011
private noncomputable def vp0000000000101100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100000-V-0000.bin"
noncomputable def vp0000000000101100000 : Blocks := vp0000000000101100000_0
theorem coverp0000000000101100000 : Covers (-5261639/15625 : ℚ) vp0000000000101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010110000_0 : Blocks := edgeBlocks% "full/vectors/000000000010110000-V-0000.bin"
noncomputable def vp000000000010110000 : Blocks := vp000000000010110000_0
private theorem bp0000000000101100000 : Branch 0 (-5261639/31250 : ℚ) vp000000000010110000 := by
  apply branch_left_normalized (c:=vp0000000000101100000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5261639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5261639/15625 : ℚ) by norm_num]
  exact coverp0000000000101100000
private noncomputable def ep0000000000101100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100001-E-0000.bin"
noncomputable def ep0000000000101100001 : Blocks := ep0000000000101100001_0
private theorem idp0000000000101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110000.list =
    C ((2:ℤ)^31) * horner X vp0000000000101100001.list + horner X ep0000000000101100001.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101100001 : Branch 1 (-5261639/31250 : ℚ) vp000000000010110000 := by
  apply branch_checked idp0000000000101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5261639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5277264/15625 : ℚ) by norm_num]
  exact coverp0000000000101100001
theorem coverp000000000010110000 : Covers (-5261639/31250 : ℚ) vp000000000010110000 := join_branches bp0000000000101100000 bp0000000000101100001
private noncomputable def vp00000000001011000_0 : Blocks := edgeBlocks% "full/vectors/00000000001011000-V-0000.bin"
noncomputable def vp00000000001011000 : Blocks := vp00000000001011000_0
private theorem bp000000000010110000 : Branch 0 (-5261639/62500 : ℚ) vp00000000001011000 := by
  apply branch_left_normalized (c:=vp000000000010110000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-5261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5261639/31250 : ℚ) by norm_num]
  exact coverp000000000010110000
private noncomputable def ep000000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000000010110001-E-0000.bin"
noncomputable def ep000000000010110001 : Blocks := ep000000000010110001_0
private theorem idp000000000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011000.list =
    C ((2:ℤ)^47) * horner X vp000000000010110001.list + horner X ep000000000010110001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010110001 : Branch 1 (-5261639/62500 : ℚ) vp00000000001011000 := by
  apply branch_checked idp000000000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5292889/31250 : ℚ) by norm_num]
  exact coverp000000000010110001
theorem coverp00000000001011000 : Covers (-5261639/62500 : ℚ) vp00000000001011000 := join_branches bp000000000010110000 bp000000000010110001
private noncomputable def vp0000000000101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101100-V-0000.bin"
noncomputable def vp0000000000101100 : Blocks := vp0000000000101100_0
private theorem bp00000000001011000 : Branch 0 (-5261639/125000 : ℚ) vp0000000000101100 := by
  apply branch_left_normalized (c:=vp00000000001011000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-5261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5261639/62500 : ℚ) by norm_num]
  exact coverp00000000001011000
private noncomputable def ep00000000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001011001-E-0000.bin"
noncomputable def ep00000000001011001 : Blocks := ep00000000001011001_0
private theorem idp00000000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101100.list =
    C ((2:ℤ)^76) * horner X vp00000000001011001.list + horner X ep00000000001011001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011001 : Branch 1 (-5261639/125000 : ℚ) vp0000000000101100 := by
  apply branch_checked idp00000000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5324139/62500 : ℚ) by norm_num]
  exact coverp00000000001011001
theorem coverp0000000000101100 : Covers (-5261639/125000 : ℚ) vp0000000000101100 := join_branches bp00000000001011000 bp00000000001011001
private noncomputable def vp000000000010110_0 : Blocks := edgeBlocks% "full/vectors/000000000010110-V-0000.bin"
noncomputable def vp000000000010110 : Blocks := vp000000000010110_0
private theorem bp0000000000101100 : Branch 0 (-5261639/250000 : ℚ) vp000000000010110 := by
  apply branch_left_normalized (c:=vp0000000000101100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-5261639/125000 : ℚ) by norm_num]
  exact coverp0000000000101100
private noncomputable def ep0000000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101101-E-0000.bin"
noncomputable def ep0000000000101101 : Blocks := ep0000000000101101_0
private theorem idp0000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010110.list =
    C ((2:ℤ)^128) * horner X vp0000000000101101.list + horner X ep0000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101101 : Branch 1 (-5261639/250000 : ℚ) vp000000000010110 := by
  apply branch_checked idp0000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-5386639/125000 : ℚ) by norm_num]
  exact coverp0000000000101101
theorem coverp000000000010110 : Covers (-5261639/250000 : ℚ) vp000000000010110 := join_branches bp0000000000101100 bp0000000000101101
private noncomputable def vp00000000001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011-V-0000.bin"
private noncomputable def vp00000000001011_1 : Blocks := edgeBlocks% "full/vectors/00000000001011-V-0001.bin"
noncomputable def vp00000000001011 : Blocks := (Blocks.join vp00000000001011_0 vp00000000001011_1)
private theorem bp000000000010110 : Branch 0 (-5261639/500000 : ℚ) vp00000000001011 := by
  apply branch_left_normalized (c:=vp000000000010110) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-5261639/250000 : ℚ) by norm_num]
  exact coverp000000000010110
private noncomputable def ep000000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000000010111-E-0000.bin"
private noncomputable def ep000000000010111_1 : Blocks := edgeBlocks% "full/vectors/000000000010111-E-0001.bin"
noncomputable def ep000000000010111 : Blocks := (Blocks.join ep000000000010111_0 ep000000000010111_1)
private theorem idp000000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001011.list =
    C ((2:ℤ)^235) * horner X vp000000000010111.list + horner X ep000000000010111.list := by
  exact edge_identity (B := (2:ℤ)^447) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010111 : Branch 1 (-5261639/500000 : ℚ) vp00000000001011 := by
  apply branch_checked idp000000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-5511639/250000 : ℚ) by norm_num]
  exact coverp000000000010111
theorem coverp00000000001011 : Covers (-5261639/500000 : ℚ) vp00000000001011 := join_branches bp000000000010110 bp000000000010111
end NextProof.EdgeFull

