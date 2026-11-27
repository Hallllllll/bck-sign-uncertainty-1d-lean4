import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111111-V-0000.bin"
noncomputable def vp000000000000001111111 : Blocks := vp000000000000001111111_0
theorem coverp000000000000001111111 : Covers (-1030931/15625 : ℚ) vp000000000000001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011111101-V-0000.bin"
noncomputable def vp0000000000000011111101 : Blocks := vp0000000000000011111101_0
theorem coverp0000000000000011111101 : Covers (-2046237/15625 : ℚ) vp0000000000000011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011111100-V-0000.bin"
noncomputable def vp0000000000000011111100 : Blocks := vp0000000000000011111100_0
theorem coverp0000000000000011111100 : Covers (-2030612/15625 : ℚ) vp0000000000000011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001111110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111110-V-0000.bin"
noncomputable def vp000000000000001111110 : Blocks := vp000000000000001111110_0
private theorem bp0000000000000011111100 : Branch 0 (-1015306/15625 : ℚ) vp000000000000001111110 := by
  apply branch_left_normalized (c:=vp0000000000000011111100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1015306/15625 : ℚ) - ((0:ℤ):ℚ) = (-2030612/15625 : ℚ) by norm_num]
  exact coverp0000000000000011111100
private noncomputable def ep0000000000000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011111101-E-0000.bin"
noncomputable def ep0000000000000011111101 : Blocks := ep0000000000000011111101_0
private theorem idp0000000000000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001111110.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011111101.list + horner X ep0000000000000011111101.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011111101 : Branch 1 (-1015306/15625 : ℚ) vp000000000000001111110 := by
  apply branch_checked idp0000000000000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1015306/15625 : ℚ) - ((1:ℤ):ℚ) = (-2046237/15625 : ℚ) by norm_num]
  exact coverp0000000000000011111101
theorem coverp000000000000001111110 : Covers (-1015306/15625 : ℚ) vp000000000000001111110 := join_branches bp0000000000000011111100 bp0000000000000011111101
private noncomputable def vp00000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111111-V-0000.bin"
noncomputable def vp00000000000000111111 : Blocks := vp00000000000000111111_0
private theorem bp000000000000001111110 : Branch 0 (-507653/15625 : ℚ) vp00000000000000111111 := by
  apply branch_left_normalized (c:=vp000000000000001111110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-507653/15625 : ℚ) - ((0:ℤ):ℚ) = (-1015306/15625 : ℚ) by norm_num]
  exact coverp000000000000001111110
private noncomputable def ep000000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111111-E-0000.bin"
noncomputable def ep000000000000001111111 : Blocks := ep000000000000001111111_0
private theorem idp000000000000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111111.list =
    C ((2:ℤ)^28) * horner X vp000000000000001111111.list + horner X ep000000000000001111111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001111111 : Branch 1 (-507653/15625 : ℚ) vp00000000000000111111 := by
  apply branch_checked idp000000000000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-507653/15625 : ℚ) - ((1:ℤ):ℚ) = (-1030931/15625 : ℚ) by norm_num]
  exact coverp000000000000001111111
theorem coverp00000000000000111111 : Covers (-507653/15625 : ℚ) vp00000000000000111111 := join_branches bp000000000000001111110 bp000000000000001111111
private noncomputable def vp000000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111101-V-0000.bin"
noncomputable def vp000000000000001111101 : Blocks := vp000000000000001111101_0
theorem coverp000000000000001111101 : Covers (-999681/15625 : ℚ) vp000000000000001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001111100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111100-V-0000.bin"
noncomputable def vp000000000000001111100 : Blocks := vp000000000000001111100_0
theorem coverp000000000000001111100 : Covers (-984056/15625 : ℚ) vp000000000000001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000111110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111110-V-0000.bin"
noncomputable def vp00000000000000111110 : Blocks := vp00000000000000111110_0
private theorem bp000000000000001111100 : Branch 0 (-492028/15625 : ℚ) vp00000000000000111110 := by
  apply branch_left_normalized (c:=vp000000000000001111100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-492028/15625 : ℚ) - ((0:ℤ):ℚ) = (-984056/15625 : ℚ) by norm_num]
  exact coverp000000000000001111100
private noncomputable def ep000000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111101-E-0000.bin"
noncomputable def ep000000000000001111101 : Blocks := ep000000000000001111101_0
private theorem idp000000000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111110.list =
    C ((2:ℤ)^29) * horner X vp000000000000001111101.list + horner X ep000000000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001111101 : Branch 1 (-492028/15625 : ℚ) vp00000000000000111110 := by
  apply branch_checked idp000000000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-492028/15625 : ℚ) - ((1:ℤ):ℚ) = (-999681/15625 : ℚ) by norm_num]
  exact coverp000000000000001111101
theorem coverp00000000000000111110 : Covers (-492028/15625 : ℚ) vp00000000000000111110 := join_branches bp000000000000001111100 bp000000000000001111101
private noncomputable def vp0000000000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011111-V-0000.bin"
noncomputable def vp0000000000000011111 : Blocks := vp0000000000000011111_0
private theorem bp00000000000000111110 : Branch 0 (-246014/15625 : ℚ) vp0000000000000011111 := by
  apply branch_left_normalized (c:=vp00000000000000111110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-246014/15625 : ℚ) - ((0:ℤ):ℚ) = (-492028/15625 : ℚ) by norm_num]
  exact coverp00000000000000111110
private noncomputable def ep00000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111111-E-0000.bin"
noncomputable def ep00000000000000111111 : Blocks := ep00000000000000111111_0
private theorem idp00000000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011111.list =
    C ((2:ℤ)^42) * horner X vp00000000000000111111.list + horner X ep00000000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000111111 : Branch 1 (-246014/15625 : ℚ) vp0000000000000011111 := by
  apply branch_checked idp00000000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-246014/15625 : ℚ) - ((1:ℤ):ℚ) = (-507653/15625 : ℚ) by norm_num]
  exact coverp00000000000000111111
theorem coverp0000000000000011111 : Covers (-246014/15625 : ℚ) vp0000000000000011111 := join_branches bp00000000000000111110 bp00000000000000111111
private noncomputable def vp0000000000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110111-V-0000.bin"
noncomputable def vp0000000000000011110111 : Blocks := vp0000000000000011110111_0
theorem coverp0000000000000011110111 : Covers (-1952487/15625 : ℚ) vp0000000000000011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110110-V-0000.bin"
noncomputable def vp0000000000000011110110 : Blocks := vp0000000000000011110110_0
theorem coverp0000000000000011110110 : Covers (-1936862/15625 : ℚ) vp0000000000000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111011-V-0000.bin"
noncomputable def vp000000000000001111011 : Blocks := vp000000000000001111011_0
private theorem bp0000000000000011110110 : Branch 0 (-968431/15625 : ℚ) vp000000000000001111011 := by
  apply branch_left_normalized (c:=vp0000000000000011110110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-968431/15625 : ℚ) - ((0:ℤ):ℚ) = (-1936862/15625 : ℚ) by norm_num]
  exact coverp0000000000000011110110
private noncomputable def ep0000000000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110111-E-0000.bin"
noncomputable def ep0000000000000011110111 : Blocks := ep0000000000000011110111_0
private theorem idp0000000000000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001111011.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011110111.list + horner X ep0000000000000011110111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011110111 : Branch 1 (-968431/15625 : ℚ) vp000000000000001111011 := by
  apply branch_checked idp0000000000000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-968431/15625 : ℚ) - ((1:ℤ):ℚ) = (-1952487/15625 : ℚ) by norm_num]
  exact coverp0000000000000011110111
theorem coverp000000000000001111011 : Covers (-968431/15625 : ℚ) vp000000000000001111011 := join_branches bp0000000000000011110110 bp0000000000000011110111
private noncomputable def vp0000000000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110101-V-0000.bin"
noncomputable def vp0000000000000011110101 : Blocks := vp0000000000000011110101_0
theorem coverp0000000000000011110101 : Covers (-1921237/15625 : ℚ) vp0000000000000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110100-V-0000.bin"
noncomputable def vp0000000000000011110100 : Blocks := vp0000000000000011110100_0
theorem coverp0000000000000011110100 : Covers (-1905612/15625 : ℚ) vp0000000000000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001111010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111010-V-0000.bin"
noncomputable def vp000000000000001111010 : Blocks := vp000000000000001111010_0
private theorem bp0000000000000011110100 : Branch 0 (-952806/15625 : ℚ) vp000000000000001111010 := by
  apply branch_left_normalized (c:=vp0000000000000011110100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-952806/15625 : ℚ) - ((0:ℤ):ℚ) = (-1905612/15625 : ℚ) by norm_num]
  exact coverp0000000000000011110100
private noncomputable def ep0000000000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110101-E-0000.bin"
noncomputable def ep0000000000000011110101 : Blocks := ep0000000000000011110101_0
private theorem idp0000000000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001111010.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011110101.list + horner X ep0000000000000011110101.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011110101 : Branch 1 (-952806/15625 : ℚ) vp000000000000001111010 := by
  apply branch_checked idp0000000000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-952806/15625 : ℚ) - ((1:ℤ):ℚ) = (-1921237/15625 : ℚ) by norm_num]
  exact coverp0000000000000011110101
theorem coverp000000000000001111010 : Covers (-952806/15625 : ℚ) vp000000000000001111010 := join_branches bp0000000000000011110100 bp0000000000000011110101
private noncomputable def vp00000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111101-V-0000.bin"
noncomputable def vp00000000000000111101 : Blocks := vp00000000000000111101_0
private theorem bp000000000000001111010 : Branch 0 (-476403/15625 : ℚ) vp00000000000000111101 := by
  apply branch_left_normalized (c:=vp000000000000001111010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-476403/15625 : ℚ) - ((0:ℤ):ℚ) = (-952806/15625 : ℚ) by norm_num]
  exact coverp000000000000001111010
private noncomputable def ep000000000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111011-E-0000.bin"
noncomputable def ep000000000000001111011 : Blocks := ep000000000000001111011_0
private theorem idp000000000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111101.list =
    C ((2:ℤ)^29) * horner X vp000000000000001111011.list + horner X ep000000000000001111011.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001111011 : Branch 1 (-476403/15625 : ℚ) vp00000000000000111101 := by
  apply branch_checked idp000000000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-476403/15625 : ℚ) - ((1:ℤ):ℚ) = (-968431/15625 : ℚ) by norm_num]
  exact coverp000000000000001111011
theorem coverp00000000000000111101 : Covers (-476403/15625 : ℚ) vp00000000000000111101 := join_branches bp000000000000001111010 bp000000000000001111011
private noncomputable def vp000000000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111001-V-0000.bin"
noncomputable def vp000000000000001111001 : Blocks := vp000000000000001111001_0
theorem coverp000000000000001111001 : Covers (-937181/15625 : ℚ) vp000000000000001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001111000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111000-V-0000.bin"
noncomputable def vp000000000000001111000 : Blocks := vp000000000000001111000_0
theorem coverp000000000000001111000 : Covers (-921556/15625 : ℚ) vp000000000000001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000111100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111100-V-0000.bin"
noncomputable def vp00000000000000111100 : Blocks := vp00000000000000111100_0
private theorem bp000000000000001111000 : Branch 0 (-460778/15625 : ℚ) vp00000000000000111100 := by
  apply branch_left_normalized (c:=vp000000000000001111000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-460778/15625 : ℚ) - ((0:ℤ):ℚ) = (-921556/15625 : ℚ) by norm_num]
  exact coverp000000000000001111000
private noncomputable def ep000000000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111001-E-0000.bin"
noncomputable def ep000000000000001111001 : Blocks := ep000000000000001111001_0
private theorem idp000000000000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111100.list =
    C ((2:ℤ)^30) * horner X vp000000000000001111001.list + horner X ep000000000000001111001.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001111001 : Branch 1 (-460778/15625 : ℚ) vp00000000000000111100 := by
  apply branch_checked idp000000000000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-460778/15625 : ℚ) - ((1:ℤ):ℚ) = (-937181/15625 : ℚ) by norm_num]
  exact coverp000000000000001111001
theorem coverp00000000000000111100 : Covers (-460778/15625 : ℚ) vp00000000000000111100 := join_branches bp000000000000001111000 bp000000000000001111001
private noncomputable def vp0000000000000011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011110-V-0000.bin"
noncomputable def vp0000000000000011110 : Blocks := vp0000000000000011110_0
private theorem bp00000000000000111100 : Branch 0 (-230389/15625 : ℚ) vp0000000000000011110 := by
  apply branch_left_normalized (c:=vp00000000000000111100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-230389/15625 : ℚ) - ((0:ℤ):ℚ) = (-460778/15625 : ℚ) by norm_num]
  exact coverp00000000000000111100
private noncomputable def ep00000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111101-E-0000.bin"
noncomputable def ep00000000000000111101 : Blocks := ep00000000000000111101_0
private theorem idp00000000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011110.list =
    C ((2:ℤ)^43) * horner X vp00000000000000111101.list + horner X ep00000000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000111101 : Branch 1 (-230389/15625 : ℚ) vp0000000000000011110 := by
  apply branch_checked idp00000000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-230389/15625 : ℚ) - ((1:ℤ):ℚ) = (-476403/15625 : ℚ) by norm_num]
  exact coverp00000000000000111101
theorem coverp0000000000000011110 : Covers (-230389/15625 : ℚ) vp0000000000000011110 := join_branches bp00000000000000111100 bp00000000000000111101
private noncomputable def vp000000000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111-V-0000.bin"
noncomputable def vp000000000000001111 : Blocks := vp000000000000001111_0
private theorem bp0000000000000011110 : Branch 0 (-230389/31250 : ℚ) vp000000000000001111 := by
  apply branch_left_normalized (c:=vp0000000000000011110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-230389/31250 : ℚ) - ((0:ℤ):ℚ) = (-230389/15625 : ℚ) by norm_num]
  exact coverp0000000000000011110
private noncomputable def ep0000000000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011111-E-0000.bin"
noncomputable def ep0000000000000011111 : Blocks := ep0000000000000011111_0
private theorem idp0000000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001111.list =
    C ((2:ℤ)^68) * horner X vp0000000000000011111.list + horner X ep0000000000000011111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011111 : Branch 1 (-230389/31250 : ℚ) vp000000000000001111 := by
  apply branch_checked idp0000000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-230389/31250 : ℚ) - ((1:ℤ):ℚ) = (-246014/15625 : ℚ) by norm_num]
  exact coverp0000000000000011111
theorem coverp000000000000001111 : Covers (-230389/31250 : ℚ) vp000000000000001111 := join_branches bp0000000000000011110 bp0000000000000011111
private noncomputable def vp0000000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011101111-V-0000.bin"
noncomputable def vp0000000000000011101111 : Blocks := vp0000000000000011101111_0
theorem coverp0000000000000011101111 : Covers (-1827487/15625 : ℚ) vp0000000000000011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011101110-V-0000.bin"
noncomputable def vp0000000000000011101110 : Blocks := vp0000000000000011101110_0
theorem coverp0000000000000011101110 : Covers (-1811862/15625 : ℚ) vp0000000000000011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110111-V-0000.bin"
noncomputable def vp000000000000001110111 : Blocks := vp000000000000001110111_0
private theorem bp0000000000000011101110 : Branch 0 (-905931/15625 : ℚ) vp000000000000001110111 := by
  apply branch_left_normalized (c:=vp0000000000000011101110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-905931/15625 : ℚ) - ((0:ℤ):ℚ) = (-1811862/15625 : ℚ) by norm_num]
  exact coverp0000000000000011101110
private noncomputable def ep0000000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011101111-E-0000.bin"
noncomputable def ep0000000000000011101111 : Blocks := ep0000000000000011101111_0
private theorem idp0000000000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001110111.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011101111.list + horner X ep0000000000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011101111 : Branch 1 (-905931/15625 : ℚ) vp000000000000001110111 := by
  apply branch_checked idp0000000000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-905931/15625 : ℚ) - ((1:ℤ):ℚ) = (-1827487/15625 : ℚ) by norm_num]
  exact coverp0000000000000011101111
theorem coverp000000000000001110111 : Covers (-905931/15625 : ℚ) vp000000000000001110111 := join_branches bp0000000000000011101110 bp0000000000000011101111
private noncomputable def vp000000000000001110110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110110-V-0000.bin"
noncomputable def vp000000000000001110110 : Blocks := vp000000000000001110110_0
theorem coverp000000000000001110110 : Covers (-890306/15625 : ℚ) vp000000000000001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111011-V-0000.bin"
noncomputable def vp00000000000000111011 : Blocks := vp00000000000000111011_0
private theorem bp000000000000001110110 : Branch 0 (-445153/15625 : ℚ) vp00000000000000111011 := by
  apply branch_left_normalized (c:=vp000000000000001110110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-445153/15625 : ℚ) - ((0:ℤ):ℚ) = (-890306/15625 : ℚ) by norm_num]
  exact coverp000000000000001110110
private noncomputable def ep000000000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110111-E-0000.bin"
noncomputable def ep000000000000001110111 : Blocks := ep000000000000001110111_0
private theorem idp000000000000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111011.list =
    C ((2:ℤ)^29) * horner X vp000000000000001110111.list + horner X ep000000000000001110111.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001110111 : Branch 1 (-445153/15625 : ℚ) vp00000000000000111011 := by
  apply branch_checked idp000000000000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-445153/15625 : ℚ) - ((1:ℤ):ℚ) = (-905931/15625 : ℚ) by norm_num]
  exact coverp000000000000001110111
theorem coverp00000000000000111011 : Covers (-445153/15625 : ℚ) vp00000000000000111011 := join_branches bp000000000000001110110 bp000000000000001110111
private noncomputable def vp000000000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110101-V-0000.bin"
noncomputable def vp000000000000001110101 : Blocks := vp000000000000001110101_0
theorem coverp000000000000001110101 : Covers (-874681/15625 : ℚ) vp000000000000001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001110100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110100-V-0000.bin"
noncomputable def vp000000000000001110100 : Blocks := vp000000000000001110100_0
theorem coverp000000000000001110100 : Covers (-859056/15625 : ℚ) vp000000000000001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000111010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111010-V-0000.bin"
noncomputable def vp00000000000000111010 : Blocks := vp00000000000000111010_0
private theorem bp000000000000001110100 : Branch 0 (-429528/15625 : ℚ) vp00000000000000111010 := by
  apply branch_left_normalized (c:=vp000000000000001110100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-429528/15625 : ℚ) - ((0:ℤ):ℚ) = (-859056/15625 : ℚ) by norm_num]
  exact coverp000000000000001110100
private noncomputable def ep000000000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110101-E-0000.bin"
noncomputable def ep000000000000001110101 : Blocks := ep000000000000001110101_0
private theorem idp000000000000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111010.list =
    C ((2:ℤ)^30) * horner X vp000000000000001110101.list + horner X ep000000000000001110101.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001110101 : Branch 1 (-429528/15625 : ℚ) vp00000000000000111010 := by
  apply branch_checked idp000000000000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-429528/15625 : ℚ) - ((1:ℤ):ℚ) = (-874681/15625 : ℚ) by norm_num]
  exact coverp000000000000001110101
theorem coverp00000000000000111010 : Covers (-429528/15625 : ℚ) vp00000000000000111010 := join_branches bp000000000000001110100 bp000000000000001110101
private noncomputable def vp0000000000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011101-V-0000.bin"
noncomputable def vp0000000000000011101 : Blocks := vp0000000000000011101_0
private theorem bp00000000000000111010 : Branch 0 (-214764/15625 : ℚ) vp0000000000000011101 := by
  apply branch_left_normalized (c:=vp00000000000000111010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-214764/15625 : ℚ) - ((0:ℤ):ℚ) = (-429528/15625 : ℚ) by norm_num]
  exact coverp00000000000000111010
private noncomputable def ep00000000000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111011-E-0000.bin"
noncomputable def ep00000000000000111011 : Blocks := ep00000000000000111011_0
private theorem idp00000000000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011101.list =
    C ((2:ℤ)^43) * horner X vp00000000000000111011.list + horner X ep00000000000000111011.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000111011 : Branch 1 (-214764/15625 : ℚ) vp0000000000000011101 := by
  apply branch_checked idp00000000000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-214764/15625 : ℚ) - ((1:ℤ):ℚ) = (-445153/15625 : ℚ) by norm_num]
  exact coverp00000000000000111011
theorem coverp0000000000000011101 : Covers (-214764/15625 : ℚ) vp0000000000000011101 := join_branches bp00000000000000111010 bp00000000000000111011
private noncomputable def vp0000000000000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100111-V-0000.bin"
noncomputable def vp0000000000000011100111 : Blocks := vp0000000000000011100111_0
theorem coverp0000000000000011100111 : Covers (-1702487/15625 : ℚ) vp0000000000000011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100110-V-0000.bin"
noncomputable def vp0000000000000011100110 : Blocks := vp0000000000000011100110_0
theorem coverp0000000000000011100110 : Covers (-1686862/15625 : ℚ) vp0000000000000011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110011-V-0000.bin"
noncomputable def vp000000000000001110011 : Blocks := vp000000000000001110011_0
private theorem bp0000000000000011100110 : Branch 0 (-843431/15625 : ℚ) vp000000000000001110011 := by
  apply branch_left_normalized (c:=vp0000000000000011100110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-843431/15625 : ℚ) - ((0:ℤ):ℚ) = (-1686862/15625 : ℚ) by norm_num]
  exact coverp0000000000000011100110
private noncomputable def ep0000000000000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100111-E-0000.bin"
noncomputable def ep0000000000000011100111 : Blocks := ep0000000000000011100111_0
private theorem idp0000000000000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001110011.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011100111.list + horner X ep0000000000000011100111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011100111 : Branch 1 (-843431/15625 : ℚ) vp000000000000001110011 := by
  apply branch_checked idp0000000000000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-843431/15625 : ℚ) - ((1:ℤ):ℚ) = (-1702487/15625 : ℚ) by norm_num]
  exact coverp0000000000000011100111
theorem coverp000000000000001110011 : Covers (-843431/15625 : ℚ) vp000000000000001110011 := join_branches bp0000000000000011100110 bp0000000000000011100111
private noncomputable def vp000000000000001110010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110010-V-0000.bin"
noncomputable def vp000000000000001110010 : Blocks := vp000000000000001110010_0
theorem coverp000000000000001110010 : Covers (-827806/15625 : ℚ) vp000000000000001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111001-V-0000.bin"
noncomputable def vp00000000000000111001 : Blocks := vp00000000000000111001_0
private theorem bp000000000000001110010 : Branch 0 (-413903/15625 : ℚ) vp00000000000000111001 := by
  apply branch_left_normalized (c:=vp000000000000001110010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-413903/15625 : ℚ) - ((0:ℤ):ℚ) = (-827806/15625 : ℚ) by norm_num]
  exact coverp000000000000001110010
private noncomputable def ep000000000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110011-E-0000.bin"
noncomputable def ep000000000000001110011 : Blocks := ep000000000000001110011_0
private theorem idp000000000000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111001.list =
    C ((2:ℤ)^28) * horner X vp000000000000001110011.list + horner X ep000000000000001110011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001110011 : Branch 1 (-413903/15625 : ℚ) vp00000000000000111001 := by
  apply branch_checked idp000000000000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-413903/15625 : ℚ) - ((1:ℤ):ℚ) = (-843431/15625 : ℚ) by norm_num]
  exact coverp000000000000001110011
theorem coverp00000000000000111001 : Covers (-413903/15625 : ℚ) vp00000000000000111001 := join_branches bp000000000000001110010 bp000000000000001110011
private noncomputable def vp000000000000001110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110001-V-0000.bin"
noncomputable def vp000000000000001110001 : Blocks := vp000000000000001110001_0
theorem coverp000000000000001110001 : Covers (-812181/15625 : ℚ) vp000000000000001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100001-V-0000.bin"
noncomputable def vp0000000000000011100001 : Blocks := vp0000000000000011100001_0
theorem coverp0000000000000011100001 : Covers (-1608737/15625 : ℚ) vp0000000000000011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100000-V-0000.bin"
noncomputable def vp0000000000000011100000 : Blocks := vp0000000000000011100000_0
theorem coverp0000000000000011100000 : Covers (-1593112/15625 : ℚ) vp0000000000000011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001110000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110000-V-0000.bin"
noncomputable def vp000000000000001110000 : Blocks := vp000000000000001110000_0
private theorem bp0000000000000011100000 : Branch 0 (-796556/15625 : ℚ) vp000000000000001110000 := by
  apply branch_left_normalized (c:=vp0000000000000011100000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-796556/15625 : ℚ) - ((0:ℤ):ℚ) = (-1593112/15625 : ℚ) by norm_num]
  exact coverp0000000000000011100000
private noncomputable def ep0000000000000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100001-E-0000.bin"
noncomputable def ep0000000000000011100001 : Blocks := ep0000000000000011100001_0
private theorem idp0000000000000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001110000.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011100001.list + horner X ep0000000000000011100001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011100001 : Branch 1 (-796556/15625 : ℚ) vp000000000000001110000 := by
  apply branch_checked idp0000000000000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-796556/15625 : ℚ) - ((1:ℤ):ℚ) = (-1608737/15625 : ℚ) by norm_num]
  exact coverp0000000000000011100001
theorem coverp000000000000001110000 : Covers (-796556/15625 : ℚ) vp000000000000001110000 := join_branches bp0000000000000011100000 bp0000000000000011100001
private noncomputable def vp00000000000000111000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111000-V-0000.bin"
noncomputable def vp00000000000000111000 : Blocks := vp00000000000000111000_0
private theorem bp000000000000001110000 : Branch 0 (-398278/15625 : ℚ) vp00000000000000111000 := by
  apply branch_left_normalized (c:=vp000000000000001110000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-398278/15625 : ℚ) - ((0:ℤ):ℚ) = (-796556/15625 : ℚ) by norm_num]
  exact coverp000000000000001110000
private noncomputable def ep000000000000001110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110001-E-0000.bin"
noncomputable def ep000000000000001110001 : Blocks := ep000000000000001110001_0
private theorem idp000000000000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111000.list =
    C ((2:ℤ)^30) * horner X vp000000000000001110001.list + horner X ep000000000000001110001.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001110001 : Branch 1 (-398278/15625 : ℚ) vp00000000000000111000 := by
  apply branch_checked idp000000000000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-398278/15625 : ℚ) - ((1:ℤ):ℚ) = (-812181/15625 : ℚ) by norm_num]
  exact coverp000000000000001110001
theorem coverp00000000000000111000 : Covers (-398278/15625 : ℚ) vp00000000000000111000 := join_branches bp000000000000001110000 bp000000000000001110001
private noncomputable def vp0000000000000011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011100-V-0000.bin"
noncomputable def vp0000000000000011100 : Blocks := vp0000000000000011100_0
private theorem bp00000000000000111000 : Branch 0 (-199139/15625 : ℚ) vp0000000000000011100 := by
  apply branch_left_normalized (c:=vp00000000000000111000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-199139/15625 : ℚ) - ((0:ℤ):ℚ) = (-398278/15625 : ℚ) by norm_num]
  exact coverp00000000000000111000
private noncomputable def ep00000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111001-E-0000.bin"
noncomputable def ep00000000000000111001 : Blocks := ep00000000000000111001_0
private theorem idp00000000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011100.list =
    C ((2:ℤ)^44) * horner X vp00000000000000111001.list + horner X ep00000000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000111001 : Branch 1 (-199139/15625 : ℚ) vp0000000000000011100 := by
  apply branch_checked idp00000000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-199139/15625 : ℚ) - ((1:ℤ):ℚ) = (-413903/15625 : ℚ) by norm_num]
  exact coverp00000000000000111001
theorem coverp0000000000000011100 : Covers (-199139/15625 : ℚ) vp0000000000000011100 := join_branches bp00000000000000111000 bp00000000000000111001
private noncomputable def vp000000000000001110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001110-V-0000.bin"
noncomputable def vp000000000000001110 : Blocks := vp000000000000001110_0
private theorem bp0000000000000011100 : Branch 0 (-199139/31250 : ℚ) vp000000000000001110 := by
  apply branch_left_normalized (c:=vp0000000000000011100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-199139/31250 : ℚ) - ((0:ℤ):ℚ) = (-199139/15625 : ℚ) by norm_num]
  exact coverp0000000000000011100
private noncomputable def ep0000000000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011101-E-0000.bin"
noncomputable def ep0000000000000011101 : Blocks := ep0000000000000011101_0
private theorem idp0000000000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001110.list =
    C ((2:ℤ)^70) * horner X vp0000000000000011101.list + horner X ep0000000000000011101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011101 : Branch 1 (-199139/31250 : ℚ) vp000000000000001110 := by
  apply branch_checked idp0000000000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-199139/31250 : ℚ) - ((1:ℤ):ℚ) = (-214764/15625 : ℚ) by norm_num]
  exact coverp0000000000000011101
theorem coverp000000000000001110 : Covers (-199139/31250 : ℚ) vp000000000000001110 := join_branches bp0000000000000011100 bp0000000000000011101
private noncomputable def vp00000000000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111-V-0000.bin"
noncomputable def vp00000000000000111 : Blocks := vp00000000000000111_0
private theorem bp000000000000001110 : Branch 0 (-199139/62500 : ℚ) vp00000000000000111 := by
  apply branch_left_normalized (c:=vp000000000000001110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-199139/31250 : ℚ) by norm_num]
  exact coverp000000000000001110
private noncomputable def ep000000000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001111-E-0000.bin"
noncomputable def ep000000000000001111 : Blocks := ep000000000000001111_0
private theorem idp000000000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000111.list =
    C ((2:ℤ)^127) * horner X vp000000000000001111.list + horner X ep000000000000001111.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001111 : Branch 1 (-199139/62500 : ℚ) vp00000000000000111 := by
  apply branch_checked idp000000000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-230389/31250 : ℚ) by norm_num]
  exact coverp000000000000001111
theorem coverp00000000000000111 : Covers (-199139/62500 : ℚ) vp00000000000000111 := join_branches bp000000000000001110 bp000000000000001111
private noncomputable def vp0000000000000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011111-V-0000.bin"
noncomputable def vp0000000000000011011111 : Blocks := vp0000000000000011011111_0
theorem coverp0000000000000011011111 : Covers (-1577487/15625 : ℚ) vp0000000000000011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011110-V-0000.bin"
noncomputable def vp0000000000000011011110 : Blocks := vp0000000000000011011110_0
theorem coverp0000000000000011011110 : Covers (-1561862/15625 : ℚ) vp0000000000000011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001101111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101111-V-0000.bin"
noncomputable def vp000000000000001101111 : Blocks := vp000000000000001101111_0
private theorem bp0000000000000011011110 : Branch 0 (-780931/15625 : ℚ) vp000000000000001101111 := by
  apply branch_left_normalized (c:=vp0000000000000011011110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-780931/15625 : ℚ) - ((0:ℤ):ℚ) = (-1561862/15625 : ℚ) by norm_num]
  exact coverp0000000000000011011110
private noncomputable def ep0000000000000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011111-E-0000.bin"
noncomputable def ep0000000000000011011111 : Blocks := ep0000000000000011011111_0
private theorem idp0000000000000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001101111.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011011111.list + horner X ep0000000000000011011111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011011111 : Branch 1 (-780931/15625 : ℚ) vp000000000000001101111 := by
  apply branch_checked idp0000000000000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-780931/15625 : ℚ) - ((1:ℤ):ℚ) = (-1577487/15625 : ℚ) by norm_num]
  exact coverp0000000000000011011111
theorem coverp000000000000001101111 : Covers (-780931/15625 : ℚ) vp000000000000001101111 := join_branches bp0000000000000011011110 bp0000000000000011011111
private noncomputable def vp000000000000001101110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101110-V-0000.bin"
noncomputable def vp000000000000001101110 : Blocks := vp000000000000001101110_0
theorem coverp000000000000001101110 : Covers (-765306/15625 : ℚ) vp000000000000001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110111-V-0000.bin"
noncomputable def vp00000000000000110111 : Blocks := vp00000000000000110111_0
private theorem bp000000000000001101110 : Branch 0 (-382653/15625 : ℚ) vp00000000000000110111 := by
  apply branch_left_normalized (c:=vp000000000000001101110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-382653/15625 : ℚ) - ((0:ℤ):ℚ) = (-765306/15625 : ℚ) by norm_num]
  exact coverp000000000000001101110
private noncomputable def ep000000000000001101111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101111-E-0000.bin"
noncomputable def ep000000000000001101111 : Blocks := ep000000000000001101111_0
private theorem idp000000000000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110111.list =
    C ((2:ℤ)^29) * horner X vp000000000000001101111.list + horner X ep000000000000001101111.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001101111 : Branch 1 (-382653/15625 : ℚ) vp00000000000000110111 := by
  apply branch_checked idp000000000000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-382653/15625 : ℚ) - ((1:ℤ):ℚ) = (-780931/15625 : ℚ) by norm_num]
  exact coverp000000000000001101111
theorem coverp00000000000000110111 : Covers (-382653/15625 : ℚ) vp00000000000000110111 := join_branches bp000000000000001101110 bp000000000000001101111
private noncomputable def vp000000000000001101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101101-V-0000.bin"
noncomputable def vp000000000000001101101 : Blocks := vp000000000000001101101_0
theorem coverp000000000000001101101 : Covers (-749681/15625 : ℚ) vp000000000000001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011001-V-0000.bin"
noncomputable def vp0000000000000011011001 : Blocks := vp0000000000000011011001_0
theorem coverp0000000000000011011001 : Covers (-1483737/15625 : ℚ) vp0000000000000011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110110001-V-0000.bin"
noncomputable def vp00000000000000110110001 : Blocks := vp00000000000000110110001_0
theorem coverp00000000000000110110001 : Covers (-2951849/15625 : ℚ) vp00000000000000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110110000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110110000-V-0000.bin"
noncomputable def vp00000000000000110110000 : Blocks := vp00000000000000110110000_0
theorem coverp00000000000000110110000 : Covers (-2936224/15625 : ℚ) vp00000000000000110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011000-V-0000.bin"
noncomputable def vp0000000000000011011000 : Blocks := vp0000000000000011011000_0
private theorem bp00000000000000110110000 : Branch 0 (-1468112/15625 : ℚ) vp0000000000000011011000 := by
  apply branch_left_normalized (c:=vp00000000000000110110000) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-1468112/15625 : ℚ) - ((0:ℤ):ℚ) = (-2936224/15625 : ℚ) by norm_num]
  exact coverp00000000000000110110000
private noncomputable def ep00000000000000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110110001-E-0000.bin"
noncomputable def ep00000000000000110110001 : Blocks := ep00000000000000110110001_0
private theorem idp00000000000000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011011000.list =
    C ((2:ℤ)^17) * horner X vp00000000000000110110001.list + horner X ep00000000000000110110001.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110110001 : Branch 1 (-1468112/15625 : ℚ) vp0000000000000011011000 := by
  apply branch_checked idp00000000000000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1468112/15625 : ℚ) - ((1:ℤ):ℚ) = (-2951849/15625 : ℚ) by norm_num]
  exact coverp00000000000000110110001
theorem coverp0000000000000011011000 : Covers (-1468112/15625 : ℚ) vp0000000000000011011000 := join_branches bp00000000000000110110000 bp00000000000000110110001
private noncomputable def vp000000000000001101100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101100-V-0000.bin"
noncomputable def vp000000000000001101100 : Blocks := vp000000000000001101100_0
private theorem bp0000000000000011011000 : Branch 0 (-734056/15625 : ℚ) vp000000000000001101100 := by
  apply branch_left_normalized (c:=vp0000000000000011011000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-734056/15625 : ℚ) - ((0:ℤ):ℚ) = (-1468112/15625 : ℚ) by norm_num]
  exact coverp0000000000000011011000
private noncomputable def ep0000000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011001-E-0000.bin"
noncomputable def ep0000000000000011011001 : Blocks := ep0000000000000011011001_0
private theorem idp0000000000000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001101100.list =
    C ((2:ℤ)^22) * horner X vp0000000000000011011001.list + horner X ep0000000000000011011001.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011011001 : Branch 1 (-734056/15625 : ℚ) vp000000000000001101100 := by
  apply branch_checked idp0000000000000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-734056/15625 : ℚ) - ((1:ℤ):ℚ) = (-1483737/15625 : ℚ) by norm_num]
  exact coverp0000000000000011011001
theorem coverp000000000000001101100 : Covers (-734056/15625 : ℚ) vp000000000000001101100 := join_branches bp0000000000000011011000 bp0000000000000011011001
private noncomputable def vp00000000000000110110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110110-V-0000.bin"
noncomputable def vp00000000000000110110 : Blocks := vp00000000000000110110_0
private theorem bp000000000000001101100 : Branch 0 (-367028/15625 : ℚ) vp00000000000000110110 := by
  apply branch_left_normalized (c:=vp000000000000001101100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-367028/15625 : ℚ) - ((0:ℤ):ℚ) = (-734056/15625 : ℚ) by norm_num]
  exact coverp000000000000001101100
private noncomputable def ep000000000000001101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101101-E-0000.bin"
noncomputable def ep000000000000001101101 : Blocks := ep000000000000001101101_0
private theorem idp000000000000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110110.list =
    C ((2:ℤ)^30) * horner X vp000000000000001101101.list + horner X ep000000000000001101101.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001101101 : Branch 1 (-367028/15625 : ℚ) vp00000000000000110110 := by
  apply branch_checked idp000000000000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-367028/15625 : ℚ) - ((1:ℤ):ℚ) = (-749681/15625 : ℚ) by norm_num]
  exact coverp000000000000001101101
theorem coverp00000000000000110110 : Covers (-367028/15625 : ℚ) vp00000000000000110110 := join_branches bp000000000000001101100 bp000000000000001101101
private noncomputable def vp0000000000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011-V-0000.bin"
noncomputable def vp0000000000000011011 : Blocks := vp0000000000000011011_0
private theorem bp00000000000000110110 : Branch 0 (-183514/15625 : ℚ) vp0000000000000011011 := by
  apply branch_left_normalized (c:=vp00000000000000110110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-183514/15625 : ℚ) - ((0:ℤ):ℚ) = (-367028/15625 : ℚ) by norm_num]
  exact coverp00000000000000110110
private noncomputable def ep00000000000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110111-E-0000.bin"
noncomputable def ep00000000000000110111 : Blocks := ep00000000000000110111_0
private theorem idp00000000000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011011.list =
    C ((2:ℤ)^44) * horner X vp00000000000000110111.list + horner X ep00000000000000110111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110111 : Branch 1 (-183514/15625 : ℚ) vp0000000000000011011 := by
  apply branch_checked idp00000000000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-183514/15625 : ℚ) - ((1:ℤ):ℚ) = (-382653/15625 : ℚ) by norm_num]
  exact coverp00000000000000110111
theorem coverp0000000000000011011 : Covers (-183514/15625 : ℚ) vp0000000000000011011 := join_branches bp00000000000000110110 bp00000000000000110111
private noncomputable def vp0000000000000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010111-V-0000.bin"
noncomputable def vp0000000000000011010111 : Blocks := vp0000000000000011010111_0
theorem coverp0000000000000011010111 : Covers (-1452487/15625 : ℚ) vp0000000000000011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010110-V-0000.bin"
noncomputable def vp0000000000000011010110 : Blocks := vp0000000000000011010110_0
theorem coverp0000000000000011010110 : Covers (-1436862/15625 : ℚ) vp0000000000000011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101011-V-0000.bin"
noncomputable def vp000000000000001101011 : Blocks := vp000000000000001101011_0
private theorem bp0000000000000011010110 : Branch 0 (-718431/15625 : ℚ) vp000000000000001101011 := by
  apply branch_left_normalized (c:=vp0000000000000011010110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-718431/15625 : ℚ) - ((0:ℤ):ℚ) = (-1436862/15625 : ℚ) by norm_num]
  exact coverp0000000000000011010110
private noncomputable def ep0000000000000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010111-E-0000.bin"
noncomputable def ep0000000000000011010111 : Blocks := ep0000000000000011010111_0
private theorem idp0000000000000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001101011.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011010111.list + horner X ep0000000000000011010111.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011010111 : Branch 1 (-718431/15625 : ℚ) vp000000000000001101011 := by
  apply branch_checked idp0000000000000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-718431/15625 : ℚ) - ((1:ℤ):ℚ) = (-1452487/15625 : ℚ) by norm_num]
  exact coverp0000000000000011010111
theorem coverp000000000000001101011 : Covers (-718431/15625 : ℚ) vp000000000000001101011 := join_branches bp0000000000000011010110 bp0000000000000011010111
private noncomputable def vp000000000000001101010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101010-V-0000.bin"
noncomputable def vp000000000000001101010 : Blocks := vp000000000000001101010_0
theorem coverp000000000000001101010 : Covers (-702806/15625 : ℚ) vp000000000000001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110101-V-0000.bin"
noncomputable def vp00000000000000110101 : Blocks := vp00000000000000110101_0
private theorem bp000000000000001101010 : Branch 0 (-351403/15625 : ℚ) vp00000000000000110101 := by
  apply branch_left_normalized (c:=vp000000000000001101010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-351403/15625 : ℚ) - ((0:ℤ):ℚ) = (-702806/15625 : ℚ) by norm_num]
  exact coverp000000000000001101010
private noncomputable def ep000000000000001101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101011-E-0000.bin"
noncomputable def ep000000000000001101011 : Blocks := ep000000000000001101011_0
private theorem idp000000000000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110101.list =
    C ((2:ℤ)^29) * horner X vp000000000000001101011.list + horner X ep000000000000001101011.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001101011 : Branch 1 (-351403/15625 : ℚ) vp00000000000000110101 := by
  apply branch_checked idp000000000000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-351403/15625 : ℚ) - ((1:ℤ):ℚ) = (-718431/15625 : ℚ) by norm_num]
  exact coverp000000000000001101011
theorem coverp00000000000000110101 : Covers (-351403/15625 : ℚ) vp00000000000000110101 := join_branches bp000000000000001101010 bp000000000000001101011
private noncomputable def vp000000000000001101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101001-V-0000.bin"
noncomputable def vp000000000000001101001 : Blocks := vp000000000000001101001_0
theorem coverp000000000000001101001 : Covers (-687181/15625 : ℚ) vp000000000000001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110100011-V-0000.bin"
noncomputable def vp00000000000000110100011 : Blocks := vp00000000000000110100011_0
theorem coverp00000000000000110100011 : Covers (-2733099/15625 : ℚ) vp00000000000000110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110100010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110100010-V-0000.bin"
noncomputable def vp00000000000000110100010 : Blocks := vp00000000000000110100010_0
theorem coverp00000000000000110100010 : Covers (-2717474/15625 : ℚ) vp00000000000000110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010001-V-0000.bin"
noncomputable def vp0000000000000011010001 : Blocks := vp0000000000000011010001_0
private theorem bp00000000000000110100010 : Branch 0 (-1358737/15625 : ℚ) vp0000000000000011010001 := by
  apply branch_left_normalized (c:=vp00000000000000110100010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-1358737/15625 : ℚ) - ((0:ℤ):ℚ) = (-2717474/15625 : ℚ) by norm_num]
  exact coverp00000000000000110100010
private noncomputable def ep00000000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110100011-E-0000.bin"
noncomputable def ep00000000000000110100011 : Blocks := ep00000000000000110100011_0
private theorem idp00000000000000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011010001.list =
    C ((2:ℤ)^17) * horner X vp00000000000000110100011.list + horner X ep00000000000000110100011.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110100011 : Branch 1 (-1358737/15625 : ℚ) vp0000000000000011010001 := by
  apply branch_checked idp00000000000000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1358737/15625 : ℚ) - ((1:ℤ):ℚ) = (-2733099/15625 : ℚ) by norm_num]
  exact coverp00000000000000110100011
theorem coverp0000000000000011010001 : Covers (-1358737/15625 : ℚ) vp0000000000000011010001 := join_branches bp00000000000000110100010 bp00000000000000110100011
private noncomputable def vp0000000000000011010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010000-V-0000.bin"
noncomputable def vp0000000000000011010000 : Blocks := vp0000000000000011010000_0
theorem coverp0000000000000011010000 : Covers (-1343112/15625 : ℚ) vp0000000000000011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001101000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101000-V-0000.bin"
noncomputable def vp000000000000001101000 : Blocks := vp000000000000001101000_0
private theorem bp0000000000000011010000 : Branch 0 (-671556/15625 : ℚ) vp000000000000001101000 := by
  apply branch_left_normalized (c:=vp0000000000000011010000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-671556/15625 : ℚ) - ((0:ℤ):ℚ) = (-1343112/15625 : ℚ) by norm_num]
  exact coverp0000000000000011010000
private noncomputable def ep0000000000000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010001-E-0000.bin"
noncomputable def ep0000000000000011010001 : Blocks := ep0000000000000011010001_0
private theorem idp0000000000000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001101000.list =
    C ((2:ℤ)^22) * horner X vp0000000000000011010001.list + horner X ep0000000000000011010001.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011010001 : Branch 1 (-671556/15625 : ℚ) vp000000000000001101000 := by
  apply branch_checked idp0000000000000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-671556/15625 : ℚ) - ((1:ℤ):ℚ) = (-1358737/15625 : ℚ) by norm_num]
  exact coverp0000000000000011010001
theorem coverp000000000000001101000 : Covers (-671556/15625 : ℚ) vp000000000000001101000 := join_branches bp0000000000000011010000 bp0000000000000011010001
private noncomputable def vp00000000000000110100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110100-V-0000.bin"
noncomputable def vp00000000000000110100 : Blocks := vp00000000000000110100_0
private theorem bp000000000000001101000 : Branch 0 (-335778/15625 : ℚ) vp00000000000000110100 := by
  apply branch_left_normalized (c:=vp000000000000001101000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-335778/15625 : ℚ) - ((0:ℤ):ℚ) = (-671556/15625 : ℚ) by norm_num]
  exact coverp000000000000001101000
private noncomputable def ep000000000000001101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101001-E-0000.bin"
noncomputable def ep000000000000001101001 : Blocks := ep000000000000001101001_0
private theorem idp000000000000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110100.list =
    C ((2:ℤ)^30) * horner X vp000000000000001101001.list + horner X ep000000000000001101001.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001101001 : Branch 1 (-335778/15625 : ℚ) vp00000000000000110100 := by
  apply branch_checked idp000000000000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-335778/15625 : ℚ) - ((1:ℤ):ℚ) = (-687181/15625 : ℚ) by norm_num]
  exact coverp000000000000001101001
theorem coverp00000000000000110100 : Covers (-335778/15625 : ℚ) vp00000000000000110100 := join_branches bp000000000000001101000 bp000000000000001101001
private noncomputable def vp0000000000000011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011010-V-0000.bin"
noncomputable def vp0000000000000011010 : Blocks := vp0000000000000011010_0
private theorem bp00000000000000110100 : Branch 0 (-167889/15625 : ℚ) vp0000000000000011010 := by
  apply branch_left_normalized (c:=vp00000000000000110100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-167889/15625 : ℚ) - ((0:ℤ):ℚ) = (-335778/15625 : ℚ) by norm_num]
  exact coverp00000000000000110100
private noncomputable def ep00000000000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110101-E-0000.bin"
noncomputable def ep00000000000000110101 : Blocks := ep00000000000000110101_0
private theorem idp00000000000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011010.list =
    C ((2:ℤ)^44) * horner X vp00000000000000110101.list + horner X ep00000000000000110101.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110101 : Branch 1 (-167889/15625 : ℚ) vp0000000000000011010 := by
  apply branch_checked idp00000000000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-167889/15625 : ℚ) - ((1:ℤ):ℚ) = (-351403/15625 : ℚ) by norm_num]
  exact coverp00000000000000110101
theorem coverp0000000000000011010 : Covers (-167889/15625 : ℚ) vp0000000000000011010 := join_branches bp00000000000000110100 bp00000000000000110101
private noncomputable def vp000000000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101-V-0000.bin"
noncomputable def vp000000000000001101 : Blocks := vp000000000000001101_0
private theorem bp0000000000000011010 : Branch 0 (-167889/31250 : ℚ) vp000000000000001101 := by
  apply branch_left_normalized (c:=vp0000000000000011010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-167889/31250 : ℚ) - ((0:ℤ):ℚ) = (-167889/15625 : ℚ) by norm_num]
  exact coverp0000000000000011010
private noncomputable def ep0000000000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011011-E-0000.bin"
noncomputable def ep0000000000000011011 : Blocks := ep0000000000000011011_0
private theorem idp0000000000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001101.list =
    C ((2:ℤ)^71) * horner X vp0000000000000011011.list + horner X ep0000000000000011011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011011 : Branch 1 (-167889/31250 : ℚ) vp000000000000001101 := by
  apply branch_checked idp0000000000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-167889/31250 : ℚ) - ((1:ℤ):ℚ) = (-183514/15625 : ℚ) by norm_num]
  exact coverp0000000000000011011
theorem coverp000000000000001101 : Covers (-167889/31250 : ℚ) vp000000000000001101 := join_branches bp0000000000000011010 bp0000000000000011011
private noncomputable def vp000000000000001100111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100111-V-0000.bin"
noncomputable def vp000000000000001100111 : Blocks := vp000000000000001100111_0
theorem coverp000000000000001100111 : Covers (-655931/15625 : ℚ) vp000000000000001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001100110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100110-V-0000.bin"
noncomputable def vp000000000000001100110 : Blocks := vp000000000000001100110_0
theorem coverp000000000000001100110 : Covers (-640306/15625 : ℚ) vp000000000000001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110011-V-0000.bin"
noncomputable def vp00000000000000110011 : Blocks := vp00000000000000110011_0
private theorem bp000000000000001100110 : Branch 0 (-320153/15625 : ℚ) vp00000000000000110011 := by
  apply branch_left_normalized (c:=vp000000000000001100110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-320153/15625 : ℚ) - ((0:ℤ):ℚ) = (-640306/15625 : ℚ) by norm_num]
  exact coverp000000000000001100110
private noncomputable def ep000000000000001100111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100111-E-0000.bin"
noncomputable def ep000000000000001100111 : Blocks := ep000000000000001100111_0
private theorem idp000000000000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110011.list =
    C ((2:ℤ)^30) * horner X vp000000000000001100111.list + horner X ep000000000000001100111.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001100111 : Branch 1 (-320153/15625 : ℚ) vp00000000000000110011 := by
  apply branch_checked idp000000000000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-320153/15625 : ℚ) - ((1:ℤ):ℚ) = (-655931/15625 : ℚ) by norm_num]
  exact coverp000000000000001100111
theorem coverp00000000000000110011 : Covers (-320153/15625 : ℚ) vp00000000000000110011 := join_branches bp000000000000001100110 bp000000000000001100111
private noncomputable def vp0000000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001011-V-0000.bin"
noncomputable def vp0000000000000011001011 : Blocks := vp0000000000000011001011_0
theorem coverp0000000000000011001011 : Covers (-1264987/15625 : ℚ) vp0000000000000011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110010101-V-0000.bin"
noncomputable def vp00000000000000110010101 : Blocks := vp00000000000000110010101_0
theorem coverp00000000000000110010101 : Covers (-2514349/15625 : ℚ) vp00000000000000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110010100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110010100-V-0000.bin"
noncomputable def vp00000000000000110010100 : Blocks := vp00000000000000110010100_0
theorem coverp00000000000000110010100 : Covers (-2498724/15625 : ℚ) vp00000000000000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001010-V-0000.bin"
noncomputable def vp0000000000000011001010 : Blocks := vp0000000000000011001010_0
private theorem bp00000000000000110010100 : Branch 0 (-1249362/15625 : ℚ) vp0000000000000011001010 := by
  apply branch_left_normalized (c:=vp00000000000000110010100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-1249362/15625 : ℚ) - ((0:ℤ):ℚ) = (-2498724/15625 : ℚ) by norm_num]
  exact coverp00000000000000110010100
private noncomputable def ep00000000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110010101-E-0000.bin"
noncomputable def ep00000000000000110010101 : Blocks := ep00000000000000110010101_0
private theorem idp00000000000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011001010.list =
    C ((2:ℤ)^17) * horner X vp00000000000000110010101.list + horner X ep00000000000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110010101 : Branch 1 (-1249362/15625 : ℚ) vp0000000000000011001010 := by
  apply branch_checked idp00000000000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1249362/15625 : ℚ) - ((1:ℤ):ℚ) = (-2514349/15625 : ℚ) by norm_num]
  exact coverp00000000000000110010101
theorem coverp0000000000000011001010 : Covers (-1249362/15625 : ℚ) vp0000000000000011001010 := join_branches bp00000000000000110010100 bp00000000000000110010101
private noncomputable def vp000000000000001100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100101-V-0000.bin"
noncomputable def vp000000000000001100101 : Blocks := vp000000000000001100101_0
private theorem bp0000000000000011001010 : Branch 0 (-624681/15625 : ℚ) vp000000000000001100101 := by
  apply branch_left_normalized (c:=vp0000000000000011001010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-624681/15625 : ℚ) - ((0:ℤ):ℚ) = (-1249362/15625 : ℚ) by norm_num]
  exact coverp0000000000000011001010
private noncomputable def ep0000000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001011-E-0000.bin"
noncomputable def ep0000000000000011001011 : Blocks := ep0000000000000011001011_0
private theorem idp0000000000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001100101.list =
    C ((2:ℤ)^22) * horner X vp0000000000000011001011.list + horner X ep0000000000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011001011 : Branch 1 (-624681/15625 : ℚ) vp000000000000001100101 := by
  apply branch_checked idp0000000000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-624681/15625 : ℚ) - ((1:ℤ):ℚ) = (-1264987/15625 : ℚ) by norm_num]
  exact coverp0000000000000011001011
theorem coverp000000000000001100101 : Covers (-624681/15625 : ℚ) vp000000000000001100101 := join_branches bp0000000000000011001010 bp0000000000000011001011
private noncomputable def vp0000000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001001-V-0000.bin"
noncomputable def vp0000000000000011001001 : Blocks := vp0000000000000011001001_0
theorem coverp0000000000000011001001 : Covers (-1233737/15625 : ℚ) vp0000000000000011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001000-V-0000.bin"
noncomputable def vp0000000000000011001000 : Blocks := vp0000000000000011001000_0
theorem coverp0000000000000011001000 : Covers (-1218112/15625 : ℚ) vp0000000000000011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001100100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100100-V-0000.bin"
noncomputable def vp000000000000001100100 : Blocks := vp000000000000001100100_0
private theorem bp0000000000000011001000 : Branch 0 (-609056/15625 : ℚ) vp000000000000001100100 := by
  apply branch_left_normalized (c:=vp0000000000000011001000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-609056/15625 : ℚ) - ((0:ℤ):ℚ) = (-1218112/15625 : ℚ) by norm_num]
  exact coverp0000000000000011001000
private noncomputable def ep0000000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001001-E-0000.bin"
noncomputable def ep0000000000000011001001 : Blocks := ep0000000000000011001001_0
private theorem idp0000000000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001100100.list =
    C ((2:ℤ)^21) * horner X vp0000000000000011001001.list + horner X ep0000000000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011001001 : Branch 1 (-609056/15625 : ℚ) vp000000000000001100100 := by
  apply branch_checked idp0000000000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-609056/15625 : ℚ) - ((1:ℤ):ℚ) = (-1233737/15625 : ℚ) by norm_num]
  exact coverp0000000000000011001001
theorem coverp000000000000001100100 : Covers (-609056/15625 : ℚ) vp000000000000001100100 := join_branches bp0000000000000011001000 bp0000000000000011001001
private noncomputable def vp00000000000000110010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110010-V-0000.bin"
noncomputable def vp00000000000000110010 : Blocks := vp00000000000000110010_0
private theorem bp000000000000001100100 : Branch 0 (-304528/15625 : ℚ) vp00000000000000110010 := by
  apply branch_left_normalized (c:=vp000000000000001100100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-304528/15625 : ℚ) - ((0:ℤ):ℚ) = (-609056/15625 : ℚ) by norm_num]
  exact coverp000000000000001100100
private noncomputable def ep000000000000001100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100101-E-0000.bin"
noncomputable def ep000000000000001100101 : Blocks := ep000000000000001100101_0
private theorem idp000000000000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110010.list =
    C ((2:ℤ)^30) * horner X vp000000000000001100101.list + horner X ep000000000000001100101.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001100101 : Branch 1 (-304528/15625 : ℚ) vp00000000000000110010 := by
  apply branch_checked idp000000000000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-304528/15625 : ℚ) - ((1:ℤ):ℚ) = (-624681/15625 : ℚ) by norm_num]
  exact coverp000000000000001100101
theorem coverp00000000000000110010 : Covers (-304528/15625 : ℚ) vp00000000000000110010 := join_branches bp000000000000001100100 bp000000000000001100101
private noncomputable def vp0000000000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001-V-0000.bin"
noncomputable def vp0000000000000011001 : Blocks := vp0000000000000011001_0
private theorem bp00000000000000110010 : Branch 0 (-152264/15625 : ℚ) vp0000000000000011001 := by
  apply branch_left_normalized (c:=vp00000000000000110010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-152264/15625 : ℚ) - ((0:ℤ):ℚ) = (-304528/15625 : ℚ) by norm_num]
  exact coverp00000000000000110010
private noncomputable def ep00000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110011-E-0000.bin"
noncomputable def ep00000000000000110011 : Blocks := ep00000000000000110011_0
private theorem idp00000000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011001.list =
    C ((2:ℤ)^45) * horner X vp00000000000000110011.list + horner X ep00000000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110011 : Branch 1 (-152264/15625 : ℚ) vp0000000000000011001 := by
  apply branch_checked idp00000000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-152264/15625 : ℚ) - ((1:ℤ):ℚ) = (-320153/15625 : ℚ) by norm_num]
  exact coverp00000000000000110011
theorem coverp0000000000000011001 : Covers (-152264/15625 : ℚ) vp0000000000000011001 := join_branches bp00000000000000110010 bp00000000000000110011
private noncomputable def vp000000000000001100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100011-V-0000.bin"
noncomputable def vp000000000000001100011 : Blocks := vp000000000000001100011_0
theorem coverp000000000000001100011 : Covers (-593431/15625 : ℚ) vp000000000000001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001100010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100010-V-0000.bin"
noncomputable def vp000000000000001100010 : Blocks := vp000000000000001100010_0
theorem coverp000000000000001100010 : Covers (-577806/15625 : ℚ) vp000000000000001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110001-V-0000.bin"
noncomputable def vp00000000000000110001 : Blocks := vp00000000000000110001_0
private theorem bp000000000000001100010 : Branch 0 (-288903/15625 : ℚ) vp00000000000000110001 := by
  apply branch_left_normalized (c:=vp000000000000001100010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-288903/15625 : ℚ) - ((0:ℤ):ℚ) = (-577806/15625 : ℚ) by norm_num]
  exact coverp000000000000001100010
private noncomputable def ep000000000000001100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100011-E-0000.bin"
noncomputable def ep000000000000001100011 : Blocks := ep000000000000001100011_0
private theorem idp000000000000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110001.list =
    C ((2:ℤ)^31) * horner X vp000000000000001100011.list + horner X ep000000000000001100011.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001100011 : Branch 1 (-288903/15625 : ℚ) vp00000000000000110001 := by
  apply branch_checked idp000000000000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-288903/15625 : ℚ) - ((1:ℤ):ℚ) = (-593431/15625 : ℚ) by norm_num]
  exact coverp000000000000001100011
theorem coverp00000000000000110001 : Covers (-288903/15625 : ℚ) vp00000000000000110001 := join_branches bp000000000000001100010 bp000000000000001100011
private noncomputable def vp00000000000000110000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110000111-V-0000.bin"
noncomputable def vp00000000000000110000111 : Blocks := vp00000000000000110000111_0
theorem coverp00000000000000110000111 : Covers (-2295599/15625 : ℚ) vp00000000000000110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110000110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110000110-V-0000.bin"
noncomputable def vp00000000000000110000110 : Blocks := vp00000000000000110000110_0
theorem coverp00000000000000110000110 : Covers (-2279974/15625 : ℚ) vp00000000000000110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011000011-V-0000.bin"
noncomputable def vp0000000000000011000011 : Blocks := vp0000000000000011000011_0
private theorem bp00000000000000110000110 : Branch 0 (-1139987/15625 : ℚ) vp0000000000000011000011 := by
  apply branch_left_normalized (c:=vp00000000000000110000110) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-1139987/15625 : ℚ) - ((0:ℤ):ℚ) = (-2279974/15625 : ℚ) by norm_num]
  exact coverp00000000000000110000110
private noncomputable def ep00000000000000110000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110000111-E-0000.bin"
noncomputable def ep00000000000000110000111 : Blocks := ep00000000000000110000111_0
private theorem idp00000000000000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011000011.list =
    C ((2:ℤ)^17) * horner X vp00000000000000110000111.list + horner X ep00000000000000110000111.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110000111 : Branch 1 (-1139987/15625 : ℚ) vp0000000000000011000011 := by
  apply branch_checked idp00000000000000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1139987/15625 : ℚ) - ((1:ℤ):ℚ) = (-2295599/15625 : ℚ) by norm_num]
  exact coverp00000000000000110000111
theorem coverp0000000000000011000011 : Covers (-1139987/15625 : ℚ) vp0000000000000011000011 := join_branches bp00000000000000110000110 bp00000000000000110000111
private noncomputable def vp0000000000000011000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011000010-V-0000.bin"
noncomputable def vp0000000000000011000010 : Blocks := vp0000000000000011000010_0
theorem coverp0000000000000011000010 : Covers (-1124362/15625 : ℚ) vp0000000000000011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100001-V-0000.bin"
noncomputable def vp000000000000001100001 : Blocks := vp000000000000001100001_0
private theorem bp0000000000000011000010 : Branch 0 (-562181/15625 : ℚ) vp000000000000001100001 := by
  apply branch_left_normalized (c:=vp0000000000000011000010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-562181/15625 : ℚ) - ((0:ℤ):ℚ) = (-1124362/15625 : ℚ) by norm_num]
  exact coverp0000000000000011000010
private noncomputable def ep0000000000000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011000011-E-0000.bin"
noncomputable def ep0000000000000011000011 : Blocks := ep0000000000000011000011_0
private theorem idp0000000000000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001100001.list =
    C ((2:ℤ)^22) * horner X vp0000000000000011000011.list + horner X ep0000000000000011000011.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011000011 : Branch 1 (-562181/15625 : ℚ) vp000000000000001100001 := by
  apply branch_checked idp0000000000000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-562181/15625 : ℚ) - ((1:ℤ):ℚ) = (-1139987/15625 : ℚ) by norm_num]
  exact coverp0000000000000011000011
theorem coverp000000000000001100001 : Covers (-562181/15625 : ℚ) vp000000000000001100001 := join_branches bp0000000000000011000010 bp0000000000000011000011
private noncomputable def vp000000000000001100000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100000-V-0000.bin"
noncomputable def vp000000000000001100000 : Blocks := vp000000000000001100000_0
theorem coverp000000000000001100000 : Covers (-546556/15625 : ℚ) vp000000000000001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000110000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110000-V-0000.bin"
noncomputable def vp00000000000000110000 : Blocks := vp00000000000000110000_0
private theorem bp000000000000001100000 : Branch 0 (-273278/15625 : ℚ) vp00000000000000110000 := by
  apply branch_left_normalized (c:=vp000000000000001100000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-273278/15625 : ℚ) - ((0:ℤ):ℚ) = (-546556/15625 : ℚ) by norm_num]
  exact coverp000000000000001100000
private noncomputable def ep000000000000001100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100001-E-0000.bin"
noncomputable def ep000000000000001100001 : Blocks := ep000000000000001100001_0
private theorem idp000000000000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110000.list =
    C ((2:ℤ)^30) * horner X vp000000000000001100001.list + horner X ep000000000000001100001.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001100001 : Branch 1 (-273278/15625 : ℚ) vp00000000000000110000 := by
  apply branch_checked idp000000000000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-273278/15625 : ℚ) - ((1:ℤ):ℚ) = (-562181/15625 : ℚ) by norm_num]
  exact coverp000000000000001100001
theorem coverp00000000000000110000 : Covers (-273278/15625 : ℚ) vp00000000000000110000 := join_branches bp000000000000001100000 bp000000000000001100001
private noncomputable def vp0000000000000011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011000-V-0000.bin"
noncomputable def vp0000000000000011000 : Blocks := vp0000000000000011000_0
private theorem bp00000000000000110000 : Branch 0 (-136639/15625 : ℚ) vp0000000000000011000 := by
  apply branch_left_normalized (c:=vp00000000000000110000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-136639/15625 : ℚ) - ((0:ℤ):ℚ) = (-273278/15625 : ℚ) by norm_num]
  exact coverp00000000000000110000
private noncomputable def ep00000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110001-E-0000.bin"
noncomputable def ep00000000000000110001 : Blocks := ep00000000000000110001_0
private theorem idp00000000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011000.list =
    C ((2:ℤ)^45) * horner X vp00000000000000110001.list + horner X ep00000000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000110001 : Branch 1 (-136639/15625 : ℚ) vp0000000000000011000 := by
  apply branch_checked idp00000000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-136639/15625 : ℚ) - ((1:ℤ):ℚ) = (-288903/15625 : ℚ) by norm_num]
  exact coverp00000000000000110001
theorem coverp0000000000000011000 : Covers (-136639/15625 : ℚ) vp0000000000000011000 := join_branches bp00000000000000110000 bp00000000000000110001
private noncomputable def vp000000000000001100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001100-V-0000.bin"
noncomputable def vp000000000000001100 : Blocks := vp000000000000001100_0
private theorem bp0000000000000011000 : Branch 0 (-136639/31250 : ℚ) vp000000000000001100 := by
  apply branch_left_normalized (c:=vp0000000000000011000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-136639/31250 : ℚ) - ((0:ℤ):ℚ) = (-136639/15625 : ℚ) by norm_num]
  exact coverp0000000000000011000
private noncomputable def ep0000000000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011001-E-0000.bin"
noncomputable def ep0000000000000011001 : Blocks := ep0000000000000011001_0
private theorem idp0000000000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001100.list =
    C ((2:ℤ)^72) * horner X vp0000000000000011001.list + horner X ep0000000000000011001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011001 : Branch 1 (-136639/31250 : ℚ) vp000000000000001100 := by
  apply branch_checked idp0000000000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-136639/31250 : ℚ) - ((1:ℤ):ℚ) = (-152264/15625 : ℚ) by norm_num]
  exact coverp0000000000000011001
theorem coverp000000000000001100 : Covers (-136639/31250 : ℚ) vp000000000000001100 := join_branches bp0000000000000011000 bp0000000000000011001
private noncomputable def vp00000000000000110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000110-V-0000.bin"
noncomputable def vp00000000000000110 : Blocks := vp00000000000000110_0
private theorem bp000000000000001100 : Branch 0 (-136639/62500 : ℚ) vp00000000000000110 := by
  apply branch_left_normalized (c:=vp000000000000001100) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-136639/31250 : ℚ) by norm_num]
  exact coverp000000000000001100
private noncomputable def ep000000000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001101-E-0000.bin"
noncomputable def ep000000000000001101 : Blocks := ep000000000000001101_0
private theorem idp000000000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000110.list =
    C ((2:ℤ)^123) * horner X vp000000000000001101.list + horner X ep000000000000001101.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001101 : Branch 1 (-136639/62500 : ℚ) vp00000000000000110 := by
  apply branch_checked idp000000000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-167889/31250 : ℚ) by norm_num]
  exact coverp000000000000001101
theorem coverp00000000000000110 : Covers (-136639/62500 : ℚ) vp00000000000000110 := join_branches bp000000000000001100 bp000000000000001101
private noncomputable def vp0000000000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011-V-0000.bin"
private noncomputable def vp0000000000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000000000011-V-0001.bin"
noncomputable def vp0000000000000011 : Blocks := (Blocks.join vp0000000000000011_0 vp0000000000000011_1)
private theorem bp00000000000000110 : Branch 0 (-136639/125000 : ℚ) vp0000000000000011 := by
  apply branch_left_normalized (c:=vp00000000000000110) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-136639/62500 : ℚ) by norm_num]
  exact coverp00000000000000110
private noncomputable def ep00000000000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000111-E-0000.bin"
private noncomputable def ep00000000000000111_1 : Blocks := edgeBlocks% "full/vectors/00000000000000111-E-0001.bin"
noncomputable def ep00000000000000111 : Blocks := (Blocks.join ep00000000000000111_0 ep00000000000000111_1)
private theorem idp00000000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000011.list =
    C ((2:ℤ)^237) * horner X vp00000000000000111.list + horner X ep00000000000000111.list := by
  exact edge_identity (B := (2:ℤ)^428) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000111 : Branch 1 (-136639/125000 : ℚ) vp0000000000000011 := by
  apply branch_checked idp00000000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-199139/62500 : ℚ) by norm_num]
  exact coverp00000000000000111
theorem coverp0000000000000011 : Covers (-136639/125000 : ℚ) vp0000000000000011 := join_branches bp00000000000000110 bp00000000000000111
end NextProof.EdgeFull

