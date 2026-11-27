import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00040
import NextProof.EdgeFull00042

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000010_0 : Blocks := edgeBlocks% "full/vectors/0000010-V-0000.bin"
private noncomputable def vp0000010_1 : Blocks := edgeBlocks% "full/vectors/0000010-V-0001.bin"
private noncomputable def vp0000010_2 : Blocks := edgeBlocks% "full/vectors/0000010-V-0002.bin"
private noncomputable def vp0000010_3 : Blocks := edgeBlocks% "full/vectors/0000010-V-0003.bin"
private noncomputable def vp0000010_4 : Blocks := edgeBlocks% "full/vectors/0000010-V-0004.bin"
private noncomputable def vp0000010_5 : Blocks := edgeBlocks% "full/vectors/0000010-V-0005.bin"
private noncomputable def vp0000010_6 : Blocks := edgeBlocks% "full/vectors/0000010-V-0006.bin"
private noncomputable def vp0000010_7 : Blocks := edgeBlocks% "full/vectors/0000010-V-0007.bin"
private noncomputable def vp0000010_8 : Blocks := edgeBlocks% "full/vectors/0000010-V-0008.bin"
private noncomputable def vp0000010_9 : Blocks := edgeBlocks% "full/vectors/0000010-V-0009.bin"
private noncomputable def vp0000010_10 : Blocks := edgeBlocks% "full/vectors/0000010-V-0010.bin"
private noncomputable def vp0000010_11 : Blocks := edgeBlocks% "full/vectors/0000010-V-0011.bin"
private noncomputable def vp0000010_12 : Blocks := edgeBlocks% "full/vectors/0000010-V-0012.bin"
private noncomputable def vp0000010_13 : Blocks := edgeBlocks% "full/vectors/0000010-V-0013.bin"
private noncomputable def vp0000010_14 : Blocks := edgeBlocks% "full/vectors/0000010-V-0014.bin"
private noncomputable def vp0000010_15 : Blocks := edgeBlocks% "full/vectors/0000010-V-0015.bin"
private noncomputable def vp0000010_16 : Blocks := edgeBlocks% "full/vectors/0000010-V-0016.bin"
private noncomputable def vp0000010_17 : Blocks := edgeBlocks% "full/vectors/0000010-V-0017.bin"
private noncomputable def vp0000010_18 : Blocks := edgeBlocks% "full/vectors/0000010-V-0018.bin"
private noncomputable def vp0000010_19 : Blocks := edgeBlocks% "full/vectors/0000010-V-0019.bin"
private noncomputable def vp0000010_20 : Blocks := edgeBlocks% "full/vectors/0000010-V-0020.bin"
private noncomputable def vp0000010_21 : Blocks := edgeBlocks% "full/vectors/0000010-V-0021.bin"
private noncomputable def vp0000010_22 : Blocks := edgeBlocks% "full/vectors/0000010-V-0022.bin"
private noncomputable def vp0000010_23 : Blocks := edgeBlocks% "full/vectors/0000010-V-0023.bin"
private noncomputable def vp0000010_24 : Blocks := edgeBlocks% "full/vectors/0000010-V-0024.bin"
private noncomputable def vp0000010_25 : Blocks := edgeBlocks% "full/vectors/0000010-V-0025.bin"
private noncomputable def vp0000010_26 : Blocks := edgeBlocks% "full/vectors/0000010-V-0026.bin"
private noncomputable def vp0000010_27 : Blocks := edgeBlocks% "full/vectors/0000010-V-0027.bin"
private noncomputable def vp0000010_28 : Blocks := edgeBlocks% "full/vectors/0000010-V-0028.bin"
private noncomputable def vp0000010_29 : Blocks := edgeBlocks% "full/vectors/0000010-V-0029.bin"
private noncomputable def vp0000010_30 : Blocks := edgeBlocks% "full/vectors/0000010-V-0030.bin"
private noncomputable def vp0000010_31 : Blocks := edgeBlocks% "full/vectors/0000010-V-0031.bin"
private noncomputable def vp0000010_32 : Blocks := edgeBlocks% "full/vectors/0000010-V-0032.bin"
private noncomputable def vp0000010_33 : Blocks := edgeBlocks% "full/vectors/0000010-V-0033.bin"
private noncomputable def vp0000010_34 : Blocks := edgeBlocks% "full/vectors/0000010-V-0034.bin"
private noncomputable def vp0000010_35 : Blocks := edgeBlocks% "full/vectors/0000010-V-0035.bin"
private noncomputable def vp0000010_36 : Blocks := edgeBlocks% "full/vectors/0000010-V-0036.bin"
private noncomputable def vp0000010_37 : Blocks := edgeBlocks% "full/vectors/0000010-V-0037.bin"
private noncomputable def vp0000010_38 : Blocks := edgeBlocks% "full/vectors/0000010-V-0038.bin"
private noncomputable def vp0000010_39 : Blocks := edgeBlocks% "full/vectors/0000010-V-0039.bin"
noncomputable def vp0000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000010_0 vp0000010_1) (Blocks.join vp0000010_2 (Blocks.join vp0000010_3 vp0000010_4))) (Blocks.join (Blocks.join vp0000010_5 vp0000010_6) (Blocks.join vp0000010_7 (Blocks.join vp0000010_8 vp0000010_9)))) (Blocks.join (Blocks.join (Blocks.join vp0000010_10 vp0000010_11) (Blocks.join vp0000010_12 (Blocks.join vp0000010_13 vp0000010_14))) (Blocks.join (Blocks.join vp0000010_15 vp0000010_16) (Blocks.join vp0000010_17 (Blocks.join vp0000010_18 vp0000010_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000010_20 vp0000010_21) (Blocks.join vp0000010_22 (Blocks.join vp0000010_23 vp0000010_24))) (Blocks.join (Blocks.join vp0000010_25 vp0000010_26) (Blocks.join vp0000010_27 (Blocks.join vp0000010_28 vp0000010_29)))) (Blocks.join (Blocks.join (Blocks.join vp0000010_30 vp0000010_31) (Blocks.join vp0000010_32 (Blocks.join vp0000010_33 vp0000010_34))) (Blocks.join (Blocks.join vp0000010_35 vp0000010_36) (Blocks.join vp0000010_37 (Blocks.join vp0000010_38 vp0000010_39))))))
private theorem bp00000100 : Branch 0 (-127761639/64000000 : ℚ) vp0000010 := by
  apply branch_left_normalized (c:=vp00000100) (k:=0) (m:=2680) (by decide +kernel)
  rw [show 2*(-127761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/32000000 : ℚ) by norm_num]
  exact coverp00000100
private noncomputable def ep00000101_0 : Blocks := edgeBlocks% "full/vectors/00000101-E-0000.bin"
private noncomputable def ep00000101_1 : Blocks := edgeBlocks% "full/vectors/00000101-E-0001.bin"
private noncomputable def ep00000101_2 : Blocks := edgeBlocks% "full/vectors/00000101-E-0002.bin"
private noncomputable def ep00000101_3 : Blocks := edgeBlocks% "full/vectors/00000101-E-0003.bin"
private noncomputable def ep00000101_4 : Blocks := edgeBlocks% "full/vectors/00000101-E-0004.bin"
private noncomputable def ep00000101_5 : Blocks := edgeBlocks% "full/vectors/00000101-E-0005.bin"
private noncomputable def ep00000101_6 : Blocks := edgeBlocks% "full/vectors/00000101-E-0006.bin"
private noncomputable def ep00000101_7 : Blocks := edgeBlocks% "full/vectors/00000101-E-0007.bin"
private noncomputable def ep00000101_8 : Blocks := edgeBlocks% "full/vectors/00000101-E-0008.bin"
private noncomputable def ep00000101_9 : Blocks := edgeBlocks% "full/vectors/00000101-E-0009.bin"
private noncomputable def ep00000101_10 : Blocks := edgeBlocks% "full/vectors/00000101-E-0010.bin"
private noncomputable def ep00000101_11 : Blocks := edgeBlocks% "full/vectors/00000101-E-0011.bin"
private noncomputable def ep00000101_12 : Blocks := edgeBlocks% "full/vectors/00000101-E-0012.bin"
private noncomputable def ep00000101_13 : Blocks := edgeBlocks% "full/vectors/00000101-E-0013.bin"
private noncomputable def ep00000101_14 : Blocks := edgeBlocks% "full/vectors/00000101-E-0014.bin"
private noncomputable def ep00000101_15 : Blocks := edgeBlocks% "full/vectors/00000101-E-0015.bin"
private noncomputable def ep00000101_16 : Blocks := edgeBlocks% "full/vectors/00000101-E-0016.bin"
private noncomputable def ep00000101_17 : Blocks := edgeBlocks% "full/vectors/00000101-E-0017.bin"
private noncomputable def ep00000101_18 : Blocks := edgeBlocks% "full/vectors/00000101-E-0018.bin"
private noncomputable def ep00000101_19 : Blocks := edgeBlocks% "full/vectors/00000101-E-0019.bin"
private noncomputable def ep00000101_20 : Blocks := edgeBlocks% "full/vectors/00000101-E-0020.bin"
private noncomputable def ep00000101_21 : Blocks := edgeBlocks% "full/vectors/00000101-E-0021.bin"
private noncomputable def ep00000101_22 : Blocks := edgeBlocks% "full/vectors/00000101-E-0022.bin"
private noncomputable def ep00000101_23 : Blocks := edgeBlocks% "full/vectors/00000101-E-0023.bin"
private noncomputable def ep00000101_24 : Blocks := edgeBlocks% "full/vectors/00000101-E-0024.bin"
private noncomputable def ep00000101_25 : Blocks := edgeBlocks% "full/vectors/00000101-E-0025.bin"
private noncomputable def ep00000101_26 : Blocks := edgeBlocks% "full/vectors/00000101-E-0026.bin"
private noncomputable def ep00000101_27 : Blocks := edgeBlocks% "full/vectors/00000101-E-0027.bin"
private noncomputable def ep00000101_28 : Blocks := edgeBlocks% "full/vectors/00000101-E-0028.bin"
private noncomputable def ep00000101_29 : Blocks := edgeBlocks% "full/vectors/00000101-E-0029.bin"
private noncomputable def ep00000101_30 : Blocks := edgeBlocks% "full/vectors/00000101-E-0030.bin"
private noncomputable def ep00000101_31 : Blocks := edgeBlocks% "full/vectors/00000101-E-0031.bin"
private noncomputable def ep00000101_32 : Blocks := edgeBlocks% "full/vectors/00000101-E-0032.bin"
private noncomputable def ep00000101_33 : Blocks := edgeBlocks% "full/vectors/00000101-E-0033.bin"
private noncomputable def ep00000101_34 : Blocks := edgeBlocks% "full/vectors/00000101-E-0034.bin"
private noncomputable def ep00000101_35 : Blocks := edgeBlocks% "full/vectors/00000101-E-0035.bin"
private noncomputable def ep00000101_36 : Blocks := edgeBlocks% "full/vectors/00000101-E-0036.bin"
private noncomputable def ep00000101_37 : Blocks := edgeBlocks% "full/vectors/00000101-E-0037.bin"
private noncomputable def ep00000101_38 : Blocks := edgeBlocks% "full/vectors/00000101-E-0038.bin"
private noncomputable def ep00000101_39 : Blocks := edgeBlocks% "full/vectors/00000101-E-0039.bin"
noncomputable def ep00000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000101_0 ep00000101_1) (Blocks.join ep00000101_2 (Blocks.join ep00000101_3 ep00000101_4))) (Blocks.join (Blocks.join ep00000101_5 ep00000101_6) (Blocks.join ep00000101_7 (Blocks.join ep00000101_8 ep00000101_9)))) (Blocks.join (Blocks.join (Blocks.join ep00000101_10 ep00000101_11) (Blocks.join ep00000101_12 (Blocks.join ep00000101_13 ep00000101_14))) (Blocks.join (Blocks.join ep00000101_15 ep00000101_16) (Blocks.join ep00000101_17 (Blocks.join ep00000101_18 ep00000101_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000101_20 ep00000101_21) (Blocks.join ep00000101_22 (Blocks.join ep00000101_23 ep00000101_24))) (Blocks.join (Blocks.join ep00000101_25 ep00000101_26) (Blocks.join ep00000101_27 (Blocks.join ep00000101_28 ep00000101_29)))) (Blocks.join (Blocks.join (Blocks.join ep00000101_30 ep00000101_31) (Blocks.join ep00000101_32 (Blocks.join ep00000101_33 ep00000101_34))) (Blocks.join (Blocks.join ep00000101_35 ep00000101_36) (Blocks.join ep00000101_37 (Blocks.join ep00000101_38 ep00000101_39))))))
private def ptsp00000101 : List ℤ := [((2:ℤ)^2346+0),((2:ℤ)^2346+1),((2:ℤ)^2346+2),((2:ℤ)^2346+3)]
private theorem boundp00000101 : 2^vp0000010.size*absSum vp0000010.list + ((2:ℤ)^5296*absSum vp00000101.list+absSum ep00000101.list) < (2:ℤ)^8068 := by decide +kernel
private theorem pointp00000101_0 : fastHom 1 ((2:ℤ)^2346+0) vp0000010 = ((2:ℤ)^5296)*vp00000101.subst ((2:ℤ)^2346+0)+ep00000101.subst ((2:ℤ)^2346+0) := by decide +kernel
private theorem pointp00000101_1 : fastHom 1 ((2:ℤ)^2346+1) vp0000010 = ((2:ℤ)^5296)*vp00000101.subst ((2:ℤ)^2346+1)+ep00000101.subst ((2:ℤ)^2346+1) := by decide +kernel
private theorem pointp00000101_2 : fastHom 1 ((2:ℤ)^2346+2) vp0000010 = ((2:ℤ)^5296)*vp00000101.subst ((2:ℤ)^2346+2)+ep00000101.subst ((2:ℤ)^2346+2) := by decide +kernel
private theorem pointp00000101_3 : fastHom 1 ((2:ℤ)^2346+3) vp0000010 = ((2:ℤ)^5296)*vp00000101.subst ((2:ℤ)^2346+3)+ep00000101.subst ((2:ℤ)^2346+3) := by decide +kernel
private theorem checkp00000101 (x:ℤ) (hx:x ∈ ptsp00000101) : fastHom 1 x vp0000010 = ((2:ℤ)^5296)*vp00000101.subst x+ep00000101.subst x := by
  simp only [ptsp00000101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp00000101_0
  · exact pointp00000101_1
  · exact pointp00000101_2
  · exact pointp00000101_3
private theorem idp00000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010.list =
    C ((2:ℤ)^5296) * horner X vp00000101.list + horner X ep00000101.list := by
  apply edge_identity (B := (2:ℤ)^8068) (by decide) (by positivity) (by positivity) boundp00000101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00000101 (by decide +kernel)
  · have h : ptsp00000101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00000101.trans_le (by decide +kernel)
  · exact checkp00000101
private theorem bp00000101 : Branch 1 (-127761639/64000000 : ℚ) vp0000010 := by
  apply branch_checked idp00000101 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-159761639/32000000 : ℚ) by norm_num]
  exact coverp00000101
theorem coverp0000010 : Covers (-127761639/64000000 : ℚ) vp0000010 := join_branches bp00000100 bp00000101
end NextProof.EdgeFull

