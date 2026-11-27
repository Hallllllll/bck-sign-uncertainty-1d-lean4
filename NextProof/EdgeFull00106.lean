import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00103
import NextProof.EdgeFull00105

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00111_0 : Blocks := edgeBlocks% "full/vectors/00111-V-0000.bin"
private noncomputable def vp00111_1 : Blocks := edgeBlocks% "full/vectors/00111-V-0001.bin"
private noncomputable def vp00111_2 : Blocks := edgeBlocks% "full/vectors/00111-V-0002.bin"
private noncomputable def vp00111_3 : Blocks := edgeBlocks% "full/vectors/00111-V-0003.bin"
private noncomputable def vp00111_4 : Blocks := edgeBlocks% "full/vectors/00111-V-0004.bin"
private noncomputable def vp00111_5 : Blocks := edgeBlocks% "full/vectors/00111-V-0005.bin"
private noncomputable def vp00111_6 : Blocks := edgeBlocks% "full/vectors/00111-V-0006.bin"
private noncomputable def vp00111_7 : Blocks := edgeBlocks% "full/vectors/00111-V-0007.bin"
private noncomputable def vp00111_8 : Blocks := edgeBlocks% "full/vectors/00111-V-0008.bin"
private noncomputable def vp00111_9 : Blocks := edgeBlocks% "full/vectors/00111-V-0009.bin"
private noncomputable def vp00111_10 : Blocks := edgeBlocks% "full/vectors/00111-V-0010.bin"
private noncomputable def vp00111_11 : Blocks := edgeBlocks% "full/vectors/00111-V-0011.bin"
private noncomputable def vp00111_12 : Blocks := edgeBlocks% "full/vectors/00111-V-0012.bin"
private noncomputable def vp00111_13 : Blocks := edgeBlocks% "full/vectors/00111-V-0013.bin"
private noncomputable def vp00111_14 : Blocks := edgeBlocks% "full/vectors/00111-V-0014.bin"
private noncomputable def vp00111_15 : Blocks := edgeBlocks% "full/vectors/00111-V-0015.bin"
private noncomputable def vp00111_16 : Blocks := edgeBlocks% "full/vectors/00111-V-0016.bin"
private noncomputable def vp00111_17 : Blocks := edgeBlocks% "full/vectors/00111-V-0017.bin"
private noncomputable def vp00111_18 : Blocks := edgeBlocks% "full/vectors/00111-V-0018.bin"
private noncomputable def vp00111_19 : Blocks := edgeBlocks% "full/vectors/00111-V-0019.bin"
private noncomputable def vp00111_20 : Blocks := edgeBlocks% "full/vectors/00111-V-0020.bin"
private noncomputable def vp00111_21 : Blocks := edgeBlocks% "full/vectors/00111-V-0021.bin"
private noncomputable def vp00111_22 : Blocks := edgeBlocks% "full/vectors/00111-V-0022.bin"
private noncomputable def vp00111_23 : Blocks := edgeBlocks% "full/vectors/00111-V-0023.bin"
private noncomputable def vp00111_24 : Blocks := edgeBlocks% "full/vectors/00111-V-0024.bin"
private noncomputable def vp00111_25 : Blocks := edgeBlocks% "full/vectors/00111-V-0025.bin"
private noncomputable def vp00111_26 : Blocks := edgeBlocks% "full/vectors/00111-V-0026.bin"
private noncomputable def vp00111_27 : Blocks := edgeBlocks% "full/vectors/00111-V-0027.bin"
private noncomputable def vp00111_28 : Blocks := edgeBlocks% "full/vectors/00111-V-0028.bin"
private noncomputable def vp00111_29 : Blocks := edgeBlocks% "full/vectors/00111-V-0029.bin"
private noncomputable def vp00111_30 : Blocks := edgeBlocks% "full/vectors/00111-V-0030.bin"
private noncomputable def vp00111_31 : Blocks := edgeBlocks% "full/vectors/00111-V-0031.bin"
private noncomputable def vp00111_32 : Blocks := edgeBlocks% "full/vectors/00111-V-0032.bin"
private noncomputable def vp00111_33 : Blocks := edgeBlocks% "full/vectors/00111-V-0033.bin"
private noncomputable def vp00111_34 : Blocks := edgeBlocks% "full/vectors/00111-V-0034.bin"
private noncomputable def vp00111_35 : Blocks := edgeBlocks% "full/vectors/00111-V-0035.bin"
private noncomputable def vp00111_36 : Blocks := edgeBlocks% "full/vectors/00111-V-0036.bin"
private noncomputable def vp00111_37 : Blocks := edgeBlocks% "full/vectors/00111-V-0037.bin"
private noncomputable def vp00111_38 : Blocks := edgeBlocks% "full/vectors/00111-V-0038.bin"
private noncomputable def vp00111_39 : Blocks := edgeBlocks% "full/vectors/00111-V-0039.bin"
private noncomputable def vp00111_40 : Blocks := edgeBlocks% "full/vectors/00111-V-0040.bin"
private noncomputable def vp00111_41 : Blocks := edgeBlocks% "full/vectors/00111-V-0041.bin"
private noncomputable def vp00111_42 : Blocks := edgeBlocks% "full/vectors/00111-V-0042.bin"
noncomputable def vp00111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00111_0 vp00111_1) (Blocks.join vp00111_2 (Blocks.join vp00111_3 vp00111_4))) (Blocks.join (Blocks.join vp00111_5 vp00111_6) (Blocks.join vp00111_7 (Blocks.join vp00111_8 vp00111_9)))) (Blocks.join (Blocks.join (Blocks.join vp00111_10 vp00111_11) (Blocks.join vp00111_12 (Blocks.join vp00111_13 vp00111_14))) (Blocks.join (Blocks.join vp00111_15 (Blocks.join vp00111_16 vp00111_17)) (Blocks.join vp00111_18 (Blocks.join vp00111_19 vp00111_20))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00111_21 vp00111_22) (Blocks.join vp00111_23 (Blocks.join vp00111_24 vp00111_25))) (Blocks.join (Blocks.join vp00111_26 (Blocks.join vp00111_27 vp00111_28)) (Blocks.join vp00111_29 (Blocks.join vp00111_30 vp00111_31)))) (Blocks.join (Blocks.join (Blocks.join vp00111_32 vp00111_33) (Blocks.join vp00111_34 (Blocks.join vp00111_35 vp00111_36))) (Blocks.join (Blocks.join vp00111_37 (Blocks.join vp00111_38 vp00111_39)) (Blocks.join vp00111_40 (Blocks.join vp00111_41 vp00111_42))))))
private theorem bp001110 : Branch 0 (-1791761639/256000000 : ℚ) vp00111 := by
  apply branch_left_normalized (c:=vp001110) (k:=0) (m:=2863) (by decide +kernel)
  rw [show 2*(-1791761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/128000000 : ℚ) by norm_num]
  exact coverp001110
private noncomputable def ep001111_0 : Blocks := edgeBlocks% "full/vectors/001111-E-0000.bin"
private noncomputable def ep001111_1 : Blocks := edgeBlocks% "full/vectors/001111-E-0001.bin"
private noncomputable def ep001111_2 : Blocks := edgeBlocks% "full/vectors/001111-E-0002.bin"
private noncomputable def ep001111_3 : Blocks := edgeBlocks% "full/vectors/001111-E-0003.bin"
private noncomputable def ep001111_4 : Blocks := edgeBlocks% "full/vectors/001111-E-0004.bin"
private noncomputable def ep001111_5 : Blocks := edgeBlocks% "full/vectors/001111-E-0005.bin"
private noncomputable def ep001111_6 : Blocks := edgeBlocks% "full/vectors/001111-E-0006.bin"
private noncomputable def ep001111_7 : Blocks := edgeBlocks% "full/vectors/001111-E-0007.bin"
private noncomputable def ep001111_8 : Blocks := edgeBlocks% "full/vectors/001111-E-0008.bin"
private noncomputable def ep001111_9 : Blocks := edgeBlocks% "full/vectors/001111-E-0009.bin"
private noncomputable def ep001111_10 : Blocks := edgeBlocks% "full/vectors/001111-E-0010.bin"
private noncomputable def ep001111_11 : Blocks := edgeBlocks% "full/vectors/001111-E-0011.bin"
private noncomputable def ep001111_12 : Blocks := edgeBlocks% "full/vectors/001111-E-0012.bin"
private noncomputable def ep001111_13 : Blocks := edgeBlocks% "full/vectors/001111-E-0013.bin"
private noncomputable def ep001111_14 : Blocks := edgeBlocks% "full/vectors/001111-E-0014.bin"
private noncomputable def ep001111_15 : Blocks := edgeBlocks% "full/vectors/001111-E-0015.bin"
private noncomputable def ep001111_16 : Blocks := edgeBlocks% "full/vectors/001111-E-0016.bin"
private noncomputable def ep001111_17 : Blocks := edgeBlocks% "full/vectors/001111-E-0017.bin"
private noncomputable def ep001111_18 : Blocks := edgeBlocks% "full/vectors/001111-E-0018.bin"
private noncomputable def ep001111_19 : Blocks := edgeBlocks% "full/vectors/001111-E-0019.bin"
private noncomputable def ep001111_20 : Blocks := edgeBlocks% "full/vectors/001111-E-0020.bin"
private noncomputable def ep001111_21 : Blocks := edgeBlocks% "full/vectors/001111-E-0021.bin"
private noncomputable def ep001111_22 : Blocks := edgeBlocks% "full/vectors/001111-E-0022.bin"
private noncomputable def ep001111_23 : Blocks := edgeBlocks% "full/vectors/001111-E-0023.bin"
private noncomputable def ep001111_24 : Blocks := edgeBlocks% "full/vectors/001111-E-0024.bin"
private noncomputable def ep001111_25 : Blocks := edgeBlocks% "full/vectors/001111-E-0025.bin"
private noncomputable def ep001111_26 : Blocks := edgeBlocks% "full/vectors/001111-E-0026.bin"
private noncomputable def ep001111_27 : Blocks := edgeBlocks% "full/vectors/001111-E-0027.bin"
private noncomputable def ep001111_28 : Blocks := edgeBlocks% "full/vectors/001111-E-0028.bin"
private noncomputable def ep001111_29 : Blocks := edgeBlocks% "full/vectors/001111-E-0029.bin"
private noncomputable def ep001111_30 : Blocks := edgeBlocks% "full/vectors/001111-E-0030.bin"
private noncomputable def ep001111_31 : Blocks := edgeBlocks% "full/vectors/001111-E-0031.bin"
private noncomputable def ep001111_32 : Blocks := edgeBlocks% "full/vectors/001111-E-0032.bin"
private noncomputable def ep001111_33 : Blocks := edgeBlocks% "full/vectors/001111-E-0033.bin"
private noncomputable def ep001111_34 : Blocks := edgeBlocks% "full/vectors/001111-E-0034.bin"
private noncomputable def ep001111_35 : Blocks := edgeBlocks% "full/vectors/001111-E-0035.bin"
private noncomputable def ep001111_36 : Blocks := edgeBlocks% "full/vectors/001111-E-0036.bin"
private noncomputable def ep001111_37 : Blocks := edgeBlocks% "full/vectors/001111-E-0037.bin"
private noncomputable def ep001111_38 : Blocks := edgeBlocks% "full/vectors/001111-E-0038.bin"
private noncomputable def ep001111_39 : Blocks := edgeBlocks% "full/vectors/001111-E-0039.bin"
private noncomputable def ep001111_40 : Blocks := edgeBlocks% "full/vectors/001111-E-0040.bin"
private noncomputable def ep001111_41 : Blocks := edgeBlocks% "full/vectors/001111-E-0041.bin"
private noncomputable def ep001111_42 : Blocks := edgeBlocks% "full/vectors/001111-E-0042.bin"
noncomputable def ep001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001111_0 ep001111_1) (Blocks.join ep001111_2 (Blocks.join ep001111_3 ep001111_4))) (Blocks.join (Blocks.join ep001111_5 ep001111_6) (Blocks.join ep001111_7 (Blocks.join ep001111_8 ep001111_9)))) (Blocks.join (Blocks.join (Blocks.join ep001111_10 ep001111_11) (Blocks.join ep001111_12 (Blocks.join ep001111_13 ep001111_14))) (Blocks.join (Blocks.join ep001111_15 (Blocks.join ep001111_16 ep001111_17)) (Blocks.join ep001111_18 (Blocks.join ep001111_19 ep001111_20))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001111_21 ep001111_22) (Blocks.join ep001111_23 (Blocks.join ep001111_24 ep001111_25))) (Blocks.join (Blocks.join ep001111_26 (Blocks.join ep001111_27 ep001111_28)) (Blocks.join ep001111_29 (Blocks.join ep001111_30 ep001111_31)))) (Blocks.join (Blocks.join (Blocks.join ep001111_32 ep001111_33) (Blocks.join ep001111_34 (Blocks.join ep001111_35 ep001111_36))) (Blocks.join (Blocks.join ep001111_37 (Blocks.join ep001111_38 ep001111_39)) (Blocks.join ep001111_40 (Blocks.join ep001111_41 ep001111_42))))))
private def ptsp001111 : List ℤ := [((2:ℤ)^2205+0),((2:ℤ)^2205+1),((2:ℤ)^2205+2),((2:ℤ)^2205+3)]
private theorem boundp001111 : 2^vp00111.size*absSum vp00111.list + ((2:ℤ)^6179*absSum vp001111.list+absSum ep001111.list) < (2:ℤ)^8597 := by decide +kernel
private theorem pointp001111_0 : fastHom 1 ((2:ℤ)^2205+0) vp00111 = ((2:ℤ)^6179)*vp001111.subst ((2:ℤ)^2205+0)+ep001111.subst ((2:ℤ)^2205+0) := by decide +kernel
private theorem pointp001111_1 : fastHom 1 ((2:ℤ)^2205+1) vp00111 = ((2:ℤ)^6179)*vp001111.subst ((2:ℤ)^2205+1)+ep001111.subst ((2:ℤ)^2205+1) := by decide +kernel
private theorem pointp001111_2 : fastHom 1 ((2:ℤ)^2205+2) vp00111 = ((2:ℤ)^6179)*vp001111.subst ((2:ℤ)^2205+2)+ep001111.subst ((2:ℤ)^2205+2) := by decide +kernel
private theorem pointp001111_3 : fastHom 1 ((2:ℤ)^2205+3) vp00111 = ((2:ℤ)^6179)*vp001111.subst ((2:ℤ)^2205+3)+ep001111.subst ((2:ℤ)^2205+3) := by decide +kernel
private theorem checkp001111 (x:ℤ) (hx:x ∈ ptsp001111) : fastHom 1 x vp00111 = ((2:ℤ)^6179)*vp001111.subst x+ep001111.subst x := by
  simp only [ptsp001111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp001111_0
  · exact pointp001111_1
  · exact pointp001111_2
  · exact pointp001111_3
private theorem idp001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111.list =
    C ((2:ℤ)^6179) * horner X vp001111.list + horner X ep001111.list := by
  apply edge_identity (B := (2:ℤ)^8597) (by decide) (by positivity) (by positivity) boundp001111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp001111 (by decide +kernel)
  · have h : ptsp001111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp001111.trans_le (by decide +kernel)
  · exact checkp001111
private theorem bp001111 : Branch 1 (-1791761639/256000000 : ℚ) vp00111 := by
  apply branch_checked idp001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-1919761639/128000000 : ℚ) by norm_num]
  exact coverp001111
theorem coverp00111 : Covers (-1791761639/256000000 : ℚ) vp00111 := join_branches bp001110 bp001111
end NextProof.EdgeFull

