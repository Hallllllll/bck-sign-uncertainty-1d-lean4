import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00098
import NextProof.EdgeFull00100

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00110_0 : Blocks := edgeBlocks% "full/vectors/00110-V-0000.bin"
private noncomputable def vp00110_1 : Blocks := edgeBlocks% "full/vectors/00110-V-0001.bin"
private noncomputable def vp00110_2 : Blocks := edgeBlocks% "full/vectors/00110-V-0002.bin"
private noncomputable def vp00110_3 : Blocks := edgeBlocks% "full/vectors/00110-V-0003.bin"
private noncomputable def vp00110_4 : Blocks := edgeBlocks% "full/vectors/00110-V-0004.bin"
private noncomputable def vp00110_5 : Blocks := edgeBlocks% "full/vectors/00110-V-0005.bin"
private noncomputable def vp00110_6 : Blocks := edgeBlocks% "full/vectors/00110-V-0006.bin"
private noncomputable def vp00110_7 : Blocks := edgeBlocks% "full/vectors/00110-V-0007.bin"
private noncomputable def vp00110_8 : Blocks := edgeBlocks% "full/vectors/00110-V-0008.bin"
private noncomputable def vp00110_9 : Blocks := edgeBlocks% "full/vectors/00110-V-0009.bin"
private noncomputable def vp00110_10 : Blocks := edgeBlocks% "full/vectors/00110-V-0010.bin"
private noncomputable def vp00110_11 : Blocks := edgeBlocks% "full/vectors/00110-V-0011.bin"
private noncomputable def vp00110_12 : Blocks := edgeBlocks% "full/vectors/00110-V-0012.bin"
private noncomputable def vp00110_13 : Blocks := edgeBlocks% "full/vectors/00110-V-0013.bin"
private noncomputable def vp00110_14 : Blocks := edgeBlocks% "full/vectors/00110-V-0014.bin"
private noncomputable def vp00110_15 : Blocks := edgeBlocks% "full/vectors/00110-V-0015.bin"
private noncomputable def vp00110_16 : Blocks := edgeBlocks% "full/vectors/00110-V-0016.bin"
private noncomputable def vp00110_17 : Blocks := edgeBlocks% "full/vectors/00110-V-0017.bin"
private noncomputable def vp00110_18 : Blocks := edgeBlocks% "full/vectors/00110-V-0018.bin"
private noncomputable def vp00110_19 : Blocks := edgeBlocks% "full/vectors/00110-V-0019.bin"
private noncomputable def vp00110_20 : Blocks := edgeBlocks% "full/vectors/00110-V-0020.bin"
private noncomputable def vp00110_21 : Blocks := edgeBlocks% "full/vectors/00110-V-0021.bin"
private noncomputable def vp00110_22 : Blocks := edgeBlocks% "full/vectors/00110-V-0022.bin"
private noncomputable def vp00110_23 : Blocks := edgeBlocks% "full/vectors/00110-V-0023.bin"
private noncomputable def vp00110_24 : Blocks := edgeBlocks% "full/vectors/00110-V-0024.bin"
private noncomputable def vp00110_25 : Blocks := edgeBlocks% "full/vectors/00110-V-0025.bin"
private noncomputable def vp00110_26 : Blocks := edgeBlocks% "full/vectors/00110-V-0026.bin"
private noncomputable def vp00110_27 : Blocks := edgeBlocks% "full/vectors/00110-V-0027.bin"
private noncomputable def vp00110_28 : Blocks := edgeBlocks% "full/vectors/00110-V-0028.bin"
private noncomputable def vp00110_29 : Blocks := edgeBlocks% "full/vectors/00110-V-0029.bin"
private noncomputable def vp00110_30 : Blocks := edgeBlocks% "full/vectors/00110-V-0030.bin"
private noncomputable def vp00110_31 : Blocks := edgeBlocks% "full/vectors/00110-V-0031.bin"
private noncomputable def vp00110_32 : Blocks := edgeBlocks% "full/vectors/00110-V-0032.bin"
private noncomputable def vp00110_33 : Blocks := edgeBlocks% "full/vectors/00110-V-0033.bin"
private noncomputable def vp00110_34 : Blocks := edgeBlocks% "full/vectors/00110-V-0034.bin"
private noncomputable def vp00110_35 : Blocks := edgeBlocks% "full/vectors/00110-V-0035.bin"
private noncomputable def vp00110_36 : Blocks := edgeBlocks% "full/vectors/00110-V-0036.bin"
private noncomputable def vp00110_37 : Blocks := edgeBlocks% "full/vectors/00110-V-0037.bin"
private noncomputable def vp00110_38 : Blocks := edgeBlocks% "full/vectors/00110-V-0038.bin"
private noncomputable def vp00110_39 : Blocks := edgeBlocks% "full/vectors/00110-V-0039.bin"
private noncomputable def vp00110_40 : Blocks := edgeBlocks% "full/vectors/00110-V-0040.bin"
private noncomputable def vp00110_41 : Blocks := edgeBlocks% "full/vectors/00110-V-0041.bin"
private noncomputable def vp00110_42 : Blocks := edgeBlocks% "full/vectors/00110-V-0042.bin"
private noncomputable def vp00110_43 : Blocks := edgeBlocks% "full/vectors/00110-V-0043.bin"
private noncomputable def vp00110_44 : Blocks := edgeBlocks% "full/vectors/00110-V-0044.bin"
private noncomputable def vp00110_45 : Blocks := edgeBlocks% "full/vectors/00110-V-0045.bin"
noncomputable def vp00110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00110_0 vp00110_1) (Blocks.join vp00110_2 (Blocks.join vp00110_3 vp00110_4))) (Blocks.join (Blocks.join vp00110_5 (Blocks.join vp00110_6 vp00110_7)) (Blocks.join vp00110_8 (Blocks.join vp00110_9 vp00110_10)))) (Blocks.join (Blocks.join (Blocks.join vp00110_11 (Blocks.join vp00110_12 vp00110_13)) (Blocks.join vp00110_14 (Blocks.join vp00110_15 vp00110_16))) (Blocks.join (Blocks.join vp00110_17 (Blocks.join vp00110_18 vp00110_19)) (Blocks.join vp00110_20 (Blocks.join vp00110_21 vp00110_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00110_23 vp00110_24) (Blocks.join vp00110_25 (Blocks.join vp00110_26 vp00110_27))) (Blocks.join (Blocks.join vp00110_28 (Blocks.join vp00110_29 vp00110_30)) (Blocks.join vp00110_31 (Blocks.join vp00110_32 vp00110_33)))) (Blocks.join (Blocks.join (Blocks.join vp00110_34 (Blocks.join vp00110_35 vp00110_36)) (Blocks.join vp00110_37 (Blocks.join vp00110_38 vp00110_39))) (Blocks.join (Blocks.join vp00110_40 (Blocks.join vp00110_41 vp00110_42)) (Blocks.join vp00110_43 (Blocks.join vp00110_44 vp00110_45))))))
private theorem bp001100 : Branch 0 (-1535761639/256000000 : ℚ) vp00110 := by
  apply branch_left_normalized (c:=vp001100) (k:=0) (m:=3078) (by decide +kernel)
  rw [show 2*(-1535761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/128000000 : ℚ) by norm_num]
  exact coverp001100
private noncomputable def ep001101_0 : Blocks := edgeBlocks% "full/vectors/001101-E-0000.bin"
private noncomputable def ep001101_1 : Blocks := edgeBlocks% "full/vectors/001101-E-0001.bin"
private noncomputable def ep001101_2 : Blocks := edgeBlocks% "full/vectors/001101-E-0002.bin"
private noncomputable def ep001101_3 : Blocks := edgeBlocks% "full/vectors/001101-E-0003.bin"
private noncomputable def ep001101_4 : Blocks := edgeBlocks% "full/vectors/001101-E-0004.bin"
private noncomputable def ep001101_5 : Blocks := edgeBlocks% "full/vectors/001101-E-0005.bin"
private noncomputable def ep001101_6 : Blocks := edgeBlocks% "full/vectors/001101-E-0006.bin"
private noncomputable def ep001101_7 : Blocks := edgeBlocks% "full/vectors/001101-E-0007.bin"
private noncomputable def ep001101_8 : Blocks := edgeBlocks% "full/vectors/001101-E-0008.bin"
private noncomputable def ep001101_9 : Blocks := edgeBlocks% "full/vectors/001101-E-0009.bin"
private noncomputable def ep001101_10 : Blocks := edgeBlocks% "full/vectors/001101-E-0010.bin"
private noncomputable def ep001101_11 : Blocks := edgeBlocks% "full/vectors/001101-E-0011.bin"
private noncomputable def ep001101_12 : Blocks := edgeBlocks% "full/vectors/001101-E-0012.bin"
private noncomputable def ep001101_13 : Blocks := edgeBlocks% "full/vectors/001101-E-0013.bin"
private noncomputable def ep001101_14 : Blocks := edgeBlocks% "full/vectors/001101-E-0014.bin"
private noncomputable def ep001101_15 : Blocks := edgeBlocks% "full/vectors/001101-E-0015.bin"
private noncomputable def ep001101_16 : Blocks := edgeBlocks% "full/vectors/001101-E-0016.bin"
private noncomputable def ep001101_17 : Blocks := edgeBlocks% "full/vectors/001101-E-0017.bin"
private noncomputable def ep001101_18 : Blocks := edgeBlocks% "full/vectors/001101-E-0018.bin"
private noncomputable def ep001101_19 : Blocks := edgeBlocks% "full/vectors/001101-E-0019.bin"
private noncomputable def ep001101_20 : Blocks := edgeBlocks% "full/vectors/001101-E-0020.bin"
private noncomputable def ep001101_21 : Blocks := edgeBlocks% "full/vectors/001101-E-0021.bin"
private noncomputable def ep001101_22 : Blocks := edgeBlocks% "full/vectors/001101-E-0022.bin"
private noncomputable def ep001101_23 : Blocks := edgeBlocks% "full/vectors/001101-E-0023.bin"
private noncomputable def ep001101_24 : Blocks := edgeBlocks% "full/vectors/001101-E-0024.bin"
private noncomputable def ep001101_25 : Blocks := edgeBlocks% "full/vectors/001101-E-0025.bin"
private noncomputable def ep001101_26 : Blocks := edgeBlocks% "full/vectors/001101-E-0026.bin"
private noncomputable def ep001101_27 : Blocks := edgeBlocks% "full/vectors/001101-E-0027.bin"
private noncomputable def ep001101_28 : Blocks := edgeBlocks% "full/vectors/001101-E-0028.bin"
private noncomputable def ep001101_29 : Blocks := edgeBlocks% "full/vectors/001101-E-0029.bin"
private noncomputable def ep001101_30 : Blocks := edgeBlocks% "full/vectors/001101-E-0030.bin"
private noncomputable def ep001101_31 : Blocks := edgeBlocks% "full/vectors/001101-E-0031.bin"
private noncomputable def ep001101_32 : Blocks := edgeBlocks% "full/vectors/001101-E-0032.bin"
private noncomputable def ep001101_33 : Blocks := edgeBlocks% "full/vectors/001101-E-0033.bin"
private noncomputable def ep001101_34 : Blocks := edgeBlocks% "full/vectors/001101-E-0034.bin"
private noncomputable def ep001101_35 : Blocks := edgeBlocks% "full/vectors/001101-E-0035.bin"
private noncomputable def ep001101_36 : Blocks := edgeBlocks% "full/vectors/001101-E-0036.bin"
private noncomputable def ep001101_37 : Blocks := edgeBlocks% "full/vectors/001101-E-0037.bin"
private noncomputable def ep001101_38 : Blocks := edgeBlocks% "full/vectors/001101-E-0038.bin"
private noncomputable def ep001101_39 : Blocks := edgeBlocks% "full/vectors/001101-E-0039.bin"
private noncomputable def ep001101_40 : Blocks := edgeBlocks% "full/vectors/001101-E-0040.bin"
private noncomputable def ep001101_41 : Blocks := edgeBlocks% "full/vectors/001101-E-0041.bin"
private noncomputable def ep001101_42 : Blocks := edgeBlocks% "full/vectors/001101-E-0042.bin"
private noncomputable def ep001101_43 : Blocks := edgeBlocks% "full/vectors/001101-E-0043.bin"
private noncomputable def ep001101_44 : Blocks := edgeBlocks% "full/vectors/001101-E-0044.bin"
private noncomputable def ep001101_45 : Blocks := edgeBlocks% "full/vectors/001101-E-0045.bin"
noncomputable def ep001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001101_0 ep001101_1) (Blocks.join ep001101_2 (Blocks.join ep001101_3 ep001101_4))) (Blocks.join (Blocks.join ep001101_5 (Blocks.join ep001101_6 ep001101_7)) (Blocks.join ep001101_8 (Blocks.join ep001101_9 ep001101_10)))) (Blocks.join (Blocks.join (Blocks.join ep001101_11 (Blocks.join ep001101_12 ep001101_13)) (Blocks.join ep001101_14 (Blocks.join ep001101_15 ep001101_16))) (Blocks.join (Blocks.join ep001101_17 (Blocks.join ep001101_18 ep001101_19)) (Blocks.join ep001101_20 (Blocks.join ep001101_21 ep001101_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001101_23 ep001101_24) (Blocks.join ep001101_25 (Blocks.join ep001101_26 ep001101_27))) (Blocks.join (Blocks.join ep001101_28 (Blocks.join ep001101_29 ep001101_30)) (Blocks.join ep001101_31 (Blocks.join ep001101_32 ep001101_33)))) (Blocks.join (Blocks.join (Blocks.join ep001101_34 (Blocks.join ep001101_35 ep001101_36)) (Blocks.join ep001101_37 (Blocks.join ep001101_38 ep001101_39))) (Blocks.join (Blocks.join ep001101_40 (Blocks.join ep001101_41 ep001101_42)) (Blocks.join ep001101_43 (Blocks.join ep001101_44 ep001101_45))))))
private def ptsp001101 : List ℤ := [((2:ℤ)^2059+0),((2:ℤ)^2059+1),((2:ℤ)^2059+2),((2:ℤ)^2059+3),((2:ℤ)^2059+4)]
private theorem boundp001101 : 2^vp00110.size*absSum vp00110.list + ((2:ℤ)^6566*absSum vp001101.list+absSum ep001101.list) < (2:ℤ)^9220 := by decide +kernel
private theorem pointp001101_0 : fastHom 1 ((2:ℤ)^2059+0) vp00110 = ((2:ℤ)^6566)*vp001101.subst ((2:ℤ)^2059+0)+ep001101.subst ((2:ℤ)^2059+0) := by decide +kernel
private theorem pointp001101_1 : fastHom 1 ((2:ℤ)^2059+1) vp00110 = ((2:ℤ)^6566)*vp001101.subst ((2:ℤ)^2059+1)+ep001101.subst ((2:ℤ)^2059+1) := by decide +kernel
private theorem pointp001101_2 : fastHom 1 ((2:ℤ)^2059+2) vp00110 = ((2:ℤ)^6566)*vp001101.subst ((2:ℤ)^2059+2)+ep001101.subst ((2:ℤ)^2059+2) := by decide +kernel
private theorem pointp001101_3 : fastHom 1 ((2:ℤ)^2059+3) vp00110 = ((2:ℤ)^6566)*vp001101.subst ((2:ℤ)^2059+3)+ep001101.subst ((2:ℤ)^2059+3) := by decide +kernel
private theorem pointp001101_4 : fastHom 1 ((2:ℤ)^2059+4) vp00110 = ((2:ℤ)^6566)*vp001101.subst ((2:ℤ)^2059+4)+ep001101.subst ((2:ℤ)^2059+4) := by decide +kernel
private theorem checkp001101 (x:ℤ) (hx:x ∈ ptsp001101) : fastHom 1 x vp00110 = ((2:ℤ)^6566)*vp001101.subst x+ep001101.subst x := by
  simp only [ptsp001101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp001101_0
  · exact pointp001101_1
  · exact pointp001101_2
  · exact pointp001101_3
  · exact pointp001101_4
private theorem idp001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110.list =
    C ((2:ℤ)^6566) * horner X vp001101.list + horner X ep001101.list := by
  apply edge_identity (B := (2:ℤ)^9220) (by decide) (by positivity) (by positivity) boundp001101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp001101 (by decide +kernel)
  · have h : ptsp001101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp001101.trans_le (by decide +kernel)
  · exact checkp001101
private theorem bp001101 : Branch 1 (-1535761639/256000000 : ℚ) vp00110 := by
  apply branch_checked idp001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-1663761639/128000000 : ℚ) by norm_num]
  exact coverp001101
theorem coverp00110 : Covers (-1535761639/256000000 : ℚ) vp00110 := join_branches bp001100 bp001101
end NextProof.EdgeFull

