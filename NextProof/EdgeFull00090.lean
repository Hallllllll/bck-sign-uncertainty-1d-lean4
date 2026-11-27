import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00087
import NextProof.EdgeFull00089

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00100_0 : Blocks := edgeBlocks% "full/vectors/00100-V-0000.bin"
private noncomputable def vp00100_1 : Blocks := edgeBlocks% "full/vectors/00100-V-0001.bin"
private noncomputable def vp00100_2 : Blocks := edgeBlocks% "full/vectors/00100-V-0002.bin"
private noncomputable def vp00100_3 : Blocks := edgeBlocks% "full/vectors/00100-V-0003.bin"
private noncomputable def vp00100_4 : Blocks := edgeBlocks% "full/vectors/00100-V-0004.bin"
private noncomputable def vp00100_5 : Blocks := edgeBlocks% "full/vectors/00100-V-0005.bin"
private noncomputable def vp00100_6 : Blocks := edgeBlocks% "full/vectors/00100-V-0006.bin"
private noncomputable def vp00100_7 : Blocks := edgeBlocks% "full/vectors/00100-V-0007.bin"
private noncomputable def vp00100_8 : Blocks := edgeBlocks% "full/vectors/00100-V-0008.bin"
private noncomputable def vp00100_9 : Blocks := edgeBlocks% "full/vectors/00100-V-0009.bin"
private noncomputable def vp00100_10 : Blocks := edgeBlocks% "full/vectors/00100-V-0010.bin"
private noncomputable def vp00100_11 : Blocks := edgeBlocks% "full/vectors/00100-V-0011.bin"
private noncomputable def vp00100_12 : Blocks := edgeBlocks% "full/vectors/00100-V-0012.bin"
private noncomputable def vp00100_13 : Blocks := edgeBlocks% "full/vectors/00100-V-0013.bin"
private noncomputable def vp00100_14 : Blocks := edgeBlocks% "full/vectors/00100-V-0014.bin"
private noncomputable def vp00100_15 : Blocks := edgeBlocks% "full/vectors/00100-V-0015.bin"
private noncomputable def vp00100_16 : Blocks := edgeBlocks% "full/vectors/00100-V-0016.bin"
private noncomputable def vp00100_17 : Blocks := edgeBlocks% "full/vectors/00100-V-0017.bin"
private noncomputable def vp00100_18 : Blocks := edgeBlocks% "full/vectors/00100-V-0018.bin"
private noncomputable def vp00100_19 : Blocks := edgeBlocks% "full/vectors/00100-V-0019.bin"
private noncomputable def vp00100_20 : Blocks := edgeBlocks% "full/vectors/00100-V-0020.bin"
private noncomputable def vp00100_21 : Blocks := edgeBlocks% "full/vectors/00100-V-0021.bin"
private noncomputable def vp00100_22 : Blocks := edgeBlocks% "full/vectors/00100-V-0022.bin"
private noncomputable def vp00100_23 : Blocks := edgeBlocks% "full/vectors/00100-V-0023.bin"
private noncomputable def vp00100_24 : Blocks := edgeBlocks% "full/vectors/00100-V-0024.bin"
private noncomputable def vp00100_25 : Blocks := edgeBlocks% "full/vectors/00100-V-0025.bin"
private noncomputable def vp00100_26 : Blocks := edgeBlocks% "full/vectors/00100-V-0026.bin"
private noncomputable def vp00100_27 : Blocks := edgeBlocks% "full/vectors/00100-V-0027.bin"
private noncomputable def vp00100_28 : Blocks := edgeBlocks% "full/vectors/00100-V-0028.bin"
private noncomputable def vp00100_29 : Blocks := edgeBlocks% "full/vectors/00100-V-0029.bin"
private noncomputable def vp00100_30 : Blocks := edgeBlocks% "full/vectors/00100-V-0030.bin"
private noncomputable def vp00100_31 : Blocks := edgeBlocks% "full/vectors/00100-V-0031.bin"
private noncomputable def vp00100_32 : Blocks := edgeBlocks% "full/vectors/00100-V-0032.bin"
private noncomputable def vp00100_33 : Blocks := edgeBlocks% "full/vectors/00100-V-0033.bin"
private noncomputable def vp00100_34 : Blocks := edgeBlocks% "full/vectors/00100-V-0034.bin"
private noncomputable def vp00100_35 : Blocks := edgeBlocks% "full/vectors/00100-V-0035.bin"
private noncomputable def vp00100_36 : Blocks := edgeBlocks% "full/vectors/00100-V-0036.bin"
private noncomputable def vp00100_37 : Blocks := edgeBlocks% "full/vectors/00100-V-0037.bin"
private noncomputable def vp00100_38 : Blocks := edgeBlocks% "full/vectors/00100-V-0038.bin"
private noncomputable def vp00100_39 : Blocks := edgeBlocks% "full/vectors/00100-V-0039.bin"
private noncomputable def vp00100_40 : Blocks := edgeBlocks% "full/vectors/00100-V-0040.bin"
private noncomputable def vp00100_41 : Blocks := edgeBlocks% "full/vectors/00100-V-0041.bin"
private noncomputable def vp00100_42 : Blocks := edgeBlocks% "full/vectors/00100-V-0042.bin"
private noncomputable def vp00100_43 : Blocks := edgeBlocks% "full/vectors/00100-V-0043.bin"
private noncomputable def vp00100_44 : Blocks := edgeBlocks% "full/vectors/00100-V-0044.bin"
private noncomputable def vp00100_45 : Blocks := edgeBlocks% "full/vectors/00100-V-0045.bin"
private noncomputable def vp00100_46 : Blocks := edgeBlocks% "full/vectors/00100-V-0046.bin"
private noncomputable def vp00100_47 : Blocks := edgeBlocks% "full/vectors/00100-V-0047.bin"
private noncomputable def vp00100_48 : Blocks := edgeBlocks% "full/vectors/00100-V-0048.bin"
private noncomputable def vp00100_49 : Blocks := edgeBlocks% "full/vectors/00100-V-0049.bin"
private noncomputable def vp00100_50 : Blocks := edgeBlocks% "full/vectors/00100-V-0050.bin"
private noncomputable def vp00100_51 : Blocks := edgeBlocks% "full/vectors/00100-V-0051.bin"
private noncomputable def vp00100_52 : Blocks := edgeBlocks% "full/vectors/00100-V-0052.bin"
private noncomputable def vp00100_53 : Blocks := edgeBlocks% "full/vectors/00100-V-0053.bin"
private noncomputable def vp00100_54 : Blocks := edgeBlocks% "full/vectors/00100-V-0054.bin"
noncomputable def vp00100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00100_0 (Blocks.join vp00100_1 vp00100_2)) (Blocks.join vp00100_3 (Blocks.join vp00100_4 vp00100_5))) (Blocks.join (Blocks.join vp00100_6 (Blocks.join vp00100_7 vp00100_8)) (Blocks.join (Blocks.join vp00100_9 vp00100_10) (Blocks.join vp00100_11 vp00100_12)))) (Blocks.join (Blocks.join (Blocks.join vp00100_13 (Blocks.join vp00100_14 vp00100_15)) (Blocks.join (Blocks.join vp00100_16 vp00100_17) (Blocks.join vp00100_18 vp00100_19))) (Blocks.join (Blocks.join vp00100_20 (Blocks.join vp00100_21 vp00100_22)) (Blocks.join (Blocks.join vp00100_23 vp00100_24) (Blocks.join vp00100_25 vp00100_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00100_27 (Blocks.join vp00100_28 vp00100_29)) (Blocks.join (Blocks.join vp00100_30 vp00100_31) (Blocks.join vp00100_32 vp00100_33))) (Blocks.join (Blocks.join vp00100_34 (Blocks.join vp00100_35 vp00100_36)) (Blocks.join (Blocks.join vp00100_37 vp00100_38) (Blocks.join vp00100_39 vp00100_40)))) (Blocks.join (Blocks.join (Blocks.join vp00100_41 (Blocks.join vp00100_42 vp00100_43)) (Blocks.join (Blocks.join vp00100_44 vp00100_45) (Blocks.join vp00100_46 vp00100_47))) (Blocks.join (Blocks.join vp00100_48 (Blocks.join vp00100_49 vp00100_50)) (Blocks.join (Blocks.join vp00100_51 vp00100_52) (Blocks.join vp00100_53 vp00100_54))))))
private theorem bp001000 : Branch 0 (-1023761639/256000000 : ℚ) vp00100 := by
  apply branch_left_normalized (c:=vp001000) (k:=0) (m:=3718) (by decide +kernel)
  rw [show 2*(-1023761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/128000000 : ℚ) by norm_num]
  exact coverp001000
private noncomputable def ep001001_0 : Blocks := edgeBlocks% "full/vectors/001001-E-0000.bin"
private noncomputable def ep001001_1 : Blocks := edgeBlocks% "full/vectors/001001-E-0001.bin"
private noncomputable def ep001001_2 : Blocks := edgeBlocks% "full/vectors/001001-E-0002.bin"
private noncomputable def ep001001_3 : Blocks := edgeBlocks% "full/vectors/001001-E-0003.bin"
private noncomputable def ep001001_4 : Blocks := edgeBlocks% "full/vectors/001001-E-0004.bin"
private noncomputable def ep001001_5 : Blocks := edgeBlocks% "full/vectors/001001-E-0005.bin"
private noncomputable def ep001001_6 : Blocks := edgeBlocks% "full/vectors/001001-E-0006.bin"
private noncomputable def ep001001_7 : Blocks := edgeBlocks% "full/vectors/001001-E-0007.bin"
private noncomputable def ep001001_8 : Blocks := edgeBlocks% "full/vectors/001001-E-0008.bin"
private noncomputable def ep001001_9 : Blocks := edgeBlocks% "full/vectors/001001-E-0009.bin"
private noncomputable def ep001001_10 : Blocks := edgeBlocks% "full/vectors/001001-E-0010.bin"
private noncomputable def ep001001_11 : Blocks := edgeBlocks% "full/vectors/001001-E-0011.bin"
private noncomputable def ep001001_12 : Blocks := edgeBlocks% "full/vectors/001001-E-0012.bin"
private noncomputable def ep001001_13 : Blocks := edgeBlocks% "full/vectors/001001-E-0013.bin"
private noncomputable def ep001001_14 : Blocks := edgeBlocks% "full/vectors/001001-E-0014.bin"
private noncomputable def ep001001_15 : Blocks := edgeBlocks% "full/vectors/001001-E-0015.bin"
private noncomputable def ep001001_16 : Blocks := edgeBlocks% "full/vectors/001001-E-0016.bin"
private noncomputable def ep001001_17 : Blocks := edgeBlocks% "full/vectors/001001-E-0017.bin"
private noncomputable def ep001001_18 : Blocks := edgeBlocks% "full/vectors/001001-E-0018.bin"
private noncomputable def ep001001_19 : Blocks := edgeBlocks% "full/vectors/001001-E-0019.bin"
private noncomputable def ep001001_20 : Blocks := edgeBlocks% "full/vectors/001001-E-0020.bin"
private noncomputable def ep001001_21 : Blocks := edgeBlocks% "full/vectors/001001-E-0021.bin"
private noncomputable def ep001001_22 : Blocks := edgeBlocks% "full/vectors/001001-E-0022.bin"
private noncomputable def ep001001_23 : Blocks := edgeBlocks% "full/vectors/001001-E-0023.bin"
private noncomputable def ep001001_24 : Blocks := edgeBlocks% "full/vectors/001001-E-0024.bin"
private noncomputable def ep001001_25 : Blocks := edgeBlocks% "full/vectors/001001-E-0025.bin"
private noncomputable def ep001001_26 : Blocks := edgeBlocks% "full/vectors/001001-E-0026.bin"
private noncomputable def ep001001_27 : Blocks := edgeBlocks% "full/vectors/001001-E-0027.bin"
private noncomputable def ep001001_28 : Blocks := edgeBlocks% "full/vectors/001001-E-0028.bin"
private noncomputable def ep001001_29 : Blocks := edgeBlocks% "full/vectors/001001-E-0029.bin"
private noncomputable def ep001001_30 : Blocks := edgeBlocks% "full/vectors/001001-E-0030.bin"
private noncomputable def ep001001_31 : Blocks := edgeBlocks% "full/vectors/001001-E-0031.bin"
private noncomputable def ep001001_32 : Blocks := edgeBlocks% "full/vectors/001001-E-0032.bin"
private noncomputable def ep001001_33 : Blocks := edgeBlocks% "full/vectors/001001-E-0033.bin"
private noncomputable def ep001001_34 : Blocks := edgeBlocks% "full/vectors/001001-E-0034.bin"
private noncomputable def ep001001_35 : Blocks := edgeBlocks% "full/vectors/001001-E-0035.bin"
private noncomputable def ep001001_36 : Blocks := edgeBlocks% "full/vectors/001001-E-0036.bin"
private noncomputable def ep001001_37 : Blocks := edgeBlocks% "full/vectors/001001-E-0037.bin"
private noncomputable def ep001001_38 : Blocks := edgeBlocks% "full/vectors/001001-E-0038.bin"
private noncomputable def ep001001_39 : Blocks := edgeBlocks% "full/vectors/001001-E-0039.bin"
private noncomputable def ep001001_40 : Blocks := edgeBlocks% "full/vectors/001001-E-0040.bin"
private noncomputable def ep001001_41 : Blocks := edgeBlocks% "full/vectors/001001-E-0041.bin"
private noncomputable def ep001001_42 : Blocks := edgeBlocks% "full/vectors/001001-E-0042.bin"
private noncomputable def ep001001_43 : Blocks := edgeBlocks% "full/vectors/001001-E-0043.bin"
private noncomputable def ep001001_44 : Blocks := edgeBlocks% "full/vectors/001001-E-0044.bin"
private noncomputable def ep001001_45 : Blocks := edgeBlocks% "full/vectors/001001-E-0045.bin"
private noncomputable def ep001001_46 : Blocks := edgeBlocks% "full/vectors/001001-E-0046.bin"
private noncomputable def ep001001_47 : Blocks := edgeBlocks% "full/vectors/001001-E-0047.bin"
private noncomputable def ep001001_48 : Blocks := edgeBlocks% "full/vectors/001001-E-0048.bin"
private noncomputable def ep001001_49 : Blocks := edgeBlocks% "full/vectors/001001-E-0049.bin"
private noncomputable def ep001001_50 : Blocks := edgeBlocks% "full/vectors/001001-E-0050.bin"
private noncomputable def ep001001_51 : Blocks := edgeBlocks% "full/vectors/001001-E-0051.bin"
private noncomputable def ep001001_52 : Blocks := edgeBlocks% "full/vectors/001001-E-0052.bin"
private noncomputable def ep001001_53 : Blocks := edgeBlocks% "full/vectors/001001-E-0053.bin"
private noncomputable def ep001001_54 : Blocks := edgeBlocks% "full/vectors/001001-E-0054.bin"
noncomputable def ep001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001001_0 (Blocks.join ep001001_1 ep001001_2)) (Blocks.join ep001001_3 (Blocks.join ep001001_4 ep001001_5))) (Blocks.join (Blocks.join ep001001_6 (Blocks.join ep001001_7 ep001001_8)) (Blocks.join (Blocks.join ep001001_9 ep001001_10) (Blocks.join ep001001_11 ep001001_12)))) (Blocks.join (Blocks.join (Blocks.join ep001001_13 (Blocks.join ep001001_14 ep001001_15)) (Blocks.join (Blocks.join ep001001_16 ep001001_17) (Blocks.join ep001001_18 ep001001_19))) (Blocks.join (Blocks.join ep001001_20 (Blocks.join ep001001_21 ep001001_22)) (Blocks.join (Blocks.join ep001001_23 ep001001_24) (Blocks.join ep001001_25 ep001001_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001001_27 (Blocks.join ep001001_28 ep001001_29)) (Blocks.join (Blocks.join ep001001_30 ep001001_31) (Blocks.join ep001001_32 ep001001_33))) (Blocks.join (Blocks.join ep001001_34 (Blocks.join ep001001_35 ep001001_36)) (Blocks.join (Blocks.join ep001001_37 ep001001_38) (Blocks.join ep001001_39 ep001001_40)))) (Blocks.join (Blocks.join (Blocks.join ep001001_41 (Blocks.join ep001001_42 ep001001_43)) (Blocks.join (Blocks.join ep001001_44 ep001001_45) (Blocks.join ep001001_46 ep001001_47))) (Blocks.join (Blocks.join ep001001_48 (Blocks.join ep001001_49 ep001001_50)) (Blocks.join (Blocks.join ep001001_51 ep001001_52) (Blocks.join ep001001_53 ep001001_54))))))
private def ptsp001001 : List ℤ := [((2:ℤ)^1724+0),((2:ℤ)^1724+1),((2:ℤ)^1724+2),((2:ℤ)^1724+3),((2:ℤ)^1724+4),((2:ℤ)^1724+5),((2:ℤ)^1724+6)]
private theorem boundp001001 : 2^vp00100.size*absSum vp00100.list + ((2:ℤ)^7699*absSum vp001001.list+absSum ep001001.list) < (2:ℤ)^11053 := by decide +kernel
private theorem pointp001001_0 : fastHom 1 ((2:ℤ)^1724+0) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+0)+ep001001.subst ((2:ℤ)^1724+0) := by decide +kernel
private theorem pointp001001_1 : fastHom 1 ((2:ℤ)^1724+1) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+1)+ep001001.subst ((2:ℤ)^1724+1) := by decide +kernel
private theorem pointp001001_2 : fastHom 1 ((2:ℤ)^1724+2) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+2)+ep001001.subst ((2:ℤ)^1724+2) := by decide +kernel
private theorem pointp001001_3 : fastHom 1 ((2:ℤ)^1724+3) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+3)+ep001001.subst ((2:ℤ)^1724+3) := by decide +kernel
private theorem pointp001001_4 : fastHom 1 ((2:ℤ)^1724+4) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+4)+ep001001.subst ((2:ℤ)^1724+4) := by decide +kernel
private theorem pointp001001_5 : fastHom 1 ((2:ℤ)^1724+5) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+5)+ep001001.subst ((2:ℤ)^1724+5) := by decide +kernel
private theorem pointp001001_6 : fastHom 1 ((2:ℤ)^1724+6) vp00100 = ((2:ℤ)^7699)*vp001001.subst ((2:ℤ)^1724+6)+ep001001.subst ((2:ℤ)^1724+6) := by decide +kernel
private theorem checkp001001 (x:ℤ) (hx:x ∈ ptsp001001) : fastHom 1 x vp00100 = ((2:ℤ)^7699)*vp001001.subst x+ep001001.subst x := by
  simp only [ptsp001001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp001001_0
  · exact pointp001001_1
  · exact pointp001001_2
  · exact pointp001001_3
  · exact pointp001001_4
  · exact pointp001001_5
  · exact pointp001001_6
private theorem idp001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100.list =
    C ((2:ℤ)^7699) * horner X vp001001.list + horner X ep001001.list := by
  apply edge_identity (B := (2:ℤ)^11053) (by decide) (by positivity) (by positivity) boundp001001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp001001 (by decide +kernel)
  · have h : ptsp001001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp001001.trans_le (by decide +kernel)
  · exact checkp001001
private theorem bp001001 : Branch 1 (-1023761639/256000000 : ℚ) vp00100 := by
  apply branch_checked idp001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-1151761639/128000000 : ℚ) by norm_num]
  exact coverp001001
theorem coverp00100 : Covers (-1023761639/256000000 : ℚ) vp00100 := join_branches bp001000 bp001001
end NextProof.EdgeFull

