import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00092
import NextProof.EdgeFull00094

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00101_0 : Blocks := edgeBlocks% "full/vectors/00101-V-0000.bin"
private noncomputable def vp00101_1 : Blocks := edgeBlocks% "full/vectors/00101-V-0001.bin"
private noncomputable def vp00101_2 : Blocks := edgeBlocks% "full/vectors/00101-V-0002.bin"
private noncomputable def vp00101_3 : Blocks := edgeBlocks% "full/vectors/00101-V-0003.bin"
private noncomputable def vp00101_4 : Blocks := edgeBlocks% "full/vectors/00101-V-0004.bin"
private noncomputable def vp00101_5 : Blocks := edgeBlocks% "full/vectors/00101-V-0005.bin"
private noncomputable def vp00101_6 : Blocks := edgeBlocks% "full/vectors/00101-V-0006.bin"
private noncomputable def vp00101_7 : Blocks := edgeBlocks% "full/vectors/00101-V-0007.bin"
private noncomputable def vp00101_8 : Blocks := edgeBlocks% "full/vectors/00101-V-0008.bin"
private noncomputable def vp00101_9 : Blocks := edgeBlocks% "full/vectors/00101-V-0009.bin"
private noncomputable def vp00101_10 : Blocks := edgeBlocks% "full/vectors/00101-V-0010.bin"
private noncomputable def vp00101_11 : Blocks := edgeBlocks% "full/vectors/00101-V-0011.bin"
private noncomputable def vp00101_12 : Blocks := edgeBlocks% "full/vectors/00101-V-0012.bin"
private noncomputable def vp00101_13 : Blocks := edgeBlocks% "full/vectors/00101-V-0013.bin"
private noncomputable def vp00101_14 : Blocks := edgeBlocks% "full/vectors/00101-V-0014.bin"
private noncomputable def vp00101_15 : Blocks := edgeBlocks% "full/vectors/00101-V-0015.bin"
private noncomputable def vp00101_16 : Blocks := edgeBlocks% "full/vectors/00101-V-0016.bin"
private noncomputable def vp00101_17 : Blocks := edgeBlocks% "full/vectors/00101-V-0017.bin"
private noncomputable def vp00101_18 : Blocks := edgeBlocks% "full/vectors/00101-V-0018.bin"
private noncomputable def vp00101_19 : Blocks := edgeBlocks% "full/vectors/00101-V-0019.bin"
private noncomputable def vp00101_20 : Blocks := edgeBlocks% "full/vectors/00101-V-0020.bin"
private noncomputable def vp00101_21 : Blocks := edgeBlocks% "full/vectors/00101-V-0021.bin"
private noncomputable def vp00101_22 : Blocks := edgeBlocks% "full/vectors/00101-V-0022.bin"
private noncomputable def vp00101_23 : Blocks := edgeBlocks% "full/vectors/00101-V-0023.bin"
private noncomputable def vp00101_24 : Blocks := edgeBlocks% "full/vectors/00101-V-0024.bin"
private noncomputable def vp00101_25 : Blocks := edgeBlocks% "full/vectors/00101-V-0025.bin"
private noncomputable def vp00101_26 : Blocks := edgeBlocks% "full/vectors/00101-V-0026.bin"
private noncomputable def vp00101_27 : Blocks := edgeBlocks% "full/vectors/00101-V-0027.bin"
private noncomputable def vp00101_28 : Blocks := edgeBlocks% "full/vectors/00101-V-0028.bin"
private noncomputable def vp00101_29 : Blocks := edgeBlocks% "full/vectors/00101-V-0029.bin"
private noncomputable def vp00101_30 : Blocks := edgeBlocks% "full/vectors/00101-V-0030.bin"
private noncomputable def vp00101_31 : Blocks := edgeBlocks% "full/vectors/00101-V-0031.bin"
private noncomputable def vp00101_32 : Blocks := edgeBlocks% "full/vectors/00101-V-0032.bin"
private noncomputable def vp00101_33 : Blocks := edgeBlocks% "full/vectors/00101-V-0033.bin"
private noncomputable def vp00101_34 : Blocks := edgeBlocks% "full/vectors/00101-V-0034.bin"
private noncomputable def vp00101_35 : Blocks := edgeBlocks% "full/vectors/00101-V-0035.bin"
private noncomputable def vp00101_36 : Blocks := edgeBlocks% "full/vectors/00101-V-0036.bin"
private noncomputable def vp00101_37 : Blocks := edgeBlocks% "full/vectors/00101-V-0037.bin"
private noncomputable def vp00101_38 : Blocks := edgeBlocks% "full/vectors/00101-V-0038.bin"
private noncomputable def vp00101_39 : Blocks := edgeBlocks% "full/vectors/00101-V-0039.bin"
private noncomputable def vp00101_40 : Blocks := edgeBlocks% "full/vectors/00101-V-0040.bin"
private noncomputable def vp00101_41 : Blocks := edgeBlocks% "full/vectors/00101-V-0041.bin"
private noncomputable def vp00101_42 : Blocks := edgeBlocks% "full/vectors/00101-V-0042.bin"
private noncomputable def vp00101_43 : Blocks := edgeBlocks% "full/vectors/00101-V-0043.bin"
private noncomputable def vp00101_44 : Blocks := edgeBlocks% "full/vectors/00101-V-0044.bin"
private noncomputable def vp00101_45 : Blocks := edgeBlocks% "full/vectors/00101-V-0045.bin"
private noncomputable def vp00101_46 : Blocks := edgeBlocks% "full/vectors/00101-V-0046.bin"
private noncomputable def vp00101_47 : Blocks := edgeBlocks% "full/vectors/00101-V-0047.bin"
private noncomputable def vp00101_48 : Blocks := edgeBlocks% "full/vectors/00101-V-0048.bin"
private noncomputable def vp00101_49 : Blocks := edgeBlocks% "full/vectors/00101-V-0049.bin"
noncomputable def vp00101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00101_0 (Blocks.join vp00101_1 vp00101_2)) (Blocks.join vp00101_3 (Blocks.join vp00101_4 vp00101_5))) (Blocks.join (Blocks.join vp00101_6 (Blocks.join vp00101_7 vp00101_8)) (Blocks.join vp00101_9 (Blocks.join vp00101_10 vp00101_11)))) (Blocks.join (Blocks.join (Blocks.join vp00101_12 (Blocks.join vp00101_13 vp00101_14)) (Blocks.join vp00101_15 (Blocks.join vp00101_16 vp00101_17))) (Blocks.join (Blocks.join vp00101_18 (Blocks.join vp00101_19 vp00101_20)) (Blocks.join (Blocks.join vp00101_21 vp00101_22) (Blocks.join vp00101_23 vp00101_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00101_25 (Blocks.join vp00101_26 vp00101_27)) (Blocks.join vp00101_28 (Blocks.join vp00101_29 vp00101_30))) (Blocks.join (Blocks.join vp00101_31 (Blocks.join vp00101_32 vp00101_33)) (Blocks.join vp00101_34 (Blocks.join vp00101_35 vp00101_36)))) (Blocks.join (Blocks.join (Blocks.join vp00101_37 (Blocks.join vp00101_38 vp00101_39)) (Blocks.join vp00101_40 (Blocks.join vp00101_41 vp00101_42))) (Blocks.join (Blocks.join vp00101_43 (Blocks.join vp00101_44 vp00101_45)) (Blocks.join (Blocks.join vp00101_46 vp00101_47) (Blocks.join vp00101_48 vp00101_49))))))
private theorem bp001010 : Branch 0 (-1279761639/256000000 : ℚ) vp00101 := by
  apply branch_left_normalized (c:=vp001010) (k:=0) (m:=3354) (by decide +kernel)
  rw [show 2*(-1279761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-1279761639/128000000 : ℚ) by norm_num]
  exact coverp001010
private noncomputable def ep001011_0 : Blocks := edgeBlocks% "full/vectors/001011-E-0000.bin"
private noncomputable def ep001011_1 : Blocks := edgeBlocks% "full/vectors/001011-E-0001.bin"
private noncomputable def ep001011_2 : Blocks := edgeBlocks% "full/vectors/001011-E-0002.bin"
private noncomputable def ep001011_3 : Blocks := edgeBlocks% "full/vectors/001011-E-0003.bin"
private noncomputable def ep001011_4 : Blocks := edgeBlocks% "full/vectors/001011-E-0004.bin"
private noncomputable def ep001011_5 : Blocks := edgeBlocks% "full/vectors/001011-E-0005.bin"
private noncomputable def ep001011_6 : Blocks := edgeBlocks% "full/vectors/001011-E-0006.bin"
private noncomputable def ep001011_7 : Blocks := edgeBlocks% "full/vectors/001011-E-0007.bin"
private noncomputable def ep001011_8 : Blocks := edgeBlocks% "full/vectors/001011-E-0008.bin"
private noncomputable def ep001011_9 : Blocks := edgeBlocks% "full/vectors/001011-E-0009.bin"
private noncomputable def ep001011_10 : Blocks := edgeBlocks% "full/vectors/001011-E-0010.bin"
private noncomputable def ep001011_11 : Blocks := edgeBlocks% "full/vectors/001011-E-0011.bin"
private noncomputable def ep001011_12 : Blocks := edgeBlocks% "full/vectors/001011-E-0012.bin"
private noncomputable def ep001011_13 : Blocks := edgeBlocks% "full/vectors/001011-E-0013.bin"
private noncomputable def ep001011_14 : Blocks := edgeBlocks% "full/vectors/001011-E-0014.bin"
private noncomputable def ep001011_15 : Blocks := edgeBlocks% "full/vectors/001011-E-0015.bin"
private noncomputable def ep001011_16 : Blocks := edgeBlocks% "full/vectors/001011-E-0016.bin"
private noncomputable def ep001011_17 : Blocks := edgeBlocks% "full/vectors/001011-E-0017.bin"
private noncomputable def ep001011_18 : Blocks := edgeBlocks% "full/vectors/001011-E-0018.bin"
private noncomputable def ep001011_19 : Blocks := edgeBlocks% "full/vectors/001011-E-0019.bin"
private noncomputable def ep001011_20 : Blocks := edgeBlocks% "full/vectors/001011-E-0020.bin"
private noncomputable def ep001011_21 : Blocks := edgeBlocks% "full/vectors/001011-E-0021.bin"
private noncomputable def ep001011_22 : Blocks := edgeBlocks% "full/vectors/001011-E-0022.bin"
private noncomputable def ep001011_23 : Blocks := edgeBlocks% "full/vectors/001011-E-0023.bin"
private noncomputable def ep001011_24 : Blocks := edgeBlocks% "full/vectors/001011-E-0024.bin"
private noncomputable def ep001011_25 : Blocks := edgeBlocks% "full/vectors/001011-E-0025.bin"
private noncomputable def ep001011_26 : Blocks := edgeBlocks% "full/vectors/001011-E-0026.bin"
private noncomputable def ep001011_27 : Blocks := edgeBlocks% "full/vectors/001011-E-0027.bin"
private noncomputable def ep001011_28 : Blocks := edgeBlocks% "full/vectors/001011-E-0028.bin"
private noncomputable def ep001011_29 : Blocks := edgeBlocks% "full/vectors/001011-E-0029.bin"
private noncomputable def ep001011_30 : Blocks := edgeBlocks% "full/vectors/001011-E-0030.bin"
private noncomputable def ep001011_31 : Blocks := edgeBlocks% "full/vectors/001011-E-0031.bin"
private noncomputable def ep001011_32 : Blocks := edgeBlocks% "full/vectors/001011-E-0032.bin"
private noncomputable def ep001011_33 : Blocks := edgeBlocks% "full/vectors/001011-E-0033.bin"
private noncomputable def ep001011_34 : Blocks := edgeBlocks% "full/vectors/001011-E-0034.bin"
private noncomputable def ep001011_35 : Blocks := edgeBlocks% "full/vectors/001011-E-0035.bin"
private noncomputable def ep001011_36 : Blocks := edgeBlocks% "full/vectors/001011-E-0036.bin"
private noncomputable def ep001011_37 : Blocks := edgeBlocks% "full/vectors/001011-E-0037.bin"
private noncomputable def ep001011_38 : Blocks := edgeBlocks% "full/vectors/001011-E-0038.bin"
private noncomputable def ep001011_39 : Blocks := edgeBlocks% "full/vectors/001011-E-0039.bin"
private noncomputable def ep001011_40 : Blocks := edgeBlocks% "full/vectors/001011-E-0040.bin"
private noncomputable def ep001011_41 : Blocks := edgeBlocks% "full/vectors/001011-E-0041.bin"
private noncomputable def ep001011_42 : Blocks := edgeBlocks% "full/vectors/001011-E-0042.bin"
private noncomputable def ep001011_43 : Blocks := edgeBlocks% "full/vectors/001011-E-0043.bin"
private noncomputable def ep001011_44 : Blocks := edgeBlocks% "full/vectors/001011-E-0044.bin"
private noncomputable def ep001011_45 : Blocks := edgeBlocks% "full/vectors/001011-E-0045.bin"
private noncomputable def ep001011_46 : Blocks := edgeBlocks% "full/vectors/001011-E-0046.bin"
private noncomputable def ep001011_47 : Blocks := edgeBlocks% "full/vectors/001011-E-0047.bin"
private noncomputable def ep001011_48 : Blocks := edgeBlocks% "full/vectors/001011-E-0048.bin"
private noncomputable def ep001011_49 : Blocks := edgeBlocks% "full/vectors/001011-E-0049.bin"
noncomputable def ep001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001011_0 (Blocks.join ep001011_1 ep001011_2)) (Blocks.join ep001011_3 (Blocks.join ep001011_4 ep001011_5))) (Blocks.join (Blocks.join ep001011_6 (Blocks.join ep001011_7 ep001011_8)) (Blocks.join ep001011_9 (Blocks.join ep001011_10 ep001011_11)))) (Blocks.join (Blocks.join (Blocks.join ep001011_12 (Blocks.join ep001011_13 ep001011_14)) (Blocks.join ep001011_15 (Blocks.join ep001011_16 ep001011_17))) (Blocks.join (Blocks.join ep001011_18 (Blocks.join ep001011_19 ep001011_20)) (Blocks.join (Blocks.join ep001011_21 ep001011_22) (Blocks.join ep001011_23 ep001011_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep001011_25 (Blocks.join ep001011_26 ep001011_27)) (Blocks.join ep001011_28 (Blocks.join ep001011_29 ep001011_30))) (Blocks.join (Blocks.join ep001011_31 (Blocks.join ep001011_32 ep001011_33)) (Blocks.join ep001011_34 (Blocks.join ep001011_35 ep001011_36)))) (Blocks.join (Blocks.join (Blocks.join ep001011_37 (Blocks.join ep001011_38 ep001011_39)) (Blocks.join ep001011_40 (Blocks.join ep001011_41 ep001011_42))) (Blocks.join (Blocks.join ep001011_43 (Blocks.join ep001011_44 ep001011_45)) (Blocks.join (Blocks.join ep001011_46 ep001011_47) (Blocks.join ep001011_48 ep001011_49))))))
private def ptsp001011 : List ℤ := [((2:ℤ)^1899+0),((2:ℤ)^1899+1),((2:ℤ)^1899+2),((2:ℤ)^1899+3),((2:ℤ)^1899+4),((2:ℤ)^1899+5)]
private theorem boundp001011 : 2^vp00101.size*absSum vp00101.list + ((2:ℤ)^7058*absSum vp001011.list+absSum ep001011.list) < (2:ℤ)^10014 := by decide +kernel
private theorem pointp001011_0 : fastHom 1 ((2:ℤ)^1899+0) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+0)+ep001011.subst ((2:ℤ)^1899+0) := by decide +kernel
private theorem pointp001011_1 : fastHom 1 ((2:ℤ)^1899+1) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+1)+ep001011.subst ((2:ℤ)^1899+1) := by decide +kernel
private theorem pointp001011_2 : fastHom 1 ((2:ℤ)^1899+2) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+2)+ep001011.subst ((2:ℤ)^1899+2) := by decide +kernel
private theorem pointp001011_3 : fastHom 1 ((2:ℤ)^1899+3) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+3)+ep001011.subst ((2:ℤ)^1899+3) := by decide +kernel
private theorem pointp001011_4 : fastHom 1 ((2:ℤ)^1899+4) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+4)+ep001011.subst ((2:ℤ)^1899+4) := by decide +kernel
private theorem pointp001011_5 : fastHom 1 ((2:ℤ)^1899+5) vp00101 = ((2:ℤ)^7058)*vp001011.subst ((2:ℤ)^1899+5)+ep001011.subst ((2:ℤ)^1899+5) := by decide +kernel
private theorem checkp001011 (x:ℤ) (hx:x ∈ ptsp001011) : fastHom 1 x vp00101 = ((2:ℤ)^7058)*vp001011.subst x+ep001011.subst x := by
  simp only [ptsp001011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp001011_0
  · exact pointp001011_1
  · exact pointp001011_2
  · exact pointp001011_3
  · exact pointp001011_4
  · exact pointp001011_5
private theorem idp001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101.list =
    C ((2:ℤ)^7058) * horner X vp001011.list + horner X ep001011.list := by
  apply edge_identity (B := (2:ℤ)^10014) (by decide) (by positivity) (by positivity) boundp001011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp001011 (by decide +kernel)
  · have h : ptsp001011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp001011.trans_le (by decide +kernel)
  · exact checkp001011
private theorem bp001011 : Branch 1 (-1279761639/256000000 : ℚ) vp00101 := by
  apply branch_checked idp001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1279761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-1407761639/128000000 : ℚ) by norm_num]
  exact coverp001011
theorem coverp00101 : Covers (-1279761639/256000000 : ℚ) vp00101 := join_branches bp001010 bp001011
end NextProof.EdgeFull

