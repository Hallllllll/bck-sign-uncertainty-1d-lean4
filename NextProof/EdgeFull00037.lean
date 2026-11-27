import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00034
import NextProof.EdgeFull00036

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000001_0 : Blocks := edgeBlocks% "full/vectors/0000001-V-0000.bin"
private noncomputable def vp0000001_1 : Blocks := edgeBlocks% "full/vectors/0000001-V-0001.bin"
private noncomputable def vp0000001_2 : Blocks := edgeBlocks% "full/vectors/0000001-V-0002.bin"
private noncomputable def vp0000001_3 : Blocks := edgeBlocks% "full/vectors/0000001-V-0003.bin"
private noncomputable def vp0000001_4 : Blocks := edgeBlocks% "full/vectors/0000001-V-0004.bin"
private noncomputable def vp0000001_5 : Blocks := edgeBlocks% "full/vectors/0000001-V-0005.bin"
private noncomputable def vp0000001_6 : Blocks := edgeBlocks% "full/vectors/0000001-V-0006.bin"
private noncomputable def vp0000001_7 : Blocks := edgeBlocks% "full/vectors/0000001-V-0007.bin"
private noncomputable def vp0000001_8 : Blocks := edgeBlocks% "full/vectors/0000001-V-0008.bin"
private noncomputable def vp0000001_9 : Blocks := edgeBlocks% "full/vectors/0000001-V-0009.bin"
private noncomputable def vp0000001_10 : Blocks := edgeBlocks% "full/vectors/0000001-V-0010.bin"
private noncomputable def vp0000001_11 : Blocks := edgeBlocks% "full/vectors/0000001-V-0011.bin"
private noncomputable def vp0000001_12 : Blocks := edgeBlocks% "full/vectors/0000001-V-0012.bin"
private noncomputable def vp0000001_13 : Blocks := edgeBlocks% "full/vectors/0000001-V-0013.bin"
private noncomputable def vp0000001_14 : Blocks := edgeBlocks% "full/vectors/0000001-V-0014.bin"
private noncomputable def vp0000001_15 : Blocks := edgeBlocks% "full/vectors/0000001-V-0015.bin"
private noncomputable def vp0000001_16 : Blocks := edgeBlocks% "full/vectors/0000001-V-0016.bin"
private noncomputable def vp0000001_17 : Blocks := edgeBlocks% "full/vectors/0000001-V-0017.bin"
private noncomputable def vp0000001_18 : Blocks := edgeBlocks% "full/vectors/0000001-V-0018.bin"
private noncomputable def vp0000001_19 : Blocks := edgeBlocks% "full/vectors/0000001-V-0019.bin"
private noncomputable def vp0000001_20 : Blocks := edgeBlocks% "full/vectors/0000001-V-0020.bin"
private noncomputable def vp0000001_21 : Blocks := edgeBlocks% "full/vectors/0000001-V-0021.bin"
private noncomputable def vp0000001_22 : Blocks := edgeBlocks% "full/vectors/0000001-V-0022.bin"
private noncomputable def vp0000001_23 : Blocks := edgeBlocks% "full/vectors/0000001-V-0023.bin"
private noncomputable def vp0000001_24 : Blocks := edgeBlocks% "full/vectors/0000001-V-0024.bin"
private noncomputable def vp0000001_25 : Blocks := edgeBlocks% "full/vectors/0000001-V-0025.bin"
private noncomputable def vp0000001_26 : Blocks := edgeBlocks% "full/vectors/0000001-V-0026.bin"
private noncomputable def vp0000001_27 : Blocks := edgeBlocks% "full/vectors/0000001-V-0027.bin"
private noncomputable def vp0000001_28 : Blocks := edgeBlocks% "full/vectors/0000001-V-0028.bin"
private noncomputable def vp0000001_29 : Blocks := edgeBlocks% "full/vectors/0000001-V-0029.bin"
private noncomputable def vp0000001_30 : Blocks := edgeBlocks% "full/vectors/0000001-V-0030.bin"
private noncomputable def vp0000001_31 : Blocks := edgeBlocks% "full/vectors/0000001-V-0031.bin"
private noncomputable def vp0000001_32 : Blocks := edgeBlocks% "full/vectors/0000001-V-0032.bin"
private noncomputable def vp0000001_33 : Blocks := edgeBlocks% "full/vectors/0000001-V-0033.bin"
private noncomputable def vp0000001_34 : Blocks := edgeBlocks% "full/vectors/0000001-V-0034.bin"
private noncomputable def vp0000001_35 : Blocks := edgeBlocks% "full/vectors/0000001-V-0035.bin"
private noncomputable def vp0000001_36 : Blocks := edgeBlocks% "full/vectors/0000001-V-0036.bin"
private noncomputable def vp0000001_37 : Blocks := edgeBlocks% "full/vectors/0000001-V-0037.bin"
private noncomputable def vp0000001_38 : Blocks := edgeBlocks% "full/vectors/0000001-V-0038.bin"
private noncomputable def vp0000001_39 : Blocks := edgeBlocks% "full/vectors/0000001-V-0039.bin"
private noncomputable def vp0000001_40 : Blocks := edgeBlocks% "full/vectors/0000001-V-0040.bin"
private noncomputable def vp0000001_41 : Blocks := edgeBlocks% "full/vectors/0000001-V-0041.bin"
private noncomputable def vp0000001_42 : Blocks := edgeBlocks% "full/vectors/0000001-V-0042.bin"
private noncomputable def vp0000001_43 : Blocks := edgeBlocks% "full/vectors/0000001-V-0043.bin"
private noncomputable def vp0000001_44 : Blocks := edgeBlocks% "full/vectors/0000001-V-0044.bin"
private noncomputable def vp0000001_45 : Blocks := edgeBlocks% "full/vectors/0000001-V-0045.bin"
private noncomputable def vp0000001_46 : Blocks := edgeBlocks% "full/vectors/0000001-V-0046.bin"
private noncomputable def vp0000001_47 : Blocks := edgeBlocks% "full/vectors/0000001-V-0047.bin"
private noncomputable def vp0000001_48 : Blocks := edgeBlocks% "full/vectors/0000001-V-0048.bin"
private noncomputable def vp0000001_49 : Blocks := edgeBlocks% "full/vectors/0000001-V-0049.bin"
private noncomputable def vp0000001_50 : Blocks := edgeBlocks% "full/vectors/0000001-V-0050.bin"
noncomputable def vp0000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000001_0 (Blocks.join vp0000001_1 vp0000001_2)) (Blocks.join vp0000001_3 (Blocks.join vp0000001_4 vp0000001_5))) (Blocks.join (Blocks.join vp0000001_6 (Blocks.join vp0000001_7 vp0000001_8)) (Blocks.join vp0000001_9 (Blocks.join vp0000001_10 vp0000001_11)))) (Blocks.join (Blocks.join (Blocks.join vp0000001_12 (Blocks.join vp0000001_13 vp0000001_14)) (Blocks.join vp0000001_15 (Blocks.join vp0000001_16 vp0000001_17))) (Blocks.join (Blocks.join vp0000001_18 (Blocks.join vp0000001_19 vp0000001_20)) (Blocks.join (Blocks.join vp0000001_21 vp0000001_22) (Blocks.join vp0000001_23 vp0000001_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000001_25 (Blocks.join vp0000001_26 vp0000001_27)) (Blocks.join vp0000001_28 (Blocks.join vp0000001_29 vp0000001_30))) (Blocks.join (Blocks.join vp0000001_31 (Blocks.join vp0000001_32 vp0000001_33)) (Blocks.join (Blocks.join vp0000001_34 vp0000001_35) (Blocks.join vp0000001_36 vp0000001_37)))) (Blocks.join (Blocks.join (Blocks.join vp0000001_38 (Blocks.join vp0000001_39 vp0000001_40)) (Blocks.join vp0000001_41 (Blocks.join vp0000001_42 vp0000001_43))) (Blocks.join (Blocks.join vp0000001_44 (Blocks.join vp0000001_45 vp0000001_46)) (Blocks.join (Blocks.join vp0000001_47 vp0000001_48) (Blocks.join vp0000001_49 vp0000001_50))))))
private theorem bp00000010 : Branch 0 (-63761639/64000000 : ℚ) vp0000001 := by
  apply branch_left_normalized (c:=vp00000010) (k:=0) (m:=3715) (by decide +kernel)
  rw [show 2*(-63761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/32000000 : ℚ) by norm_num]
  exact coverp00000010
private noncomputable def ep00000011_0 : Blocks := edgeBlocks% "full/vectors/00000011-E-0000.bin"
private noncomputable def ep00000011_1 : Blocks := edgeBlocks% "full/vectors/00000011-E-0001.bin"
private noncomputable def ep00000011_2 : Blocks := edgeBlocks% "full/vectors/00000011-E-0002.bin"
private noncomputable def ep00000011_3 : Blocks := edgeBlocks% "full/vectors/00000011-E-0003.bin"
private noncomputable def ep00000011_4 : Blocks := edgeBlocks% "full/vectors/00000011-E-0004.bin"
private noncomputable def ep00000011_5 : Blocks := edgeBlocks% "full/vectors/00000011-E-0005.bin"
private noncomputable def ep00000011_6 : Blocks := edgeBlocks% "full/vectors/00000011-E-0006.bin"
private noncomputable def ep00000011_7 : Blocks := edgeBlocks% "full/vectors/00000011-E-0007.bin"
private noncomputable def ep00000011_8 : Blocks := edgeBlocks% "full/vectors/00000011-E-0008.bin"
private noncomputable def ep00000011_9 : Blocks := edgeBlocks% "full/vectors/00000011-E-0009.bin"
private noncomputable def ep00000011_10 : Blocks := edgeBlocks% "full/vectors/00000011-E-0010.bin"
private noncomputable def ep00000011_11 : Blocks := edgeBlocks% "full/vectors/00000011-E-0011.bin"
private noncomputable def ep00000011_12 : Blocks := edgeBlocks% "full/vectors/00000011-E-0012.bin"
private noncomputable def ep00000011_13 : Blocks := edgeBlocks% "full/vectors/00000011-E-0013.bin"
private noncomputable def ep00000011_14 : Blocks := edgeBlocks% "full/vectors/00000011-E-0014.bin"
private noncomputable def ep00000011_15 : Blocks := edgeBlocks% "full/vectors/00000011-E-0015.bin"
private noncomputable def ep00000011_16 : Blocks := edgeBlocks% "full/vectors/00000011-E-0016.bin"
private noncomputable def ep00000011_17 : Blocks := edgeBlocks% "full/vectors/00000011-E-0017.bin"
private noncomputable def ep00000011_18 : Blocks := edgeBlocks% "full/vectors/00000011-E-0018.bin"
private noncomputable def ep00000011_19 : Blocks := edgeBlocks% "full/vectors/00000011-E-0019.bin"
private noncomputable def ep00000011_20 : Blocks := edgeBlocks% "full/vectors/00000011-E-0020.bin"
private noncomputable def ep00000011_21 : Blocks := edgeBlocks% "full/vectors/00000011-E-0021.bin"
private noncomputable def ep00000011_22 : Blocks := edgeBlocks% "full/vectors/00000011-E-0022.bin"
private noncomputable def ep00000011_23 : Blocks := edgeBlocks% "full/vectors/00000011-E-0023.bin"
private noncomputable def ep00000011_24 : Blocks := edgeBlocks% "full/vectors/00000011-E-0024.bin"
private noncomputable def ep00000011_25 : Blocks := edgeBlocks% "full/vectors/00000011-E-0025.bin"
private noncomputable def ep00000011_26 : Blocks := edgeBlocks% "full/vectors/00000011-E-0026.bin"
private noncomputable def ep00000011_27 : Blocks := edgeBlocks% "full/vectors/00000011-E-0027.bin"
private noncomputable def ep00000011_28 : Blocks := edgeBlocks% "full/vectors/00000011-E-0028.bin"
private noncomputable def ep00000011_29 : Blocks := edgeBlocks% "full/vectors/00000011-E-0029.bin"
private noncomputable def ep00000011_30 : Blocks := edgeBlocks% "full/vectors/00000011-E-0030.bin"
private noncomputable def ep00000011_31 : Blocks := edgeBlocks% "full/vectors/00000011-E-0031.bin"
private noncomputable def ep00000011_32 : Blocks := edgeBlocks% "full/vectors/00000011-E-0032.bin"
private noncomputable def ep00000011_33 : Blocks := edgeBlocks% "full/vectors/00000011-E-0033.bin"
private noncomputable def ep00000011_34 : Blocks := edgeBlocks% "full/vectors/00000011-E-0034.bin"
private noncomputable def ep00000011_35 : Blocks := edgeBlocks% "full/vectors/00000011-E-0035.bin"
private noncomputable def ep00000011_36 : Blocks := edgeBlocks% "full/vectors/00000011-E-0036.bin"
private noncomputable def ep00000011_37 : Blocks := edgeBlocks% "full/vectors/00000011-E-0037.bin"
private noncomputable def ep00000011_38 : Blocks := edgeBlocks% "full/vectors/00000011-E-0038.bin"
private noncomputable def ep00000011_39 : Blocks := edgeBlocks% "full/vectors/00000011-E-0039.bin"
private noncomputable def ep00000011_40 : Blocks := edgeBlocks% "full/vectors/00000011-E-0040.bin"
private noncomputable def ep00000011_41 : Blocks := edgeBlocks% "full/vectors/00000011-E-0041.bin"
private noncomputable def ep00000011_42 : Blocks := edgeBlocks% "full/vectors/00000011-E-0042.bin"
private noncomputable def ep00000011_43 : Blocks := edgeBlocks% "full/vectors/00000011-E-0043.bin"
private noncomputable def ep00000011_44 : Blocks := edgeBlocks% "full/vectors/00000011-E-0044.bin"
private noncomputable def ep00000011_45 : Blocks := edgeBlocks% "full/vectors/00000011-E-0045.bin"
private noncomputable def ep00000011_46 : Blocks := edgeBlocks% "full/vectors/00000011-E-0046.bin"
private noncomputable def ep00000011_47 : Blocks := edgeBlocks% "full/vectors/00000011-E-0047.bin"
private noncomputable def ep00000011_48 : Blocks := edgeBlocks% "full/vectors/00000011-E-0048.bin"
private noncomputable def ep00000011_49 : Blocks := edgeBlocks% "full/vectors/00000011-E-0049.bin"
private noncomputable def ep00000011_50 : Blocks := edgeBlocks% "full/vectors/00000011-E-0050.bin"
noncomputable def ep00000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000011_0 (Blocks.join ep00000011_1 ep00000011_2)) (Blocks.join ep00000011_3 (Blocks.join ep00000011_4 ep00000011_5))) (Blocks.join (Blocks.join ep00000011_6 (Blocks.join ep00000011_7 ep00000011_8)) (Blocks.join ep00000011_9 (Blocks.join ep00000011_10 ep00000011_11)))) (Blocks.join (Blocks.join (Blocks.join ep00000011_12 (Blocks.join ep00000011_13 ep00000011_14)) (Blocks.join ep00000011_15 (Blocks.join ep00000011_16 ep00000011_17))) (Blocks.join (Blocks.join ep00000011_18 (Blocks.join ep00000011_19 ep00000011_20)) (Blocks.join (Blocks.join ep00000011_21 ep00000011_22) (Blocks.join ep00000011_23 ep00000011_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000011_25 (Blocks.join ep00000011_26 ep00000011_27)) (Blocks.join ep00000011_28 (Blocks.join ep00000011_29 ep00000011_30))) (Blocks.join (Blocks.join ep00000011_31 (Blocks.join ep00000011_32 ep00000011_33)) (Blocks.join (Blocks.join ep00000011_34 ep00000011_35) (Blocks.join ep00000011_36 ep00000011_37)))) (Blocks.join (Blocks.join (Blocks.join ep00000011_38 (Blocks.join ep00000011_39 ep00000011_40)) (Blocks.join ep00000011_41 (Blocks.join ep00000011_42 ep00000011_43))) (Blocks.join (Blocks.join ep00000011_44 (Blocks.join ep00000011_45 ep00000011_46)) (Blocks.join (Blocks.join ep00000011_47 ep00000011_48) (Blocks.join ep00000011_49 ep00000011_50))))))
private def ptsp00000011 : List ℤ := [((2:ℤ)^1867+0),((2:ℤ)^1867+1),((2:ℤ)^1867+2),((2:ℤ)^1867+3),((2:ℤ)^1867+4),((2:ℤ)^1867+5)]
private theorem boundp00000011 : 2^vp0000001.size*absSum vp0000001.list + ((2:ℤ)^6609*absSum vp00000011.list+absSum ep00000011.list) < (2:ℤ)^10514 := by decide +kernel
private theorem pointp00000011_0 : fastHom 1 ((2:ℤ)^1867+0) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+0)+ep00000011.subst ((2:ℤ)^1867+0) := by decide +kernel
private theorem pointp00000011_1 : fastHom 1 ((2:ℤ)^1867+1) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+1)+ep00000011.subst ((2:ℤ)^1867+1) := by decide +kernel
private theorem pointp00000011_2 : fastHom 1 ((2:ℤ)^1867+2) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+2)+ep00000011.subst ((2:ℤ)^1867+2) := by decide +kernel
private theorem pointp00000011_3 : fastHom 1 ((2:ℤ)^1867+3) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+3)+ep00000011.subst ((2:ℤ)^1867+3) := by decide +kernel
private theorem pointp00000011_4 : fastHom 1 ((2:ℤ)^1867+4) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+4)+ep00000011.subst ((2:ℤ)^1867+4) := by decide +kernel
private theorem pointp00000011_5 : fastHom 1 ((2:ℤ)^1867+5) vp0000001 = ((2:ℤ)^6609)*vp00000011.subst ((2:ℤ)^1867+5)+ep00000011.subst ((2:ℤ)^1867+5) := by decide +kernel
private theorem checkp00000011 (x:ℤ) (hx:x ∈ ptsp00000011) : fastHom 1 x vp0000001 = ((2:ℤ)^6609)*vp00000011.subst x+ep00000011.subst x := by
  simp only [ptsp00000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp00000011_0
  · exact pointp00000011_1
  · exact pointp00000011_2
  · exact pointp00000011_3
  · exact pointp00000011_4
  · exact pointp00000011_5
private theorem idp00000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001.list =
    C ((2:ℤ)^6609) * horner X vp00000011.list + horner X ep00000011.list := by
  apply edge_identity (B := (2:ℤ)^10514) (by decide) (by positivity) (by positivity) boundp00000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00000011 (by decide +kernel)
  · have h : ptsp00000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00000011.trans_le (by decide +kernel)
  · exact checkp00000011
private theorem bp00000011 : Branch 1 (-63761639/64000000 : ℚ) vp0000001 := by
  apply branch_checked idp00000011 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-95761639/32000000 : ℚ) by norm_num]
  exact coverp00000011
theorem coverp0000001 : Covers (-63761639/64000000 : ℚ) vp0000001 := join_branches bp00000010 bp00000011
end NextProof.EdgeFull

