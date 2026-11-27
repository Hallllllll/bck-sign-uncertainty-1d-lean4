import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00053
import NextProof.EdgeFull00056

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000010_0 : Blocks := edgeBlocks% "full/vectors/000010-V-0000.bin"
private noncomputable def vp000010_1 : Blocks := edgeBlocks% "full/vectors/000010-V-0001.bin"
private noncomputable def vp000010_2 : Blocks := edgeBlocks% "full/vectors/000010-V-0002.bin"
private noncomputable def vp000010_3 : Blocks := edgeBlocks% "full/vectors/000010-V-0003.bin"
private noncomputable def vp000010_4 : Blocks := edgeBlocks% "full/vectors/000010-V-0004.bin"
private noncomputable def vp000010_5 : Blocks := edgeBlocks% "full/vectors/000010-V-0005.bin"
private noncomputable def vp000010_6 : Blocks := edgeBlocks% "full/vectors/000010-V-0006.bin"
private noncomputable def vp000010_7 : Blocks := edgeBlocks% "full/vectors/000010-V-0007.bin"
private noncomputable def vp000010_8 : Blocks := edgeBlocks% "full/vectors/000010-V-0008.bin"
private noncomputable def vp000010_9 : Blocks := edgeBlocks% "full/vectors/000010-V-0009.bin"
private noncomputable def vp000010_10 : Blocks := edgeBlocks% "full/vectors/000010-V-0010.bin"
private noncomputable def vp000010_11 : Blocks := edgeBlocks% "full/vectors/000010-V-0011.bin"
private noncomputable def vp000010_12 : Blocks := edgeBlocks% "full/vectors/000010-V-0012.bin"
private noncomputable def vp000010_13 : Blocks := edgeBlocks% "full/vectors/000010-V-0013.bin"
private noncomputable def vp000010_14 : Blocks := edgeBlocks% "full/vectors/000010-V-0014.bin"
private noncomputable def vp000010_15 : Blocks := edgeBlocks% "full/vectors/000010-V-0015.bin"
private noncomputable def vp000010_16 : Blocks := edgeBlocks% "full/vectors/000010-V-0016.bin"
private noncomputable def vp000010_17 : Blocks := edgeBlocks% "full/vectors/000010-V-0017.bin"
private noncomputable def vp000010_18 : Blocks := edgeBlocks% "full/vectors/000010-V-0018.bin"
private noncomputable def vp000010_19 : Blocks := edgeBlocks% "full/vectors/000010-V-0019.bin"
private noncomputable def vp000010_20 : Blocks := edgeBlocks% "full/vectors/000010-V-0020.bin"
private noncomputable def vp000010_21 : Blocks := edgeBlocks% "full/vectors/000010-V-0021.bin"
private noncomputable def vp000010_22 : Blocks := edgeBlocks% "full/vectors/000010-V-0022.bin"
private noncomputable def vp000010_23 : Blocks := edgeBlocks% "full/vectors/000010-V-0023.bin"
private noncomputable def vp000010_24 : Blocks := edgeBlocks% "full/vectors/000010-V-0024.bin"
private noncomputable def vp000010_25 : Blocks := edgeBlocks% "full/vectors/000010-V-0025.bin"
private noncomputable def vp000010_26 : Blocks := edgeBlocks% "full/vectors/000010-V-0026.bin"
private noncomputable def vp000010_27 : Blocks := edgeBlocks% "full/vectors/000010-V-0027.bin"
private noncomputable def vp000010_28 : Blocks := edgeBlocks% "full/vectors/000010-V-0028.bin"
private noncomputable def vp000010_29 : Blocks := edgeBlocks% "full/vectors/000010-V-0029.bin"
private noncomputable def vp000010_30 : Blocks := edgeBlocks% "full/vectors/000010-V-0030.bin"
private noncomputable def vp000010_31 : Blocks := edgeBlocks% "full/vectors/000010-V-0031.bin"
private noncomputable def vp000010_32 : Blocks := edgeBlocks% "full/vectors/000010-V-0032.bin"
private noncomputable def vp000010_33 : Blocks := edgeBlocks% "full/vectors/000010-V-0033.bin"
private noncomputable def vp000010_34 : Blocks := edgeBlocks% "full/vectors/000010-V-0034.bin"
private noncomputable def vp000010_35 : Blocks := edgeBlocks% "full/vectors/000010-V-0035.bin"
private noncomputable def vp000010_36 : Blocks := edgeBlocks% "full/vectors/000010-V-0036.bin"
private noncomputable def vp000010_37 : Blocks := edgeBlocks% "full/vectors/000010-V-0037.bin"
private noncomputable def vp000010_38 : Blocks := edgeBlocks% "full/vectors/000010-V-0038.bin"
private noncomputable def vp000010_39 : Blocks := edgeBlocks% "full/vectors/000010-V-0039.bin"
private noncomputable def vp000010_40 : Blocks := edgeBlocks% "full/vectors/000010-V-0040.bin"
private noncomputable def vp000010_41 : Blocks := edgeBlocks% "full/vectors/000010-V-0041.bin"
private noncomputable def vp000010_42 : Blocks := edgeBlocks% "full/vectors/000010-V-0042.bin"
private noncomputable def vp000010_43 : Blocks := edgeBlocks% "full/vectors/000010-V-0043.bin"
private noncomputable def vp000010_44 : Blocks := edgeBlocks% "full/vectors/000010-V-0044.bin"
private noncomputable def vp000010_45 : Blocks := edgeBlocks% "full/vectors/000010-V-0045.bin"
private noncomputable def vp000010_46 : Blocks := edgeBlocks% "full/vectors/000010-V-0046.bin"
private noncomputable def vp000010_47 : Blocks := edgeBlocks% "full/vectors/000010-V-0047.bin"
private noncomputable def vp000010_48 : Blocks := edgeBlocks% "full/vectors/000010-V-0048.bin"
private noncomputable def vp000010_49 : Blocks := edgeBlocks% "full/vectors/000010-V-0049.bin"
private noncomputable def vp000010_50 : Blocks := edgeBlocks% "full/vectors/000010-V-0050.bin"
private noncomputable def vp000010_51 : Blocks := edgeBlocks% "full/vectors/000010-V-0051.bin"
private noncomputable def vp000010_52 : Blocks := edgeBlocks% "full/vectors/000010-V-0052.bin"
private noncomputable def vp000010_53 : Blocks := edgeBlocks% "full/vectors/000010-V-0053.bin"
private noncomputable def vp000010_54 : Blocks := edgeBlocks% "full/vectors/000010-V-0054.bin"
noncomputable def vp000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000010_0 (Blocks.join vp000010_1 vp000010_2)) (Blocks.join vp000010_3 (Blocks.join vp000010_4 vp000010_5))) (Blocks.join (Blocks.join vp000010_6 (Blocks.join vp000010_7 vp000010_8)) (Blocks.join (Blocks.join vp000010_9 vp000010_10) (Blocks.join vp000010_11 vp000010_12)))) (Blocks.join (Blocks.join (Blocks.join vp000010_13 (Blocks.join vp000010_14 vp000010_15)) (Blocks.join (Blocks.join vp000010_16 vp000010_17) (Blocks.join vp000010_18 vp000010_19))) (Blocks.join (Blocks.join vp000010_20 (Blocks.join vp000010_21 vp000010_22)) (Blocks.join (Blocks.join vp000010_23 vp000010_24) (Blocks.join vp000010_25 vp000010_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000010_27 (Blocks.join vp000010_28 vp000010_29)) (Blocks.join (Blocks.join vp000010_30 vp000010_31) (Blocks.join vp000010_32 vp000010_33))) (Blocks.join (Blocks.join vp000010_34 (Blocks.join vp000010_35 vp000010_36)) (Blocks.join (Blocks.join vp000010_37 vp000010_38) (Blocks.join vp000010_39 vp000010_40)))) (Blocks.join (Blocks.join (Blocks.join vp000010_41 (Blocks.join vp000010_42 vp000010_43)) (Blocks.join (Blocks.join vp000010_44 vp000010_45) (Blocks.join vp000010_46 vp000010_47))) (Blocks.join (Blocks.join vp000010_48 (Blocks.join vp000010_49 vp000010_50)) (Blocks.join (Blocks.join vp000010_51 vp000010_52) (Blocks.join vp000010_53 vp000010_54))))))
private theorem bp0000100 : Branch 0 (-255761639/128000000 : ℚ) vp000010 := by
  apply branch_left_normalized (c:=vp0000100) (k:=0) (m:=3716) (by decide +kernel)
  rw [show 2*(-255761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/64000000 : ℚ) by norm_num]
  exact coverp0000100
private noncomputable def ep0000101_0 : Blocks := edgeBlocks% "full/vectors/0000101-E-0000.bin"
private noncomputable def ep0000101_1 : Blocks := edgeBlocks% "full/vectors/0000101-E-0001.bin"
private noncomputable def ep0000101_2 : Blocks := edgeBlocks% "full/vectors/0000101-E-0002.bin"
private noncomputable def ep0000101_3 : Blocks := edgeBlocks% "full/vectors/0000101-E-0003.bin"
private noncomputable def ep0000101_4 : Blocks := edgeBlocks% "full/vectors/0000101-E-0004.bin"
private noncomputable def ep0000101_5 : Blocks := edgeBlocks% "full/vectors/0000101-E-0005.bin"
private noncomputable def ep0000101_6 : Blocks := edgeBlocks% "full/vectors/0000101-E-0006.bin"
private noncomputable def ep0000101_7 : Blocks := edgeBlocks% "full/vectors/0000101-E-0007.bin"
private noncomputable def ep0000101_8 : Blocks := edgeBlocks% "full/vectors/0000101-E-0008.bin"
private noncomputable def ep0000101_9 : Blocks := edgeBlocks% "full/vectors/0000101-E-0009.bin"
private noncomputable def ep0000101_10 : Blocks := edgeBlocks% "full/vectors/0000101-E-0010.bin"
private noncomputable def ep0000101_11 : Blocks := edgeBlocks% "full/vectors/0000101-E-0011.bin"
private noncomputable def ep0000101_12 : Blocks := edgeBlocks% "full/vectors/0000101-E-0012.bin"
private noncomputable def ep0000101_13 : Blocks := edgeBlocks% "full/vectors/0000101-E-0013.bin"
private noncomputable def ep0000101_14 : Blocks := edgeBlocks% "full/vectors/0000101-E-0014.bin"
private noncomputable def ep0000101_15 : Blocks := edgeBlocks% "full/vectors/0000101-E-0015.bin"
private noncomputable def ep0000101_16 : Blocks := edgeBlocks% "full/vectors/0000101-E-0016.bin"
private noncomputable def ep0000101_17 : Blocks := edgeBlocks% "full/vectors/0000101-E-0017.bin"
private noncomputable def ep0000101_18 : Blocks := edgeBlocks% "full/vectors/0000101-E-0018.bin"
private noncomputable def ep0000101_19 : Blocks := edgeBlocks% "full/vectors/0000101-E-0019.bin"
private noncomputable def ep0000101_20 : Blocks := edgeBlocks% "full/vectors/0000101-E-0020.bin"
private noncomputable def ep0000101_21 : Blocks := edgeBlocks% "full/vectors/0000101-E-0021.bin"
private noncomputable def ep0000101_22 : Blocks := edgeBlocks% "full/vectors/0000101-E-0022.bin"
private noncomputable def ep0000101_23 : Blocks := edgeBlocks% "full/vectors/0000101-E-0023.bin"
private noncomputable def ep0000101_24 : Blocks := edgeBlocks% "full/vectors/0000101-E-0024.bin"
private noncomputable def ep0000101_25 : Blocks := edgeBlocks% "full/vectors/0000101-E-0025.bin"
private noncomputable def ep0000101_26 : Blocks := edgeBlocks% "full/vectors/0000101-E-0026.bin"
private noncomputable def ep0000101_27 : Blocks := edgeBlocks% "full/vectors/0000101-E-0027.bin"
private noncomputable def ep0000101_28 : Blocks := edgeBlocks% "full/vectors/0000101-E-0028.bin"
private noncomputable def ep0000101_29 : Blocks := edgeBlocks% "full/vectors/0000101-E-0029.bin"
private noncomputable def ep0000101_30 : Blocks := edgeBlocks% "full/vectors/0000101-E-0030.bin"
private noncomputable def ep0000101_31 : Blocks := edgeBlocks% "full/vectors/0000101-E-0031.bin"
private noncomputable def ep0000101_32 : Blocks := edgeBlocks% "full/vectors/0000101-E-0032.bin"
private noncomputable def ep0000101_33 : Blocks := edgeBlocks% "full/vectors/0000101-E-0033.bin"
private noncomputable def ep0000101_34 : Blocks := edgeBlocks% "full/vectors/0000101-E-0034.bin"
private noncomputable def ep0000101_35 : Blocks := edgeBlocks% "full/vectors/0000101-E-0035.bin"
private noncomputable def ep0000101_36 : Blocks := edgeBlocks% "full/vectors/0000101-E-0036.bin"
private noncomputable def ep0000101_37 : Blocks := edgeBlocks% "full/vectors/0000101-E-0037.bin"
private noncomputable def ep0000101_38 : Blocks := edgeBlocks% "full/vectors/0000101-E-0038.bin"
private noncomputable def ep0000101_39 : Blocks := edgeBlocks% "full/vectors/0000101-E-0039.bin"
private noncomputable def ep0000101_40 : Blocks := edgeBlocks% "full/vectors/0000101-E-0040.bin"
private noncomputable def ep0000101_41 : Blocks := edgeBlocks% "full/vectors/0000101-E-0041.bin"
private noncomputable def ep0000101_42 : Blocks := edgeBlocks% "full/vectors/0000101-E-0042.bin"
private noncomputable def ep0000101_43 : Blocks := edgeBlocks% "full/vectors/0000101-E-0043.bin"
private noncomputable def ep0000101_44 : Blocks := edgeBlocks% "full/vectors/0000101-E-0044.bin"
private noncomputable def ep0000101_45 : Blocks := edgeBlocks% "full/vectors/0000101-E-0045.bin"
private noncomputable def ep0000101_46 : Blocks := edgeBlocks% "full/vectors/0000101-E-0046.bin"
private noncomputable def ep0000101_47 : Blocks := edgeBlocks% "full/vectors/0000101-E-0047.bin"
private noncomputable def ep0000101_48 : Blocks := edgeBlocks% "full/vectors/0000101-E-0048.bin"
private noncomputable def ep0000101_49 : Blocks := edgeBlocks% "full/vectors/0000101-E-0049.bin"
private noncomputable def ep0000101_50 : Blocks := edgeBlocks% "full/vectors/0000101-E-0050.bin"
private noncomputable def ep0000101_51 : Blocks := edgeBlocks% "full/vectors/0000101-E-0051.bin"
private noncomputable def ep0000101_52 : Blocks := edgeBlocks% "full/vectors/0000101-E-0052.bin"
private noncomputable def ep0000101_53 : Blocks := edgeBlocks% "full/vectors/0000101-E-0053.bin"
private noncomputable def ep0000101_54 : Blocks := edgeBlocks% "full/vectors/0000101-E-0054.bin"
noncomputable def ep0000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000101_0 (Blocks.join ep0000101_1 ep0000101_2)) (Blocks.join ep0000101_3 (Blocks.join ep0000101_4 ep0000101_5))) (Blocks.join (Blocks.join ep0000101_6 (Blocks.join ep0000101_7 ep0000101_8)) (Blocks.join (Blocks.join ep0000101_9 ep0000101_10) (Blocks.join ep0000101_11 ep0000101_12)))) (Blocks.join (Blocks.join (Blocks.join ep0000101_13 (Blocks.join ep0000101_14 ep0000101_15)) (Blocks.join (Blocks.join ep0000101_16 ep0000101_17) (Blocks.join ep0000101_18 ep0000101_19))) (Blocks.join (Blocks.join ep0000101_20 (Blocks.join ep0000101_21 ep0000101_22)) (Blocks.join (Blocks.join ep0000101_23 ep0000101_24) (Blocks.join ep0000101_25 ep0000101_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000101_27 (Blocks.join ep0000101_28 ep0000101_29)) (Blocks.join (Blocks.join ep0000101_30 ep0000101_31) (Blocks.join ep0000101_32 ep0000101_33))) (Blocks.join (Blocks.join ep0000101_34 (Blocks.join ep0000101_35 ep0000101_36)) (Blocks.join (Blocks.join ep0000101_37 ep0000101_38) (Blocks.join ep0000101_39 ep0000101_40)))) (Blocks.join (Blocks.join (Blocks.join ep0000101_41 (Blocks.join ep0000101_42 ep0000101_43)) (Blocks.join (Blocks.join ep0000101_44 ep0000101_45) (Blocks.join ep0000101_46 ep0000101_47))) (Blocks.join (Blocks.join ep0000101_48 (Blocks.join ep0000101_49 ep0000101_50)) (Blocks.join (Blocks.join ep0000101_51 ep0000101_52) (Blocks.join ep0000101_53 ep0000101_54))))))
private def ptsp0000101 : List ℤ := [((2:ℤ)^1724+0),((2:ℤ)^1724+1),((2:ℤ)^1724+2),((2:ℤ)^1724+3),((2:ℤ)^1724+4),((2:ℤ)^1724+5),((2:ℤ)^1724+6)]
private theorem boundp0000101 : 2^vp000010.size*absSum vp000010.list + ((2:ℤ)^7326*absSum vp0000101.list+absSum ep0000101.list) < (2:ℤ)^11049 := by decide +kernel
private theorem pointp0000101_0 : fastHom 1 ((2:ℤ)^1724+0) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+0)+ep0000101.subst ((2:ℤ)^1724+0) := by decide +kernel
private theorem pointp0000101_1 : fastHom 1 ((2:ℤ)^1724+1) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+1)+ep0000101.subst ((2:ℤ)^1724+1) := by decide +kernel
private theorem pointp0000101_2 : fastHom 1 ((2:ℤ)^1724+2) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+2)+ep0000101.subst ((2:ℤ)^1724+2) := by decide +kernel
private theorem pointp0000101_3 : fastHom 1 ((2:ℤ)^1724+3) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+3)+ep0000101.subst ((2:ℤ)^1724+3) := by decide +kernel
private theorem pointp0000101_4 : fastHom 1 ((2:ℤ)^1724+4) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+4)+ep0000101.subst ((2:ℤ)^1724+4) := by decide +kernel
private theorem pointp0000101_5 : fastHom 1 ((2:ℤ)^1724+5) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+5)+ep0000101.subst ((2:ℤ)^1724+5) := by decide +kernel
private theorem pointp0000101_6 : fastHom 1 ((2:ℤ)^1724+6) vp000010 = ((2:ℤ)^7326)*vp0000101.subst ((2:ℤ)^1724+6)+ep0000101.subst ((2:ℤ)^1724+6) := by decide +kernel
private theorem checkp0000101 (x:ℤ) (hx:x ∈ ptsp0000101) : fastHom 1 x vp000010 = ((2:ℤ)^7326)*vp0000101.subst x+ep0000101.subst x := by
  simp only [ptsp0000101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp0000101_0
  · exact pointp0000101_1
  · exact pointp0000101_2
  · exact pointp0000101_3
  · exact pointp0000101_4
  · exact pointp0000101_5
  · exact pointp0000101_6
private theorem idp0000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010.list =
    C ((2:ℤ)^7326) * horner X vp0000101.list + horner X ep0000101.list := by
  apply edge_identity (B := (2:ℤ)^11049) (by decide) (by positivity) (by positivity) boundp0000101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000101 (by decide +kernel)
  · have h : ptsp0000101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000101.trans_le (by decide +kernel)
  · exact checkp0000101
private theorem bp0000101 : Branch 1 (-255761639/128000000 : ℚ) vp000010 := by
  apply branch_checked idp0000101 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-319761639/64000000 : ℚ) by norm_num]
  exact coverp0000101
theorem coverp000010 : Covers (-255761639/128000000 : ℚ) vp000010 := join_branches bp0000100 bp0000101
end NextProof.EdgeFull

