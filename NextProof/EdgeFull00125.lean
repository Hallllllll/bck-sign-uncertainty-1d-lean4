import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00122
import NextProof.EdgeFull00124

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0110_0 : Blocks := edgeBlocks% "full/vectors/0110-V-0000.bin"
private noncomputable def vp0110_1 : Blocks := edgeBlocks% "full/vectors/0110-V-0001.bin"
private noncomputable def vp0110_2 : Blocks := edgeBlocks% "full/vectors/0110-V-0002.bin"
private noncomputable def vp0110_3 : Blocks := edgeBlocks% "full/vectors/0110-V-0003.bin"
private noncomputable def vp0110_4 : Blocks := edgeBlocks% "full/vectors/0110-V-0004.bin"
private noncomputable def vp0110_5 : Blocks := edgeBlocks% "full/vectors/0110-V-0005.bin"
private noncomputable def vp0110_6 : Blocks := edgeBlocks% "full/vectors/0110-V-0006.bin"
private noncomputable def vp0110_7 : Blocks := edgeBlocks% "full/vectors/0110-V-0007.bin"
private noncomputable def vp0110_8 : Blocks := edgeBlocks% "full/vectors/0110-V-0008.bin"
private noncomputable def vp0110_9 : Blocks := edgeBlocks% "full/vectors/0110-V-0009.bin"
private noncomputable def vp0110_10 : Blocks := edgeBlocks% "full/vectors/0110-V-0010.bin"
private noncomputable def vp0110_11 : Blocks := edgeBlocks% "full/vectors/0110-V-0011.bin"
private noncomputable def vp0110_12 : Blocks := edgeBlocks% "full/vectors/0110-V-0012.bin"
private noncomputable def vp0110_13 : Blocks := edgeBlocks% "full/vectors/0110-V-0013.bin"
private noncomputable def vp0110_14 : Blocks := edgeBlocks% "full/vectors/0110-V-0014.bin"
private noncomputable def vp0110_15 : Blocks := edgeBlocks% "full/vectors/0110-V-0015.bin"
private noncomputable def vp0110_16 : Blocks := edgeBlocks% "full/vectors/0110-V-0016.bin"
private noncomputable def vp0110_17 : Blocks := edgeBlocks% "full/vectors/0110-V-0017.bin"
private noncomputable def vp0110_18 : Blocks := edgeBlocks% "full/vectors/0110-V-0018.bin"
private noncomputable def vp0110_19 : Blocks := edgeBlocks% "full/vectors/0110-V-0019.bin"
private noncomputable def vp0110_20 : Blocks := edgeBlocks% "full/vectors/0110-V-0020.bin"
private noncomputable def vp0110_21 : Blocks := edgeBlocks% "full/vectors/0110-V-0021.bin"
private noncomputable def vp0110_22 : Blocks := edgeBlocks% "full/vectors/0110-V-0022.bin"
private noncomputable def vp0110_23 : Blocks := edgeBlocks% "full/vectors/0110-V-0023.bin"
private noncomputable def vp0110_24 : Blocks := edgeBlocks% "full/vectors/0110-V-0024.bin"
private noncomputable def vp0110_25 : Blocks := edgeBlocks% "full/vectors/0110-V-0025.bin"
private noncomputable def vp0110_26 : Blocks := edgeBlocks% "full/vectors/0110-V-0026.bin"
private noncomputable def vp0110_27 : Blocks := edgeBlocks% "full/vectors/0110-V-0027.bin"
private noncomputable def vp0110_28 : Blocks := edgeBlocks% "full/vectors/0110-V-0028.bin"
private noncomputable def vp0110_29 : Blocks := edgeBlocks% "full/vectors/0110-V-0029.bin"
private noncomputable def vp0110_30 : Blocks := edgeBlocks% "full/vectors/0110-V-0030.bin"
private noncomputable def vp0110_31 : Blocks := edgeBlocks% "full/vectors/0110-V-0031.bin"
private noncomputable def vp0110_32 : Blocks := edgeBlocks% "full/vectors/0110-V-0032.bin"
private noncomputable def vp0110_33 : Blocks := edgeBlocks% "full/vectors/0110-V-0033.bin"
private noncomputable def vp0110_34 : Blocks := edgeBlocks% "full/vectors/0110-V-0034.bin"
private noncomputable def vp0110_35 : Blocks := edgeBlocks% "full/vectors/0110-V-0035.bin"
private noncomputable def vp0110_36 : Blocks := edgeBlocks% "full/vectors/0110-V-0036.bin"
private noncomputable def vp0110_37 : Blocks := edgeBlocks% "full/vectors/0110-V-0037.bin"
private noncomputable def vp0110_38 : Blocks := edgeBlocks% "full/vectors/0110-V-0038.bin"
private noncomputable def vp0110_39 : Blocks := edgeBlocks% "full/vectors/0110-V-0039.bin"
private noncomputable def vp0110_40 : Blocks := edgeBlocks% "full/vectors/0110-V-0040.bin"
private noncomputable def vp0110_41 : Blocks := edgeBlocks% "full/vectors/0110-V-0041.bin"
private noncomputable def vp0110_42 : Blocks := edgeBlocks% "full/vectors/0110-V-0042.bin"
private noncomputable def vp0110_43 : Blocks := edgeBlocks% "full/vectors/0110-V-0043.bin"
private noncomputable def vp0110_44 : Blocks := edgeBlocks% "full/vectors/0110-V-0044.bin"
private noncomputable def vp0110_45 : Blocks := edgeBlocks% "full/vectors/0110-V-0045.bin"
private noncomputable def vp0110_46 : Blocks := edgeBlocks% "full/vectors/0110-V-0046.bin"
private noncomputable def vp0110_47 : Blocks := edgeBlocks% "full/vectors/0110-V-0047.bin"
private noncomputable def vp0110_48 : Blocks := edgeBlocks% "full/vectors/0110-V-0048.bin"
private noncomputable def vp0110_49 : Blocks := edgeBlocks% "full/vectors/0110-V-0049.bin"
private noncomputable def vp0110_50 : Blocks := edgeBlocks% "full/vectors/0110-V-0050.bin"
private noncomputable def vp0110_51 : Blocks := edgeBlocks% "full/vectors/0110-V-0051.bin"
private noncomputable def vp0110_52 : Blocks := edgeBlocks% "full/vectors/0110-V-0052.bin"
private noncomputable def vp0110_53 : Blocks := edgeBlocks% "full/vectors/0110-V-0053.bin"
private noncomputable def vp0110_54 : Blocks := edgeBlocks% "full/vectors/0110-V-0054.bin"
private noncomputable def vp0110_55 : Blocks := edgeBlocks% "full/vectors/0110-V-0055.bin"
private noncomputable def vp0110_56 : Blocks := edgeBlocks% "full/vectors/0110-V-0056.bin"
private noncomputable def vp0110_57 : Blocks := edgeBlocks% "full/vectors/0110-V-0057.bin"
private noncomputable def vp0110_58 : Blocks := edgeBlocks% "full/vectors/0110-V-0058.bin"
private noncomputable def vp0110_59 : Blocks := edgeBlocks% "full/vectors/0110-V-0059.bin"
private noncomputable def vp0110_60 : Blocks := edgeBlocks% "full/vectors/0110-V-0060.bin"
private noncomputable def vp0110_61 : Blocks := edgeBlocks% "full/vectors/0110-V-0061.bin"
noncomputable def vp0110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0110_0 (Blocks.join vp0110_1 vp0110_2)) (Blocks.join (Blocks.join vp0110_3 vp0110_4) (Blocks.join vp0110_5 vp0110_6))) (Blocks.join (Blocks.join (Blocks.join vp0110_7 vp0110_8) (Blocks.join vp0110_9 vp0110_10)) (Blocks.join (Blocks.join vp0110_11 vp0110_12) (Blocks.join vp0110_13 vp0110_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0110_15 vp0110_16) (Blocks.join vp0110_17 vp0110_18)) (Blocks.join (Blocks.join vp0110_19 vp0110_20) (Blocks.join vp0110_21 vp0110_22))) (Blocks.join (Blocks.join (Blocks.join vp0110_23 vp0110_24) (Blocks.join vp0110_25 vp0110_26)) (Blocks.join (Blocks.join vp0110_27 vp0110_28) (Blocks.join vp0110_29 vp0110_30))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0110_31 (Blocks.join vp0110_32 vp0110_33)) (Blocks.join (Blocks.join vp0110_34 vp0110_35) (Blocks.join vp0110_36 vp0110_37))) (Blocks.join (Blocks.join (Blocks.join vp0110_38 vp0110_39) (Blocks.join vp0110_40 vp0110_41)) (Blocks.join (Blocks.join vp0110_42 vp0110_43) (Blocks.join vp0110_44 vp0110_45)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0110_46 vp0110_47) (Blocks.join vp0110_48 vp0110_49)) (Blocks.join (Blocks.join vp0110_50 vp0110_51) (Blocks.join vp0110_52 vp0110_53))) (Blocks.join (Blocks.join (Blocks.join vp0110_54 vp0110_55) (Blocks.join vp0110_56 vp0110_57)) (Blocks.join (Blocks.join vp0110_58 vp0110_59) (Blocks.join vp0110_60 vp0110_61))))))
private theorem bp01100 : Branch 0 (-3071761639/512000000 : ℚ) vp0110 := by
  apply branch_left_normalized (c:=vp01100) (k:=0) (m:=4255) (by decide +kernel)
  rw [show 2*(-3071761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/256000000 : ℚ) by norm_num]
  exact coverp01100
private noncomputable def ep01101_0 : Blocks := edgeBlocks% "full/vectors/01101-E-0000.bin"
private noncomputable def ep01101_1 : Blocks := edgeBlocks% "full/vectors/01101-E-0001.bin"
private noncomputable def ep01101_2 : Blocks := edgeBlocks% "full/vectors/01101-E-0002.bin"
private noncomputable def ep01101_3 : Blocks := edgeBlocks% "full/vectors/01101-E-0003.bin"
private noncomputable def ep01101_4 : Blocks := edgeBlocks% "full/vectors/01101-E-0004.bin"
private noncomputable def ep01101_5 : Blocks := edgeBlocks% "full/vectors/01101-E-0005.bin"
private noncomputable def ep01101_6 : Blocks := edgeBlocks% "full/vectors/01101-E-0006.bin"
private noncomputable def ep01101_7 : Blocks := edgeBlocks% "full/vectors/01101-E-0007.bin"
private noncomputable def ep01101_8 : Blocks := edgeBlocks% "full/vectors/01101-E-0008.bin"
private noncomputable def ep01101_9 : Blocks := edgeBlocks% "full/vectors/01101-E-0009.bin"
private noncomputable def ep01101_10 : Blocks := edgeBlocks% "full/vectors/01101-E-0010.bin"
private noncomputable def ep01101_11 : Blocks := edgeBlocks% "full/vectors/01101-E-0011.bin"
private noncomputable def ep01101_12 : Blocks := edgeBlocks% "full/vectors/01101-E-0012.bin"
private noncomputable def ep01101_13 : Blocks := edgeBlocks% "full/vectors/01101-E-0013.bin"
private noncomputable def ep01101_14 : Blocks := edgeBlocks% "full/vectors/01101-E-0014.bin"
private noncomputable def ep01101_15 : Blocks := edgeBlocks% "full/vectors/01101-E-0015.bin"
private noncomputable def ep01101_16 : Blocks := edgeBlocks% "full/vectors/01101-E-0016.bin"
private noncomputable def ep01101_17 : Blocks := edgeBlocks% "full/vectors/01101-E-0017.bin"
private noncomputable def ep01101_18 : Blocks := edgeBlocks% "full/vectors/01101-E-0018.bin"
private noncomputable def ep01101_19 : Blocks := edgeBlocks% "full/vectors/01101-E-0019.bin"
private noncomputable def ep01101_20 : Blocks := edgeBlocks% "full/vectors/01101-E-0020.bin"
private noncomputable def ep01101_21 : Blocks := edgeBlocks% "full/vectors/01101-E-0021.bin"
private noncomputable def ep01101_22 : Blocks := edgeBlocks% "full/vectors/01101-E-0022.bin"
private noncomputable def ep01101_23 : Blocks := edgeBlocks% "full/vectors/01101-E-0023.bin"
private noncomputable def ep01101_24 : Blocks := edgeBlocks% "full/vectors/01101-E-0024.bin"
private noncomputable def ep01101_25 : Blocks := edgeBlocks% "full/vectors/01101-E-0025.bin"
private noncomputable def ep01101_26 : Blocks := edgeBlocks% "full/vectors/01101-E-0026.bin"
private noncomputable def ep01101_27 : Blocks := edgeBlocks% "full/vectors/01101-E-0027.bin"
private noncomputable def ep01101_28 : Blocks := edgeBlocks% "full/vectors/01101-E-0028.bin"
private noncomputable def ep01101_29 : Blocks := edgeBlocks% "full/vectors/01101-E-0029.bin"
private noncomputable def ep01101_30 : Blocks := edgeBlocks% "full/vectors/01101-E-0030.bin"
private noncomputable def ep01101_31 : Blocks := edgeBlocks% "full/vectors/01101-E-0031.bin"
private noncomputable def ep01101_32 : Blocks := edgeBlocks% "full/vectors/01101-E-0032.bin"
private noncomputable def ep01101_33 : Blocks := edgeBlocks% "full/vectors/01101-E-0033.bin"
private noncomputable def ep01101_34 : Blocks := edgeBlocks% "full/vectors/01101-E-0034.bin"
private noncomputable def ep01101_35 : Blocks := edgeBlocks% "full/vectors/01101-E-0035.bin"
private noncomputable def ep01101_36 : Blocks := edgeBlocks% "full/vectors/01101-E-0036.bin"
private noncomputable def ep01101_37 : Blocks := edgeBlocks% "full/vectors/01101-E-0037.bin"
private noncomputable def ep01101_38 : Blocks := edgeBlocks% "full/vectors/01101-E-0038.bin"
private noncomputable def ep01101_39 : Blocks := edgeBlocks% "full/vectors/01101-E-0039.bin"
private noncomputable def ep01101_40 : Blocks := edgeBlocks% "full/vectors/01101-E-0040.bin"
private noncomputable def ep01101_41 : Blocks := edgeBlocks% "full/vectors/01101-E-0041.bin"
private noncomputable def ep01101_42 : Blocks := edgeBlocks% "full/vectors/01101-E-0042.bin"
private noncomputable def ep01101_43 : Blocks := edgeBlocks% "full/vectors/01101-E-0043.bin"
private noncomputable def ep01101_44 : Blocks := edgeBlocks% "full/vectors/01101-E-0044.bin"
private noncomputable def ep01101_45 : Blocks := edgeBlocks% "full/vectors/01101-E-0045.bin"
private noncomputable def ep01101_46 : Blocks := edgeBlocks% "full/vectors/01101-E-0046.bin"
private noncomputable def ep01101_47 : Blocks := edgeBlocks% "full/vectors/01101-E-0047.bin"
private noncomputable def ep01101_48 : Blocks := edgeBlocks% "full/vectors/01101-E-0048.bin"
private noncomputable def ep01101_49 : Blocks := edgeBlocks% "full/vectors/01101-E-0049.bin"
private noncomputable def ep01101_50 : Blocks := edgeBlocks% "full/vectors/01101-E-0050.bin"
private noncomputable def ep01101_51 : Blocks := edgeBlocks% "full/vectors/01101-E-0051.bin"
private noncomputable def ep01101_52 : Blocks := edgeBlocks% "full/vectors/01101-E-0052.bin"
private noncomputable def ep01101_53 : Blocks := edgeBlocks% "full/vectors/01101-E-0053.bin"
private noncomputable def ep01101_54 : Blocks := edgeBlocks% "full/vectors/01101-E-0054.bin"
private noncomputable def ep01101_55 : Blocks := edgeBlocks% "full/vectors/01101-E-0055.bin"
private noncomputable def ep01101_56 : Blocks := edgeBlocks% "full/vectors/01101-E-0056.bin"
private noncomputable def ep01101_57 : Blocks := edgeBlocks% "full/vectors/01101-E-0057.bin"
private noncomputable def ep01101_58 : Blocks := edgeBlocks% "full/vectors/01101-E-0058.bin"
private noncomputable def ep01101_59 : Blocks := edgeBlocks% "full/vectors/01101-E-0059.bin"
private noncomputable def ep01101_60 : Blocks := edgeBlocks% "full/vectors/01101-E-0060.bin"
private noncomputable def ep01101_61 : Blocks := edgeBlocks% "full/vectors/01101-E-0061.bin"
noncomputable def ep01101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01101_0 (Blocks.join ep01101_1 ep01101_2)) (Blocks.join (Blocks.join ep01101_3 ep01101_4) (Blocks.join ep01101_5 ep01101_6))) (Blocks.join (Blocks.join (Blocks.join ep01101_7 ep01101_8) (Blocks.join ep01101_9 ep01101_10)) (Blocks.join (Blocks.join ep01101_11 ep01101_12) (Blocks.join ep01101_13 ep01101_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01101_15 ep01101_16) (Blocks.join ep01101_17 ep01101_18)) (Blocks.join (Blocks.join ep01101_19 ep01101_20) (Blocks.join ep01101_21 ep01101_22))) (Blocks.join (Blocks.join (Blocks.join ep01101_23 ep01101_24) (Blocks.join ep01101_25 ep01101_26)) (Blocks.join (Blocks.join ep01101_27 ep01101_28) (Blocks.join ep01101_29 ep01101_30))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01101_31 (Blocks.join ep01101_32 ep01101_33)) (Blocks.join (Blocks.join ep01101_34 ep01101_35) (Blocks.join ep01101_36 ep01101_37))) (Blocks.join (Blocks.join (Blocks.join ep01101_38 ep01101_39) (Blocks.join ep01101_40 ep01101_41)) (Blocks.join (Blocks.join ep01101_42 ep01101_43) (Blocks.join ep01101_44 ep01101_45)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01101_46 ep01101_47) (Blocks.join ep01101_48 ep01101_49)) (Blocks.join (Blocks.join ep01101_50 ep01101_51) (Blocks.join ep01101_52 ep01101_53))) (Blocks.join (Blocks.join (Blocks.join ep01101_54 ep01101_55) (Blocks.join ep01101_56 ep01101_57)) (Blocks.join (Blocks.join ep01101_58 ep01101_59) (Blocks.join ep01101_60 ep01101_61))))))
private def ptsp01101 : List ℤ := [((2:ℤ)^1523+0),((2:ℤ)^1523+1),((2:ℤ)^1523+2),((2:ℤ)^1523+3),((2:ℤ)^1523+4),((2:ℤ)^1523+5),((2:ℤ)^1523+6),((2:ℤ)^1523+7),((2:ℤ)^1523+8)]
private theorem boundp01101 : 2^vp0110.size*absSum vp0110.list + ((2:ℤ)^9358*absSum vp01101.list+absSum ep01101.list) < (2:ℤ)^12566 := by decide +kernel
private theorem pointp01101_0 : fastHom 1 ((2:ℤ)^1523+0) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+0)+ep01101.subst ((2:ℤ)^1523+0) := by decide +kernel
private theorem pointp01101_1 : fastHom 1 ((2:ℤ)^1523+1) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+1)+ep01101.subst ((2:ℤ)^1523+1) := by decide +kernel
private theorem pointp01101_2 : fastHom 1 ((2:ℤ)^1523+2) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+2)+ep01101.subst ((2:ℤ)^1523+2) := by decide +kernel
private theorem pointp01101_3 : fastHom 1 ((2:ℤ)^1523+3) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+3)+ep01101.subst ((2:ℤ)^1523+3) := by decide +kernel
private theorem pointp01101_4 : fastHom 1 ((2:ℤ)^1523+4) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+4)+ep01101.subst ((2:ℤ)^1523+4) := by decide +kernel
private theorem pointp01101_5 : fastHom 1 ((2:ℤ)^1523+5) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+5)+ep01101.subst ((2:ℤ)^1523+5) := by decide +kernel
private theorem pointp01101_6 : fastHom 1 ((2:ℤ)^1523+6) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+6)+ep01101.subst ((2:ℤ)^1523+6) := by decide +kernel
private theorem pointp01101_7 : fastHom 1 ((2:ℤ)^1523+7) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+7)+ep01101.subst ((2:ℤ)^1523+7) := by decide +kernel
private theorem pointp01101_8 : fastHom 1 ((2:ℤ)^1523+8) vp0110 = ((2:ℤ)^9358)*vp01101.subst ((2:ℤ)^1523+8)+ep01101.subst ((2:ℤ)^1523+8) := by decide +kernel
private theorem checkp01101 (x:ℤ) (hx:x ∈ ptsp01101) : fastHom 1 x vp0110 = ((2:ℤ)^9358)*vp01101.subst x+ep01101.subst x := by
  simp only [ptsp01101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp01101_0
  · exact pointp01101_1
  · exact pointp01101_2
  · exact pointp01101_3
  · exact pointp01101_4
  · exact pointp01101_5
  · exact pointp01101_6
  · exact pointp01101_7
  · exact pointp01101_8
private theorem idp01101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110.list =
    C ((2:ℤ)^9358) * horner X vp01101.list + horner X ep01101.list := by
  apply edge_identity (B := (2:ℤ)^12566) (by decide) (by positivity) (by positivity) boundp01101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp01101 (by decide +kernel)
  · have h : ptsp01101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp01101.trans_le (by decide +kernel)
  · exact checkp01101
private theorem bp01101 : Branch 1 (-3071761639/512000000 : ℚ) vp0110 := by
  apply branch_checked idp01101 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-3327761639/256000000 : ℚ) by norm_num]
  exact coverp01101
theorem coverp0110 : Covers (-3071761639/512000000 : ℚ) vp0110 := join_branches bp01100 bp01101
end NextProof.EdgeFull

