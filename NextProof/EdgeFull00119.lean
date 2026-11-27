import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00116
import NextProof.EdgeFull00118

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0101_0 : Blocks := edgeBlocks% "full/vectors/0101-V-0000.bin"
private noncomputable def vp0101_1 : Blocks := edgeBlocks% "full/vectors/0101-V-0001.bin"
private noncomputable def vp0101_2 : Blocks := edgeBlocks% "full/vectors/0101-V-0002.bin"
private noncomputable def vp0101_3 : Blocks := edgeBlocks% "full/vectors/0101-V-0003.bin"
private noncomputable def vp0101_4 : Blocks := edgeBlocks% "full/vectors/0101-V-0004.bin"
private noncomputable def vp0101_5 : Blocks := edgeBlocks% "full/vectors/0101-V-0005.bin"
private noncomputable def vp0101_6 : Blocks := edgeBlocks% "full/vectors/0101-V-0006.bin"
private noncomputable def vp0101_7 : Blocks := edgeBlocks% "full/vectors/0101-V-0007.bin"
private noncomputable def vp0101_8 : Blocks := edgeBlocks% "full/vectors/0101-V-0008.bin"
private noncomputable def vp0101_9 : Blocks := edgeBlocks% "full/vectors/0101-V-0009.bin"
private noncomputable def vp0101_10 : Blocks := edgeBlocks% "full/vectors/0101-V-0010.bin"
private noncomputable def vp0101_11 : Blocks := edgeBlocks% "full/vectors/0101-V-0011.bin"
private noncomputable def vp0101_12 : Blocks := edgeBlocks% "full/vectors/0101-V-0012.bin"
private noncomputable def vp0101_13 : Blocks := edgeBlocks% "full/vectors/0101-V-0013.bin"
private noncomputable def vp0101_14 : Blocks := edgeBlocks% "full/vectors/0101-V-0014.bin"
private noncomputable def vp0101_15 : Blocks := edgeBlocks% "full/vectors/0101-V-0015.bin"
private noncomputable def vp0101_16 : Blocks := edgeBlocks% "full/vectors/0101-V-0016.bin"
private noncomputable def vp0101_17 : Blocks := edgeBlocks% "full/vectors/0101-V-0017.bin"
private noncomputable def vp0101_18 : Blocks := edgeBlocks% "full/vectors/0101-V-0018.bin"
private noncomputable def vp0101_19 : Blocks := edgeBlocks% "full/vectors/0101-V-0019.bin"
private noncomputable def vp0101_20 : Blocks := edgeBlocks% "full/vectors/0101-V-0020.bin"
private noncomputable def vp0101_21 : Blocks := edgeBlocks% "full/vectors/0101-V-0021.bin"
private noncomputable def vp0101_22 : Blocks := edgeBlocks% "full/vectors/0101-V-0022.bin"
private noncomputable def vp0101_23 : Blocks := edgeBlocks% "full/vectors/0101-V-0023.bin"
private noncomputable def vp0101_24 : Blocks := edgeBlocks% "full/vectors/0101-V-0024.bin"
private noncomputable def vp0101_25 : Blocks := edgeBlocks% "full/vectors/0101-V-0025.bin"
private noncomputable def vp0101_26 : Blocks := edgeBlocks% "full/vectors/0101-V-0026.bin"
private noncomputable def vp0101_27 : Blocks := edgeBlocks% "full/vectors/0101-V-0027.bin"
private noncomputable def vp0101_28 : Blocks := edgeBlocks% "full/vectors/0101-V-0028.bin"
private noncomputable def vp0101_29 : Blocks := edgeBlocks% "full/vectors/0101-V-0029.bin"
private noncomputable def vp0101_30 : Blocks := edgeBlocks% "full/vectors/0101-V-0030.bin"
private noncomputable def vp0101_31 : Blocks := edgeBlocks% "full/vectors/0101-V-0031.bin"
private noncomputable def vp0101_32 : Blocks := edgeBlocks% "full/vectors/0101-V-0032.bin"
private noncomputable def vp0101_33 : Blocks := edgeBlocks% "full/vectors/0101-V-0033.bin"
private noncomputable def vp0101_34 : Blocks := edgeBlocks% "full/vectors/0101-V-0034.bin"
private noncomputable def vp0101_35 : Blocks := edgeBlocks% "full/vectors/0101-V-0035.bin"
private noncomputable def vp0101_36 : Blocks := edgeBlocks% "full/vectors/0101-V-0036.bin"
private noncomputable def vp0101_37 : Blocks := edgeBlocks% "full/vectors/0101-V-0037.bin"
private noncomputable def vp0101_38 : Blocks := edgeBlocks% "full/vectors/0101-V-0038.bin"
private noncomputable def vp0101_39 : Blocks := edgeBlocks% "full/vectors/0101-V-0039.bin"
private noncomputable def vp0101_40 : Blocks := edgeBlocks% "full/vectors/0101-V-0040.bin"
private noncomputable def vp0101_41 : Blocks := edgeBlocks% "full/vectors/0101-V-0041.bin"
private noncomputable def vp0101_42 : Blocks := edgeBlocks% "full/vectors/0101-V-0042.bin"
private noncomputable def vp0101_43 : Blocks := edgeBlocks% "full/vectors/0101-V-0043.bin"
private noncomputable def vp0101_44 : Blocks := edgeBlocks% "full/vectors/0101-V-0044.bin"
private noncomputable def vp0101_45 : Blocks := edgeBlocks% "full/vectors/0101-V-0045.bin"
private noncomputable def vp0101_46 : Blocks := edgeBlocks% "full/vectors/0101-V-0046.bin"
private noncomputable def vp0101_47 : Blocks := edgeBlocks% "full/vectors/0101-V-0047.bin"
private noncomputable def vp0101_48 : Blocks := edgeBlocks% "full/vectors/0101-V-0048.bin"
private noncomputable def vp0101_49 : Blocks := edgeBlocks% "full/vectors/0101-V-0049.bin"
private noncomputable def vp0101_50 : Blocks := edgeBlocks% "full/vectors/0101-V-0050.bin"
private noncomputable def vp0101_51 : Blocks := edgeBlocks% "full/vectors/0101-V-0051.bin"
private noncomputable def vp0101_52 : Blocks := edgeBlocks% "full/vectors/0101-V-0052.bin"
private noncomputable def vp0101_53 : Blocks := edgeBlocks% "full/vectors/0101-V-0053.bin"
private noncomputable def vp0101_54 : Blocks := edgeBlocks% "full/vectors/0101-V-0054.bin"
private noncomputable def vp0101_55 : Blocks := edgeBlocks% "full/vectors/0101-V-0055.bin"
private noncomputable def vp0101_56 : Blocks := edgeBlocks% "full/vectors/0101-V-0056.bin"
private noncomputable def vp0101_57 : Blocks := edgeBlocks% "full/vectors/0101-V-0057.bin"
private noncomputable def vp0101_58 : Blocks := edgeBlocks% "full/vectors/0101-V-0058.bin"
private noncomputable def vp0101_59 : Blocks := edgeBlocks% "full/vectors/0101-V-0059.bin"
private noncomputable def vp0101_60 : Blocks := edgeBlocks% "full/vectors/0101-V-0060.bin"
private noncomputable def vp0101_61 : Blocks := edgeBlocks% "full/vectors/0101-V-0061.bin"
private noncomputable def vp0101_62 : Blocks := edgeBlocks% "full/vectors/0101-V-0062.bin"
private noncomputable def vp0101_63 : Blocks := edgeBlocks% "full/vectors/0101-V-0063.bin"
private noncomputable def vp0101_64 : Blocks := edgeBlocks% "full/vectors/0101-V-0064.bin"
private noncomputable def vp0101_65 : Blocks := edgeBlocks% "full/vectors/0101-V-0065.bin"
private noncomputable def vp0101_66 : Blocks := edgeBlocks% "full/vectors/0101-V-0066.bin"
noncomputable def vp0101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0101_0 vp0101_1) (Blocks.join vp0101_2 vp0101_3)) (Blocks.join (Blocks.join vp0101_4 vp0101_5) (Blocks.join vp0101_6 vp0101_7))) (Blocks.join (Blocks.join (Blocks.join vp0101_8 vp0101_9) (Blocks.join vp0101_10 vp0101_11)) (Blocks.join (Blocks.join vp0101_12 vp0101_13) (Blocks.join vp0101_14 vp0101_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0101_16 vp0101_17) (Blocks.join vp0101_18 vp0101_19)) (Blocks.join (Blocks.join vp0101_20 vp0101_21) (Blocks.join vp0101_22 vp0101_23))) (Blocks.join (Blocks.join (Blocks.join vp0101_24 vp0101_25) (Blocks.join vp0101_26 vp0101_27)) (Blocks.join (Blocks.join vp0101_28 vp0101_29) (Blocks.join vp0101_30 (Blocks.join vp0101_31 vp0101_32)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0101_33 vp0101_34) (Blocks.join vp0101_35 vp0101_36)) (Blocks.join (Blocks.join vp0101_37 vp0101_38) (Blocks.join vp0101_39 vp0101_40))) (Blocks.join (Blocks.join (Blocks.join vp0101_41 vp0101_42) (Blocks.join vp0101_43 vp0101_44)) (Blocks.join (Blocks.join vp0101_45 vp0101_46) (Blocks.join vp0101_47 (Blocks.join vp0101_48 vp0101_49))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0101_50 vp0101_51) (Blocks.join vp0101_52 vp0101_53)) (Blocks.join (Blocks.join vp0101_54 vp0101_55) (Blocks.join vp0101_56 vp0101_57))) (Blocks.join (Blocks.join (Blocks.join vp0101_58 vp0101_59) (Blocks.join vp0101_60 vp0101_61)) (Blocks.join (Blocks.join vp0101_62 vp0101_63) (Blocks.join vp0101_64 (Blocks.join vp0101_65 vp0101_66)))))))
private theorem bp01010 : Branch 0 (-2559761639/512000000 : ℚ) vp0101 := by
  apply branch_left_normalized (c:=vp01010) (k:=0) (m:=4625) (by decide +kernel)
  rw [show 2*(-2559761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/256000000 : ℚ) by norm_num]
  exact coverp01010
private noncomputable def ep01011_0 : Blocks := edgeBlocks% "full/vectors/01011-E-0000.bin"
private noncomputable def ep01011_1 : Blocks := edgeBlocks% "full/vectors/01011-E-0001.bin"
private noncomputable def ep01011_2 : Blocks := edgeBlocks% "full/vectors/01011-E-0002.bin"
private noncomputable def ep01011_3 : Blocks := edgeBlocks% "full/vectors/01011-E-0003.bin"
private noncomputable def ep01011_4 : Blocks := edgeBlocks% "full/vectors/01011-E-0004.bin"
private noncomputable def ep01011_5 : Blocks := edgeBlocks% "full/vectors/01011-E-0005.bin"
private noncomputable def ep01011_6 : Blocks := edgeBlocks% "full/vectors/01011-E-0006.bin"
private noncomputable def ep01011_7 : Blocks := edgeBlocks% "full/vectors/01011-E-0007.bin"
private noncomputable def ep01011_8 : Blocks := edgeBlocks% "full/vectors/01011-E-0008.bin"
private noncomputable def ep01011_9 : Blocks := edgeBlocks% "full/vectors/01011-E-0009.bin"
private noncomputable def ep01011_10 : Blocks := edgeBlocks% "full/vectors/01011-E-0010.bin"
private noncomputable def ep01011_11 : Blocks := edgeBlocks% "full/vectors/01011-E-0011.bin"
private noncomputable def ep01011_12 : Blocks := edgeBlocks% "full/vectors/01011-E-0012.bin"
private noncomputable def ep01011_13 : Blocks := edgeBlocks% "full/vectors/01011-E-0013.bin"
private noncomputable def ep01011_14 : Blocks := edgeBlocks% "full/vectors/01011-E-0014.bin"
private noncomputable def ep01011_15 : Blocks := edgeBlocks% "full/vectors/01011-E-0015.bin"
private noncomputable def ep01011_16 : Blocks := edgeBlocks% "full/vectors/01011-E-0016.bin"
private noncomputable def ep01011_17 : Blocks := edgeBlocks% "full/vectors/01011-E-0017.bin"
private noncomputable def ep01011_18 : Blocks := edgeBlocks% "full/vectors/01011-E-0018.bin"
private noncomputable def ep01011_19 : Blocks := edgeBlocks% "full/vectors/01011-E-0019.bin"
private noncomputable def ep01011_20 : Blocks := edgeBlocks% "full/vectors/01011-E-0020.bin"
private noncomputable def ep01011_21 : Blocks := edgeBlocks% "full/vectors/01011-E-0021.bin"
private noncomputable def ep01011_22 : Blocks := edgeBlocks% "full/vectors/01011-E-0022.bin"
private noncomputable def ep01011_23 : Blocks := edgeBlocks% "full/vectors/01011-E-0023.bin"
private noncomputable def ep01011_24 : Blocks := edgeBlocks% "full/vectors/01011-E-0024.bin"
private noncomputable def ep01011_25 : Blocks := edgeBlocks% "full/vectors/01011-E-0025.bin"
private noncomputable def ep01011_26 : Blocks := edgeBlocks% "full/vectors/01011-E-0026.bin"
private noncomputable def ep01011_27 : Blocks := edgeBlocks% "full/vectors/01011-E-0027.bin"
private noncomputable def ep01011_28 : Blocks := edgeBlocks% "full/vectors/01011-E-0028.bin"
private noncomputable def ep01011_29 : Blocks := edgeBlocks% "full/vectors/01011-E-0029.bin"
private noncomputable def ep01011_30 : Blocks := edgeBlocks% "full/vectors/01011-E-0030.bin"
private noncomputable def ep01011_31 : Blocks := edgeBlocks% "full/vectors/01011-E-0031.bin"
private noncomputable def ep01011_32 : Blocks := edgeBlocks% "full/vectors/01011-E-0032.bin"
private noncomputable def ep01011_33 : Blocks := edgeBlocks% "full/vectors/01011-E-0033.bin"
private noncomputable def ep01011_34 : Blocks := edgeBlocks% "full/vectors/01011-E-0034.bin"
private noncomputable def ep01011_35 : Blocks := edgeBlocks% "full/vectors/01011-E-0035.bin"
private noncomputable def ep01011_36 : Blocks := edgeBlocks% "full/vectors/01011-E-0036.bin"
private noncomputable def ep01011_37 : Blocks := edgeBlocks% "full/vectors/01011-E-0037.bin"
private noncomputable def ep01011_38 : Blocks := edgeBlocks% "full/vectors/01011-E-0038.bin"
private noncomputable def ep01011_39 : Blocks := edgeBlocks% "full/vectors/01011-E-0039.bin"
private noncomputable def ep01011_40 : Blocks := edgeBlocks% "full/vectors/01011-E-0040.bin"
private noncomputable def ep01011_41 : Blocks := edgeBlocks% "full/vectors/01011-E-0041.bin"
private noncomputable def ep01011_42 : Blocks := edgeBlocks% "full/vectors/01011-E-0042.bin"
private noncomputable def ep01011_43 : Blocks := edgeBlocks% "full/vectors/01011-E-0043.bin"
private noncomputable def ep01011_44 : Blocks := edgeBlocks% "full/vectors/01011-E-0044.bin"
private noncomputable def ep01011_45 : Blocks := edgeBlocks% "full/vectors/01011-E-0045.bin"
private noncomputable def ep01011_46 : Blocks := edgeBlocks% "full/vectors/01011-E-0046.bin"
private noncomputable def ep01011_47 : Blocks := edgeBlocks% "full/vectors/01011-E-0047.bin"
private noncomputable def ep01011_48 : Blocks := edgeBlocks% "full/vectors/01011-E-0048.bin"
private noncomputable def ep01011_49 : Blocks := edgeBlocks% "full/vectors/01011-E-0049.bin"
private noncomputable def ep01011_50 : Blocks := edgeBlocks% "full/vectors/01011-E-0050.bin"
private noncomputable def ep01011_51 : Blocks := edgeBlocks% "full/vectors/01011-E-0051.bin"
private noncomputable def ep01011_52 : Blocks := edgeBlocks% "full/vectors/01011-E-0052.bin"
private noncomputable def ep01011_53 : Blocks := edgeBlocks% "full/vectors/01011-E-0053.bin"
private noncomputable def ep01011_54 : Blocks := edgeBlocks% "full/vectors/01011-E-0054.bin"
private noncomputable def ep01011_55 : Blocks := edgeBlocks% "full/vectors/01011-E-0055.bin"
private noncomputable def ep01011_56 : Blocks := edgeBlocks% "full/vectors/01011-E-0056.bin"
private noncomputable def ep01011_57 : Blocks := edgeBlocks% "full/vectors/01011-E-0057.bin"
private noncomputable def ep01011_58 : Blocks := edgeBlocks% "full/vectors/01011-E-0058.bin"
private noncomputable def ep01011_59 : Blocks := edgeBlocks% "full/vectors/01011-E-0059.bin"
private noncomputable def ep01011_60 : Blocks := edgeBlocks% "full/vectors/01011-E-0060.bin"
private noncomputable def ep01011_61 : Blocks := edgeBlocks% "full/vectors/01011-E-0061.bin"
private noncomputable def ep01011_62 : Blocks := edgeBlocks% "full/vectors/01011-E-0062.bin"
private noncomputable def ep01011_63 : Blocks := edgeBlocks% "full/vectors/01011-E-0063.bin"
private noncomputable def ep01011_64 : Blocks := edgeBlocks% "full/vectors/01011-E-0064.bin"
private noncomputable def ep01011_65 : Blocks := edgeBlocks% "full/vectors/01011-E-0065.bin"
private noncomputable def ep01011_66 : Blocks := edgeBlocks% "full/vectors/01011-E-0066.bin"
noncomputable def ep01011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01011_0 ep01011_1) (Blocks.join ep01011_2 ep01011_3)) (Blocks.join (Blocks.join ep01011_4 ep01011_5) (Blocks.join ep01011_6 ep01011_7))) (Blocks.join (Blocks.join (Blocks.join ep01011_8 ep01011_9) (Blocks.join ep01011_10 ep01011_11)) (Blocks.join (Blocks.join ep01011_12 ep01011_13) (Blocks.join ep01011_14 ep01011_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01011_16 ep01011_17) (Blocks.join ep01011_18 ep01011_19)) (Blocks.join (Blocks.join ep01011_20 ep01011_21) (Blocks.join ep01011_22 ep01011_23))) (Blocks.join (Blocks.join (Blocks.join ep01011_24 ep01011_25) (Blocks.join ep01011_26 ep01011_27)) (Blocks.join (Blocks.join ep01011_28 ep01011_29) (Blocks.join ep01011_30 (Blocks.join ep01011_31 ep01011_32)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01011_33 ep01011_34) (Blocks.join ep01011_35 ep01011_36)) (Blocks.join (Blocks.join ep01011_37 ep01011_38) (Blocks.join ep01011_39 ep01011_40))) (Blocks.join (Blocks.join (Blocks.join ep01011_41 ep01011_42) (Blocks.join ep01011_43 ep01011_44)) (Blocks.join (Blocks.join ep01011_45 ep01011_46) (Blocks.join ep01011_47 (Blocks.join ep01011_48 ep01011_49))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01011_50 ep01011_51) (Blocks.join ep01011_52 ep01011_53)) (Blocks.join (Blocks.join ep01011_54 ep01011_55) (Blocks.join ep01011_56 ep01011_57))) (Blocks.join (Blocks.join (Blocks.join ep01011_58 ep01011_59) (Blocks.join ep01011_60 ep01011_61)) (Blocks.join (Blocks.join ep01011_62 ep01011_63) (Blocks.join ep01011_64 (Blocks.join ep01011_65 ep01011_66)))))))
private def ptsp01011 : List ℤ := [((2:ℤ)^1411+0),((2:ℤ)^1411+1),((2:ℤ)^1411+2),((2:ℤ)^1411+3),((2:ℤ)^1411+4),((2:ℤ)^1411+5),((2:ℤ)^1411+6),((2:ℤ)^1411+7),((2:ℤ)^1411+8),((2:ℤ)^1411+9)]
private theorem boundp01011 : 2^vp0101.size*absSum vp0101.list + ((2:ℤ)^9989*absSum vp01011.list+absSum ep01011.list) < (2:ℤ)^13604 := by decide +kernel
private theorem pointp01011_0 : fastHom 1 ((2:ℤ)^1411+0) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+0)+ep01011.subst ((2:ℤ)^1411+0) := by decide +kernel
private theorem pointp01011_1 : fastHom 1 ((2:ℤ)^1411+1) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+1)+ep01011.subst ((2:ℤ)^1411+1) := by decide +kernel
private theorem pointp01011_2 : fastHom 1 ((2:ℤ)^1411+2) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+2)+ep01011.subst ((2:ℤ)^1411+2) := by decide +kernel
private theorem pointp01011_3 : fastHom 1 ((2:ℤ)^1411+3) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+3)+ep01011.subst ((2:ℤ)^1411+3) := by decide +kernel
private theorem pointp01011_4 : fastHom 1 ((2:ℤ)^1411+4) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+4)+ep01011.subst ((2:ℤ)^1411+4) := by decide +kernel
private theorem pointp01011_5 : fastHom 1 ((2:ℤ)^1411+5) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+5)+ep01011.subst ((2:ℤ)^1411+5) := by decide +kernel
private theorem pointp01011_6 : fastHom 1 ((2:ℤ)^1411+6) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+6)+ep01011.subst ((2:ℤ)^1411+6) := by decide +kernel
private theorem pointp01011_7 : fastHom 1 ((2:ℤ)^1411+7) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+7)+ep01011.subst ((2:ℤ)^1411+7) := by decide +kernel
private theorem pointp01011_8 : fastHom 1 ((2:ℤ)^1411+8) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+8)+ep01011.subst ((2:ℤ)^1411+8) := by decide +kernel
private theorem pointp01011_9 : fastHom 1 ((2:ℤ)^1411+9) vp0101 = ((2:ℤ)^9989)*vp01011.subst ((2:ℤ)^1411+9)+ep01011.subst ((2:ℤ)^1411+9) := by decide +kernel
private theorem checkp01011 (x:ℤ) (hx:x ∈ ptsp01011) : fastHom 1 x vp0101 = ((2:ℤ)^9989)*vp01011.subst x+ep01011.subst x := by
  simp only [ptsp01011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp01011_0
  · exact pointp01011_1
  · exact pointp01011_2
  · exact pointp01011_3
  · exact pointp01011_4
  · exact pointp01011_5
  · exact pointp01011_6
  · exact pointp01011_7
  · exact pointp01011_8
  · exact pointp01011_9
private theorem idp01011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101.list =
    C ((2:ℤ)^9989) * horner X vp01011.list + horner X ep01011.list := by
  apply edge_identity (B := (2:ℤ)^13604) (by decide) (by positivity) (by positivity) boundp01011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp01011 (by decide +kernel)
  · have h : ptsp01011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp01011.trans_le (by decide +kernel)
  · exact checkp01011
private theorem bp01011 : Branch 1 (-2559761639/512000000 : ℚ) vp0101 := by
  apply branch_checked idp01011 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-2815761639/256000000 : ℚ) by norm_num]
  exact coverp01011
theorem coverp0101 : Covers (-2559761639/512000000 : ℚ) vp0101 := join_branches bp01010 bp01011
end NextProof.EdgeFull

