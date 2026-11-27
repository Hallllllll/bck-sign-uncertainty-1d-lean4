import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00111
import NextProof.EdgeFull00113

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0100_0 : Blocks := edgeBlocks% "full/vectors/0100-V-0000.bin"
private noncomputable def vp0100_1 : Blocks := edgeBlocks% "full/vectors/0100-V-0001.bin"
private noncomputable def vp0100_2 : Blocks := edgeBlocks% "full/vectors/0100-V-0002.bin"
private noncomputable def vp0100_3 : Blocks := edgeBlocks% "full/vectors/0100-V-0003.bin"
private noncomputable def vp0100_4 : Blocks := edgeBlocks% "full/vectors/0100-V-0004.bin"
private noncomputable def vp0100_5 : Blocks := edgeBlocks% "full/vectors/0100-V-0005.bin"
private noncomputable def vp0100_6 : Blocks := edgeBlocks% "full/vectors/0100-V-0006.bin"
private noncomputable def vp0100_7 : Blocks := edgeBlocks% "full/vectors/0100-V-0007.bin"
private noncomputable def vp0100_8 : Blocks := edgeBlocks% "full/vectors/0100-V-0008.bin"
private noncomputable def vp0100_9 : Blocks := edgeBlocks% "full/vectors/0100-V-0009.bin"
private noncomputable def vp0100_10 : Blocks := edgeBlocks% "full/vectors/0100-V-0010.bin"
private noncomputable def vp0100_11 : Blocks := edgeBlocks% "full/vectors/0100-V-0011.bin"
private noncomputable def vp0100_12 : Blocks := edgeBlocks% "full/vectors/0100-V-0012.bin"
private noncomputable def vp0100_13 : Blocks := edgeBlocks% "full/vectors/0100-V-0013.bin"
private noncomputable def vp0100_14 : Blocks := edgeBlocks% "full/vectors/0100-V-0014.bin"
private noncomputable def vp0100_15 : Blocks := edgeBlocks% "full/vectors/0100-V-0015.bin"
private noncomputable def vp0100_16 : Blocks := edgeBlocks% "full/vectors/0100-V-0016.bin"
private noncomputable def vp0100_17 : Blocks := edgeBlocks% "full/vectors/0100-V-0017.bin"
private noncomputable def vp0100_18 : Blocks := edgeBlocks% "full/vectors/0100-V-0018.bin"
private noncomputable def vp0100_19 : Blocks := edgeBlocks% "full/vectors/0100-V-0019.bin"
private noncomputable def vp0100_20 : Blocks := edgeBlocks% "full/vectors/0100-V-0020.bin"
private noncomputable def vp0100_21 : Blocks := edgeBlocks% "full/vectors/0100-V-0021.bin"
private noncomputable def vp0100_22 : Blocks := edgeBlocks% "full/vectors/0100-V-0022.bin"
private noncomputable def vp0100_23 : Blocks := edgeBlocks% "full/vectors/0100-V-0023.bin"
private noncomputable def vp0100_24 : Blocks := edgeBlocks% "full/vectors/0100-V-0024.bin"
private noncomputable def vp0100_25 : Blocks := edgeBlocks% "full/vectors/0100-V-0025.bin"
private noncomputable def vp0100_26 : Blocks := edgeBlocks% "full/vectors/0100-V-0026.bin"
private noncomputable def vp0100_27 : Blocks := edgeBlocks% "full/vectors/0100-V-0027.bin"
private noncomputable def vp0100_28 : Blocks := edgeBlocks% "full/vectors/0100-V-0028.bin"
private noncomputable def vp0100_29 : Blocks := edgeBlocks% "full/vectors/0100-V-0029.bin"
private noncomputable def vp0100_30 : Blocks := edgeBlocks% "full/vectors/0100-V-0030.bin"
private noncomputable def vp0100_31 : Blocks := edgeBlocks% "full/vectors/0100-V-0031.bin"
private noncomputable def vp0100_32 : Blocks := edgeBlocks% "full/vectors/0100-V-0032.bin"
private noncomputable def vp0100_33 : Blocks := edgeBlocks% "full/vectors/0100-V-0033.bin"
private noncomputable def vp0100_34 : Blocks := edgeBlocks% "full/vectors/0100-V-0034.bin"
private noncomputable def vp0100_35 : Blocks := edgeBlocks% "full/vectors/0100-V-0035.bin"
private noncomputable def vp0100_36 : Blocks := edgeBlocks% "full/vectors/0100-V-0036.bin"
private noncomputable def vp0100_37 : Blocks := edgeBlocks% "full/vectors/0100-V-0037.bin"
private noncomputable def vp0100_38 : Blocks := edgeBlocks% "full/vectors/0100-V-0038.bin"
private noncomputable def vp0100_39 : Blocks := edgeBlocks% "full/vectors/0100-V-0039.bin"
private noncomputable def vp0100_40 : Blocks := edgeBlocks% "full/vectors/0100-V-0040.bin"
private noncomputable def vp0100_41 : Blocks := edgeBlocks% "full/vectors/0100-V-0041.bin"
private noncomputable def vp0100_42 : Blocks := edgeBlocks% "full/vectors/0100-V-0042.bin"
private noncomputable def vp0100_43 : Blocks := edgeBlocks% "full/vectors/0100-V-0043.bin"
private noncomputable def vp0100_44 : Blocks := edgeBlocks% "full/vectors/0100-V-0044.bin"
private noncomputable def vp0100_45 : Blocks := edgeBlocks% "full/vectors/0100-V-0045.bin"
private noncomputable def vp0100_46 : Blocks := edgeBlocks% "full/vectors/0100-V-0046.bin"
private noncomputable def vp0100_47 : Blocks := edgeBlocks% "full/vectors/0100-V-0047.bin"
private noncomputable def vp0100_48 : Blocks := edgeBlocks% "full/vectors/0100-V-0048.bin"
private noncomputable def vp0100_49 : Blocks := edgeBlocks% "full/vectors/0100-V-0049.bin"
private noncomputable def vp0100_50 : Blocks := edgeBlocks% "full/vectors/0100-V-0050.bin"
private noncomputable def vp0100_51 : Blocks := edgeBlocks% "full/vectors/0100-V-0051.bin"
private noncomputable def vp0100_52 : Blocks := edgeBlocks% "full/vectors/0100-V-0052.bin"
private noncomputable def vp0100_53 : Blocks := edgeBlocks% "full/vectors/0100-V-0053.bin"
private noncomputable def vp0100_54 : Blocks := edgeBlocks% "full/vectors/0100-V-0054.bin"
private noncomputable def vp0100_55 : Blocks := edgeBlocks% "full/vectors/0100-V-0055.bin"
private noncomputable def vp0100_56 : Blocks := edgeBlocks% "full/vectors/0100-V-0056.bin"
private noncomputable def vp0100_57 : Blocks := edgeBlocks% "full/vectors/0100-V-0057.bin"
private noncomputable def vp0100_58 : Blocks := edgeBlocks% "full/vectors/0100-V-0058.bin"
private noncomputable def vp0100_59 : Blocks := edgeBlocks% "full/vectors/0100-V-0059.bin"
private noncomputable def vp0100_60 : Blocks := edgeBlocks% "full/vectors/0100-V-0060.bin"
private noncomputable def vp0100_61 : Blocks := edgeBlocks% "full/vectors/0100-V-0061.bin"
private noncomputable def vp0100_62 : Blocks := edgeBlocks% "full/vectors/0100-V-0062.bin"
private noncomputable def vp0100_63 : Blocks := edgeBlocks% "full/vectors/0100-V-0063.bin"
private noncomputable def vp0100_64 : Blocks := edgeBlocks% "full/vectors/0100-V-0064.bin"
private noncomputable def vp0100_65 : Blocks := edgeBlocks% "full/vectors/0100-V-0065.bin"
private noncomputable def vp0100_66 : Blocks := edgeBlocks% "full/vectors/0100-V-0066.bin"
private noncomputable def vp0100_67 : Blocks := edgeBlocks% "full/vectors/0100-V-0067.bin"
private noncomputable def vp0100_68 : Blocks := edgeBlocks% "full/vectors/0100-V-0068.bin"
private noncomputable def vp0100_69 : Blocks := edgeBlocks% "full/vectors/0100-V-0069.bin"
private noncomputable def vp0100_70 : Blocks := edgeBlocks% "full/vectors/0100-V-0070.bin"
private noncomputable def vp0100_71 : Blocks := edgeBlocks% "full/vectors/0100-V-0071.bin"
private noncomputable def vp0100_72 : Blocks := edgeBlocks% "full/vectors/0100-V-0072.bin"
noncomputable def vp0100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0100_0 vp0100_1) (Blocks.join vp0100_2 vp0100_3)) (Blocks.join (Blocks.join vp0100_4 vp0100_5) (Blocks.join vp0100_6 (Blocks.join vp0100_7 vp0100_8)))) (Blocks.join (Blocks.join (Blocks.join vp0100_9 vp0100_10) (Blocks.join vp0100_11 vp0100_12)) (Blocks.join (Blocks.join vp0100_13 vp0100_14) (Blocks.join vp0100_15 (Blocks.join vp0100_16 vp0100_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0100_18 vp0100_19) (Blocks.join vp0100_20 vp0100_21)) (Blocks.join (Blocks.join vp0100_22 vp0100_23) (Blocks.join vp0100_24 (Blocks.join vp0100_25 vp0100_26)))) (Blocks.join (Blocks.join (Blocks.join vp0100_27 vp0100_28) (Blocks.join vp0100_29 vp0100_30)) (Blocks.join (Blocks.join vp0100_31 vp0100_32) (Blocks.join vp0100_33 (Blocks.join vp0100_34 vp0100_35)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0100_36 vp0100_37) (Blocks.join vp0100_38 vp0100_39)) (Blocks.join (Blocks.join vp0100_40 vp0100_41) (Blocks.join vp0100_42 (Blocks.join vp0100_43 vp0100_44)))) (Blocks.join (Blocks.join (Blocks.join vp0100_45 vp0100_46) (Blocks.join vp0100_47 vp0100_48)) (Blocks.join (Blocks.join vp0100_49 vp0100_50) (Blocks.join vp0100_51 (Blocks.join vp0100_52 vp0100_53))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0100_54 vp0100_55) (Blocks.join vp0100_56 vp0100_57)) (Blocks.join (Blocks.join vp0100_58 vp0100_59) (Blocks.join vp0100_60 (Blocks.join vp0100_61 vp0100_62)))) (Blocks.join (Blocks.join (Blocks.join vp0100_63 vp0100_64) (Blocks.join vp0100_65 (Blocks.join vp0100_66 vp0100_67))) (Blocks.join (Blocks.join vp0100_68 vp0100_69) (Blocks.join vp0100_70 (Blocks.join vp0100_71 vp0100_72)))))))
private theorem bp01000 : Branch 0 (-2047761639/512000000 : ℚ) vp0100 := by
  apply branch_left_normalized (c:=vp01000) (k:=0) (m:=5118) (by decide +kernel)
  rw [show 2*(-2047761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/256000000 : ℚ) by norm_num]
  exact coverp01000
private noncomputable def ep01001_0 : Blocks := edgeBlocks% "full/vectors/01001-E-0000.bin"
private noncomputable def ep01001_1 : Blocks := edgeBlocks% "full/vectors/01001-E-0001.bin"
private noncomputable def ep01001_2 : Blocks := edgeBlocks% "full/vectors/01001-E-0002.bin"
private noncomputable def ep01001_3 : Blocks := edgeBlocks% "full/vectors/01001-E-0003.bin"
private noncomputable def ep01001_4 : Blocks := edgeBlocks% "full/vectors/01001-E-0004.bin"
private noncomputable def ep01001_5 : Blocks := edgeBlocks% "full/vectors/01001-E-0005.bin"
private noncomputable def ep01001_6 : Blocks := edgeBlocks% "full/vectors/01001-E-0006.bin"
private noncomputable def ep01001_7 : Blocks := edgeBlocks% "full/vectors/01001-E-0007.bin"
private noncomputable def ep01001_8 : Blocks := edgeBlocks% "full/vectors/01001-E-0008.bin"
private noncomputable def ep01001_9 : Blocks := edgeBlocks% "full/vectors/01001-E-0009.bin"
private noncomputable def ep01001_10 : Blocks := edgeBlocks% "full/vectors/01001-E-0010.bin"
private noncomputable def ep01001_11 : Blocks := edgeBlocks% "full/vectors/01001-E-0011.bin"
private noncomputable def ep01001_12 : Blocks := edgeBlocks% "full/vectors/01001-E-0012.bin"
private noncomputable def ep01001_13 : Blocks := edgeBlocks% "full/vectors/01001-E-0013.bin"
private noncomputable def ep01001_14 : Blocks := edgeBlocks% "full/vectors/01001-E-0014.bin"
private noncomputable def ep01001_15 : Blocks := edgeBlocks% "full/vectors/01001-E-0015.bin"
private noncomputable def ep01001_16 : Blocks := edgeBlocks% "full/vectors/01001-E-0016.bin"
private noncomputable def ep01001_17 : Blocks := edgeBlocks% "full/vectors/01001-E-0017.bin"
private noncomputable def ep01001_18 : Blocks := edgeBlocks% "full/vectors/01001-E-0018.bin"
private noncomputable def ep01001_19 : Blocks := edgeBlocks% "full/vectors/01001-E-0019.bin"
private noncomputable def ep01001_20 : Blocks := edgeBlocks% "full/vectors/01001-E-0020.bin"
private noncomputable def ep01001_21 : Blocks := edgeBlocks% "full/vectors/01001-E-0021.bin"
private noncomputable def ep01001_22 : Blocks := edgeBlocks% "full/vectors/01001-E-0022.bin"
private noncomputable def ep01001_23 : Blocks := edgeBlocks% "full/vectors/01001-E-0023.bin"
private noncomputable def ep01001_24 : Blocks := edgeBlocks% "full/vectors/01001-E-0024.bin"
private noncomputable def ep01001_25 : Blocks := edgeBlocks% "full/vectors/01001-E-0025.bin"
private noncomputable def ep01001_26 : Blocks := edgeBlocks% "full/vectors/01001-E-0026.bin"
private noncomputable def ep01001_27 : Blocks := edgeBlocks% "full/vectors/01001-E-0027.bin"
private noncomputable def ep01001_28 : Blocks := edgeBlocks% "full/vectors/01001-E-0028.bin"
private noncomputable def ep01001_29 : Blocks := edgeBlocks% "full/vectors/01001-E-0029.bin"
private noncomputable def ep01001_30 : Blocks := edgeBlocks% "full/vectors/01001-E-0030.bin"
private noncomputable def ep01001_31 : Blocks := edgeBlocks% "full/vectors/01001-E-0031.bin"
private noncomputable def ep01001_32 : Blocks := edgeBlocks% "full/vectors/01001-E-0032.bin"
private noncomputable def ep01001_33 : Blocks := edgeBlocks% "full/vectors/01001-E-0033.bin"
private noncomputable def ep01001_34 : Blocks := edgeBlocks% "full/vectors/01001-E-0034.bin"
private noncomputable def ep01001_35 : Blocks := edgeBlocks% "full/vectors/01001-E-0035.bin"
private noncomputable def ep01001_36 : Blocks := edgeBlocks% "full/vectors/01001-E-0036.bin"
private noncomputable def ep01001_37 : Blocks := edgeBlocks% "full/vectors/01001-E-0037.bin"
private noncomputable def ep01001_38 : Blocks := edgeBlocks% "full/vectors/01001-E-0038.bin"
private noncomputable def ep01001_39 : Blocks := edgeBlocks% "full/vectors/01001-E-0039.bin"
private noncomputable def ep01001_40 : Blocks := edgeBlocks% "full/vectors/01001-E-0040.bin"
private noncomputable def ep01001_41 : Blocks := edgeBlocks% "full/vectors/01001-E-0041.bin"
private noncomputable def ep01001_42 : Blocks := edgeBlocks% "full/vectors/01001-E-0042.bin"
private noncomputable def ep01001_43 : Blocks := edgeBlocks% "full/vectors/01001-E-0043.bin"
private noncomputable def ep01001_44 : Blocks := edgeBlocks% "full/vectors/01001-E-0044.bin"
private noncomputable def ep01001_45 : Blocks := edgeBlocks% "full/vectors/01001-E-0045.bin"
private noncomputable def ep01001_46 : Blocks := edgeBlocks% "full/vectors/01001-E-0046.bin"
private noncomputable def ep01001_47 : Blocks := edgeBlocks% "full/vectors/01001-E-0047.bin"
private noncomputable def ep01001_48 : Blocks := edgeBlocks% "full/vectors/01001-E-0048.bin"
private noncomputable def ep01001_49 : Blocks := edgeBlocks% "full/vectors/01001-E-0049.bin"
private noncomputable def ep01001_50 : Blocks := edgeBlocks% "full/vectors/01001-E-0050.bin"
private noncomputable def ep01001_51 : Blocks := edgeBlocks% "full/vectors/01001-E-0051.bin"
private noncomputable def ep01001_52 : Blocks := edgeBlocks% "full/vectors/01001-E-0052.bin"
private noncomputable def ep01001_53 : Blocks := edgeBlocks% "full/vectors/01001-E-0053.bin"
private noncomputable def ep01001_54 : Blocks := edgeBlocks% "full/vectors/01001-E-0054.bin"
private noncomputable def ep01001_55 : Blocks := edgeBlocks% "full/vectors/01001-E-0055.bin"
private noncomputable def ep01001_56 : Blocks := edgeBlocks% "full/vectors/01001-E-0056.bin"
private noncomputable def ep01001_57 : Blocks := edgeBlocks% "full/vectors/01001-E-0057.bin"
private noncomputable def ep01001_58 : Blocks := edgeBlocks% "full/vectors/01001-E-0058.bin"
private noncomputable def ep01001_59 : Blocks := edgeBlocks% "full/vectors/01001-E-0059.bin"
private noncomputable def ep01001_60 : Blocks := edgeBlocks% "full/vectors/01001-E-0060.bin"
private noncomputable def ep01001_61 : Blocks := edgeBlocks% "full/vectors/01001-E-0061.bin"
private noncomputable def ep01001_62 : Blocks := edgeBlocks% "full/vectors/01001-E-0062.bin"
private noncomputable def ep01001_63 : Blocks := edgeBlocks% "full/vectors/01001-E-0063.bin"
private noncomputable def ep01001_64 : Blocks := edgeBlocks% "full/vectors/01001-E-0064.bin"
private noncomputable def ep01001_65 : Blocks := edgeBlocks% "full/vectors/01001-E-0065.bin"
private noncomputable def ep01001_66 : Blocks := edgeBlocks% "full/vectors/01001-E-0066.bin"
private noncomputable def ep01001_67 : Blocks := edgeBlocks% "full/vectors/01001-E-0067.bin"
private noncomputable def ep01001_68 : Blocks := edgeBlocks% "full/vectors/01001-E-0068.bin"
private noncomputable def ep01001_69 : Blocks := edgeBlocks% "full/vectors/01001-E-0069.bin"
private noncomputable def ep01001_70 : Blocks := edgeBlocks% "full/vectors/01001-E-0070.bin"
private noncomputable def ep01001_71 : Blocks := edgeBlocks% "full/vectors/01001-E-0071.bin"
private noncomputable def ep01001_72 : Blocks := edgeBlocks% "full/vectors/01001-E-0072.bin"
noncomputable def ep01001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01001_0 ep01001_1) (Blocks.join ep01001_2 ep01001_3)) (Blocks.join (Blocks.join ep01001_4 ep01001_5) (Blocks.join ep01001_6 (Blocks.join ep01001_7 ep01001_8)))) (Blocks.join (Blocks.join (Blocks.join ep01001_9 ep01001_10) (Blocks.join ep01001_11 ep01001_12)) (Blocks.join (Blocks.join ep01001_13 ep01001_14) (Blocks.join ep01001_15 (Blocks.join ep01001_16 ep01001_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01001_18 ep01001_19) (Blocks.join ep01001_20 ep01001_21)) (Blocks.join (Blocks.join ep01001_22 ep01001_23) (Blocks.join ep01001_24 (Blocks.join ep01001_25 ep01001_26)))) (Blocks.join (Blocks.join (Blocks.join ep01001_27 ep01001_28) (Blocks.join ep01001_29 ep01001_30)) (Blocks.join (Blocks.join ep01001_31 ep01001_32) (Blocks.join ep01001_33 (Blocks.join ep01001_34 ep01001_35)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01001_36 ep01001_37) (Blocks.join ep01001_38 ep01001_39)) (Blocks.join (Blocks.join ep01001_40 ep01001_41) (Blocks.join ep01001_42 (Blocks.join ep01001_43 ep01001_44)))) (Blocks.join (Blocks.join (Blocks.join ep01001_45 ep01001_46) (Blocks.join ep01001_47 ep01001_48)) (Blocks.join (Blocks.join ep01001_49 ep01001_50) (Blocks.join ep01001_51 (Blocks.join ep01001_52 ep01001_53))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01001_54 ep01001_55) (Blocks.join ep01001_56 ep01001_57)) (Blocks.join (Blocks.join ep01001_58 ep01001_59) (Blocks.join ep01001_60 (Blocks.join ep01001_61 ep01001_62)))) (Blocks.join (Blocks.join (Blocks.join ep01001_63 ep01001_64) (Blocks.join ep01001_65 (Blocks.join ep01001_66 ep01001_67))) (Blocks.join (Blocks.join ep01001_68 ep01001_69) (Blocks.join ep01001_70 (Blocks.join ep01001_71 ep01001_72)))))))
private def ptsp01001 : List ℤ := [((2:ℤ)^1288+0),((2:ℤ)^1288+1),((2:ℤ)^1288+2),((2:ℤ)^1288+3),((2:ℤ)^1288+4),((2:ℤ)^1288+5),((2:ℤ)^1288+6),((2:ℤ)^1288+7),((2:ℤ)^1288+8),((2:ℤ)^1288+9),((2:ℤ)^1288+10),((2:ℤ)^1288+11)]
private theorem boundp01001 : 2^vp0100.size*absSum vp0100.list + ((2:ℤ)^10788*absSum vp01001.list+absSum ep01001.list) < (2:ℤ)^14965 := by decide +kernel
private theorem pointp01001_0 : fastHom 1 ((2:ℤ)^1288+0) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+0)+ep01001.subst ((2:ℤ)^1288+0) := by decide +kernel
private theorem pointp01001_1 : fastHom 1 ((2:ℤ)^1288+1) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+1)+ep01001.subst ((2:ℤ)^1288+1) := by decide +kernel
private theorem pointp01001_2 : fastHom 1 ((2:ℤ)^1288+2) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+2)+ep01001.subst ((2:ℤ)^1288+2) := by decide +kernel
private theorem pointp01001_3 : fastHom 1 ((2:ℤ)^1288+3) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+3)+ep01001.subst ((2:ℤ)^1288+3) := by decide +kernel
private theorem pointp01001_4 : fastHom 1 ((2:ℤ)^1288+4) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+4)+ep01001.subst ((2:ℤ)^1288+4) := by decide +kernel
private theorem pointp01001_5 : fastHom 1 ((2:ℤ)^1288+5) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+5)+ep01001.subst ((2:ℤ)^1288+5) := by decide +kernel
private theorem pointp01001_6 : fastHom 1 ((2:ℤ)^1288+6) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+6)+ep01001.subst ((2:ℤ)^1288+6) := by decide +kernel
private theorem pointp01001_7 : fastHom 1 ((2:ℤ)^1288+7) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+7)+ep01001.subst ((2:ℤ)^1288+7) := by decide +kernel
private theorem pointp01001_8 : fastHom 1 ((2:ℤ)^1288+8) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+8)+ep01001.subst ((2:ℤ)^1288+8) := by decide +kernel
private theorem pointp01001_9 : fastHom 1 ((2:ℤ)^1288+9) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+9)+ep01001.subst ((2:ℤ)^1288+9) := by decide +kernel
private theorem pointp01001_10 : fastHom 1 ((2:ℤ)^1288+10) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+10)+ep01001.subst ((2:ℤ)^1288+10) := by decide +kernel
private theorem pointp01001_11 : fastHom 1 ((2:ℤ)^1288+11) vp0100 = ((2:ℤ)^10788)*vp01001.subst ((2:ℤ)^1288+11)+ep01001.subst ((2:ℤ)^1288+11) := by decide +kernel
private theorem checkp01001 (x:ℤ) (hx:x ∈ ptsp01001) : fastHom 1 x vp0100 = ((2:ℤ)^10788)*vp01001.subst x+ep01001.subst x := by
  simp only [ptsp01001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp01001_0
  · exact pointp01001_1
  · exact pointp01001_2
  · exact pointp01001_3
  · exact pointp01001_4
  · exact pointp01001_5
  · exact pointp01001_6
  · exact pointp01001_7
  · exact pointp01001_8
  · exact pointp01001_9
  · exact pointp01001_10
  · exact pointp01001_11
private theorem idp01001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100.list =
    C ((2:ℤ)^10788) * horner X vp01001.list + horner X ep01001.list := by
  apply edge_identity (B := (2:ℤ)^14965) (by decide) (by positivity) (by positivity) boundp01001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp01001 (by decide +kernel)
  · have h : ptsp01001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp01001.trans_le (by decide +kernel)
  · exact checkp01001
private theorem bp01001 : Branch 1 (-2047761639/512000000 : ℚ) vp0100 := by
  apply branch_checked idp01001 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-2303761639/256000000 : ℚ) by norm_num]
  exact coverp01001
theorem coverp0100 : Covers (-2047761639/512000000 : ℚ) vp0100 := join_branches bp01000 bp01001
end NextProof.EdgeFull

