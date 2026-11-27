import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00140
import NextProof.EdgeFull00141

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp110_0 : Blocks := edgeBlocks% "full/vectors/110-V-0000.bin"
private noncomputable def vp110_1 : Blocks := edgeBlocks% "full/vectors/110-V-0001.bin"
private noncomputable def vp110_2 : Blocks := edgeBlocks% "full/vectors/110-V-0002.bin"
private noncomputable def vp110_3 : Blocks := edgeBlocks% "full/vectors/110-V-0003.bin"
private noncomputable def vp110_4 : Blocks := edgeBlocks% "full/vectors/110-V-0004.bin"
private noncomputable def vp110_5 : Blocks := edgeBlocks% "full/vectors/110-V-0005.bin"
private noncomputable def vp110_6 : Blocks := edgeBlocks% "full/vectors/110-V-0006.bin"
private noncomputable def vp110_7 : Blocks := edgeBlocks% "full/vectors/110-V-0007.bin"
private noncomputable def vp110_8 : Blocks := edgeBlocks% "full/vectors/110-V-0008.bin"
private noncomputable def vp110_9 : Blocks := edgeBlocks% "full/vectors/110-V-0009.bin"
private noncomputable def vp110_10 : Blocks := edgeBlocks% "full/vectors/110-V-0010.bin"
private noncomputable def vp110_11 : Blocks := edgeBlocks% "full/vectors/110-V-0011.bin"
private noncomputable def vp110_12 : Blocks := edgeBlocks% "full/vectors/110-V-0012.bin"
private noncomputable def vp110_13 : Blocks := edgeBlocks% "full/vectors/110-V-0013.bin"
private noncomputable def vp110_14 : Blocks := edgeBlocks% "full/vectors/110-V-0014.bin"
private noncomputable def vp110_15 : Blocks := edgeBlocks% "full/vectors/110-V-0015.bin"
private noncomputable def vp110_16 : Blocks := edgeBlocks% "full/vectors/110-V-0016.bin"
private noncomputable def vp110_17 : Blocks := edgeBlocks% "full/vectors/110-V-0017.bin"
private noncomputable def vp110_18 : Blocks := edgeBlocks% "full/vectors/110-V-0018.bin"
private noncomputable def vp110_19 : Blocks := edgeBlocks% "full/vectors/110-V-0019.bin"
private noncomputable def vp110_20 : Blocks := edgeBlocks% "full/vectors/110-V-0020.bin"
private noncomputable def vp110_21 : Blocks := edgeBlocks% "full/vectors/110-V-0021.bin"
private noncomputable def vp110_22 : Blocks := edgeBlocks% "full/vectors/110-V-0022.bin"
private noncomputable def vp110_23 : Blocks := edgeBlocks% "full/vectors/110-V-0023.bin"
private noncomputable def vp110_24 : Blocks := edgeBlocks% "full/vectors/110-V-0024.bin"
private noncomputable def vp110_25 : Blocks := edgeBlocks% "full/vectors/110-V-0025.bin"
private noncomputable def vp110_26 : Blocks := edgeBlocks% "full/vectors/110-V-0026.bin"
private noncomputable def vp110_27 : Blocks := edgeBlocks% "full/vectors/110-V-0027.bin"
private noncomputable def vp110_28 : Blocks := edgeBlocks% "full/vectors/110-V-0028.bin"
private noncomputable def vp110_29 : Blocks := edgeBlocks% "full/vectors/110-V-0029.bin"
private noncomputable def vp110_30 : Blocks := edgeBlocks% "full/vectors/110-V-0030.bin"
private noncomputable def vp110_31 : Blocks := edgeBlocks% "full/vectors/110-V-0031.bin"
private noncomputable def vp110_32 : Blocks := edgeBlocks% "full/vectors/110-V-0032.bin"
private noncomputable def vp110_33 : Blocks := edgeBlocks% "full/vectors/110-V-0033.bin"
private noncomputable def vp110_34 : Blocks := edgeBlocks% "full/vectors/110-V-0034.bin"
private noncomputable def vp110_35 : Blocks := edgeBlocks% "full/vectors/110-V-0035.bin"
private noncomputable def vp110_36 : Blocks := edgeBlocks% "full/vectors/110-V-0036.bin"
private noncomputable def vp110_37 : Blocks := edgeBlocks% "full/vectors/110-V-0037.bin"
private noncomputable def vp110_38 : Blocks := edgeBlocks% "full/vectors/110-V-0038.bin"
private noncomputable def vp110_39 : Blocks := edgeBlocks% "full/vectors/110-V-0039.bin"
private noncomputable def vp110_40 : Blocks := edgeBlocks% "full/vectors/110-V-0040.bin"
private noncomputable def vp110_41 : Blocks := edgeBlocks% "full/vectors/110-V-0041.bin"
private noncomputable def vp110_42 : Blocks := edgeBlocks% "full/vectors/110-V-0042.bin"
private noncomputable def vp110_43 : Blocks := edgeBlocks% "full/vectors/110-V-0043.bin"
private noncomputable def vp110_44 : Blocks := edgeBlocks% "full/vectors/110-V-0044.bin"
private noncomputable def vp110_45 : Blocks := edgeBlocks% "full/vectors/110-V-0045.bin"
private noncomputable def vp110_46 : Blocks := edgeBlocks% "full/vectors/110-V-0046.bin"
private noncomputable def vp110_47 : Blocks := edgeBlocks% "full/vectors/110-V-0047.bin"
private noncomputable def vp110_48 : Blocks := edgeBlocks% "full/vectors/110-V-0048.bin"
private noncomputable def vp110_49 : Blocks := edgeBlocks% "full/vectors/110-V-0049.bin"
private noncomputable def vp110_50 : Blocks := edgeBlocks% "full/vectors/110-V-0050.bin"
private noncomputable def vp110_51 : Blocks := edgeBlocks% "full/vectors/110-V-0051.bin"
private noncomputable def vp110_52 : Blocks := edgeBlocks% "full/vectors/110-V-0052.bin"
private noncomputable def vp110_53 : Blocks := edgeBlocks% "full/vectors/110-V-0053.bin"
private noncomputable def vp110_54 : Blocks := edgeBlocks% "full/vectors/110-V-0054.bin"
private noncomputable def vp110_55 : Blocks := edgeBlocks% "full/vectors/110-V-0055.bin"
private noncomputable def vp110_56 : Blocks := edgeBlocks% "full/vectors/110-V-0056.bin"
private noncomputable def vp110_57 : Blocks := edgeBlocks% "full/vectors/110-V-0057.bin"
private noncomputable def vp110_58 : Blocks := edgeBlocks% "full/vectors/110-V-0058.bin"
private noncomputable def vp110_59 : Blocks := edgeBlocks% "full/vectors/110-V-0059.bin"
private noncomputable def vp110_60 : Blocks := edgeBlocks% "full/vectors/110-V-0060.bin"
private noncomputable def vp110_61 : Blocks := edgeBlocks% "full/vectors/110-V-0061.bin"
private noncomputable def vp110_62 : Blocks := edgeBlocks% "full/vectors/110-V-0062.bin"
private noncomputable def vp110_63 : Blocks := edgeBlocks% "full/vectors/110-V-0063.bin"
private noncomputable def vp110_64 : Blocks := edgeBlocks% "full/vectors/110-V-0064.bin"
private noncomputable def vp110_65 : Blocks := edgeBlocks% "full/vectors/110-V-0065.bin"
private noncomputable def vp110_66 : Blocks := edgeBlocks% "full/vectors/110-V-0066.bin"
private noncomputable def vp110_67 : Blocks := edgeBlocks% "full/vectors/110-V-0067.bin"
private noncomputable def vp110_68 : Blocks := edgeBlocks% "full/vectors/110-V-0068.bin"
private noncomputable def vp110_69 : Blocks := edgeBlocks% "full/vectors/110-V-0069.bin"
private noncomputable def vp110_70 : Blocks := edgeBlocks% "full/vectors/110-V-0070.bin"
private noncomputable def vp110_71 : Blocks := edgeBlocks% "full/vectors/110-V-0071.bin"
private noncomputable def vp110_72 : Blocks := edgeBlocks% "full/vectors/110-V-0072.bin"
private noncomputable def vp110_73 : Blocks := edgeBlocks% "full/vectors/110-V-0073.bin"
private noncomputable def vp110_74 : Blocks := edgeBlocks% "full/vectors/110-V-0074.bin"
private noncomputable def vp110_75 : Blocks := edgeBlocks% "full/vectors/110-V-0075.bin"
private noncomputable def vp110_76 : Blocks := edgeBlocks% "full/vectors/110-V-0076.bin"
private noncomputable def vp110_77 : Blocks := edgeBlocks% "full/vectors/110-V-0077.bin"
noncomputable def vp110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp110_0 vp110_1) (Blocks.join vp110_2 vp110_3)) (Blocks.join (Blocks.join vp110_4 vp110_5) (Blocks.join vp110_6 (Blocks.join vp110_7 vp110_8)))) (Blocks.join (Blocks.join (Blocks.join vp110_9 vp110_10) (Blocks.join vp110_11 (Blocks.join vp110_12 vp110_13))) (Blocks.join (Blocks.join vp110_14 vp110_15) (Blocks.join vp110_16 (Blocks.join vp110_17 vp110_18))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp110_19 vp110_20) (Blocks.join vp110_21 (Blocks.join vp110_22 vp110_23))) (Blocks.join (Blocks.join vp110_24 vp110_25) (Blocks.join vp110_26 (Blocks.join vp110_27 vp110_28)))) (Blocks.join (Blocks.join (Blocks.join vp110_29 vp110_30) (Blocks.join vp110_31 (Blocks.join vp110_32 vp110_33))) (Blocks.join (Blocks.join vp110_34 vp110_35) (Blocks.join vp110_36 (Blocks.join vp110_37 vp110_38)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp110_39 vp110_40) (Blocks.join vp110_41 vp110_42)) (Blocks.join (Blocks.join vp110_43 vp110_44) (Blocks.join vp110_45 (Blocks.join vp110_46 vp110_47)))) (Blocks.join (Blocks.join (Blocks.join vp110_48 vp110_49) (Blocks.join vp110_50 (Blocks.join vp110_51 vp110_52))) (Blocks.join (Blocks.join vp110_53 vp110_54) (Blocks.join vp110_55 (Blocks.join vp110_56 vp110_57))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp110_58 vp110_59) (Blocks.join vp110_60 (Blocks.join vp110_61 vp110_62))) (Blocks.join (Blocks.join vp110_63 vp110_64) (Blocks.join vp110_65 (Blocks.join vp110_66 vp110_67)))) (Blocks.join (Blocks.join (Blocks.join vp110_68 vp110_69) (Blocks.join vp110_70 (Blocks.join vp110_71 vp110_72))) (Blocks.join (Blocks.join vp110_73 vp110_74) (Blocks.join vp110_75 (Blocks.join vp110_76 vp110_77)))))))
private theorem bp1100 : Branch 0 (-6143761639/1024000000 : ℚ) vp110 := by
  apply branch_left_normalized (c:=vp1100) (k:=0) (m:=5829) (by decide +kernel)
  rw [show 2*(-6143761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/512000000 : ℚ) by norm_num]
  exact coverp1100
private noncomputable def ep1101_0 : Blocks := edgeBlocks% "full/vectors/1101-E-0000.bin"
private noncomputable def ep1101_1 : Blocks := edgeBlocks% "full/vectors/1101-E-0001.bin"
private noncomputable def ep1101_2 : Blocks := edgeBlocks% "full/vectors/1101-E-0002.bin"
private noncomputable def ep1101_3 : Blocks := edgeBlocks% "full/vectors/1101-E-0003.bin"
private noncomputable def ep1101_4 : Blocks := edgeBlocks% "full/vectors/1101-E-0004.bin"
private noncomputable def ep1101_5 : Blocks := edgeBlocks% "full/vectors/1101-E-0005.bin"
private noncomputable def ep1101_6 : Blocks := edgeBlocks% "full/vectors/1101-E-0006.bin"
private noncomputable def ep1101_7 : Blocks := edgeBlocks% "full/vectors/1101-E-0007.bin"
private noncomputable def ep1101_8 : Blocks := edgeBlocks% "full/vectors/1101-E-0008.bin"
private noncomputable def ep1101_9 : Blocks := edgeBlocks% "full/vectors/1101-E-0009.bin"
private noncomputable def ep1101_10 : Blocks := edgeBlocks% "full/vectors/1101-E-0010.bin"
private noncomputable def ep1101_11 : Blocks := edgeBlocks% "full/vectors/1101-E-0011.bin"
private noncomputable def ep1101_12 : Blocks := edgeBlocks% "full/vectors/1101-E-0012.bin"
private noncomputable def ep1101_13 : Blocks := edgeBlocks% "full/vectors/1101-E-0013.bin"
private noncomputable def ep1101_14 : Blocks := edgeBlocks% "full/vectors/1101-E-0014.bin"
private noncomputable def ep1101_15 : Blocks := edgeBlocks% "full/vectors/1101-E-0015.bin"
private noncomputable def ep1101_16 : Blocks := edgeBlocks% "full/vectors/1101-E-0016.bin"
private noncomputable def ep1101_17 : Blocks := edgeBlocks% "full/vectors/1101-E-0017.bin"
private noncomputable def ep1101_18 : Blocks := edgeBlocks% "full/vectors/1101-E-0018.bin"
private noncomputable def ep1101_19 : Blocks := edgeBlocks% "full/vectors/1101-E-0019.bin"
private noncomputable def ep1101_20 : Blocks := edgeBlocks% "full/vectors/1101-E-0020.bin"
private noncomputable def ep1101_21 : Blocks := edgeBlocks% "full/vectors/1101-E-0021.bin"
private noncomputable def ep1101_22 : Blocks := edgeBlocks% "full/vectors/1101-E-0022.bin"
private noncomputable def ep1101_23 : Blocks := edgeBlocks% "full/vectors/1101-E-0023.bin"
private noncomputable def ep1101_24 : Blocks := edgeBlocks% "full/vectors/1101-E-0024.bin"
private noncomputable def ep1101_25 : Blocks := edgeBlocks% "full/vectors/1101-E-0025.bin"
private noncomputable def ep1101_26 : Blocks := edgeBlocks% "full/vectors/1101-E-0026.bin"
private noncomputable def ep1101_27 : Blocks := edgeBlocks% "full/vectors/1101-E-0027.bin"
private noncomputable def ep1101_28 : Blocks := edgeBlocks% "full/vectors/1101-E-0028.bin"
private noncomputable def ep1101_29 : Blocks := edgeBlocks% "full/vectors/1101-E-0029.bin"
private noncomputable def ep1101_30 : Blocks := edgeBlocks% "full/vectors/1101-E-0030.bin"
private noncomputable def ep1101_31 : Blocks := edgeBlocks% "full/vectors/1101-E-0031.bin"
private noncomputable def ep1101_32 : Blocks := edgeBlocks% "full/vectors/1101-E-0032.bin"
private noncomputable def ep1101_33 : Blocks := edgeBlocks% "full/vectors/1101-E-0033.bin"
private noncomputable def ep1101_34 : Blocks := edgeBlocks% "full/vectors/1101-E-0034.bin"
private noncomputable def ep1101_35 : Blocks := edgeBlocks% "full/vectors/1101-E-0035.bin"
private noncomputable def ep1101_36 : Blocks := edgeBlocks% "full/vectors/1101-E-0036.bin"
private noncomputable def ep1101_37 : Blocks := edgeBlocks% "full/vectors/1101-E-0037.bin"
private noncomputable def ep1101_38 : Blocks := edgeBlocks% "full/vectors/1101-E-0038.bin"
private noncomputable def ep1101_39 : Blocks := edgeBlocks% "full/vectors/1101-E-0039.bin"
private noncomputable def ep1101_40 : Blocks := edgeBlocks% "full/vectors/1101-E-0040.bin"
private noncomputable def ep1101_41 : Blocks := edgeBlocks% "full/vectors/1101-E-0041.bin"
private noncomputable def ep1101_42 : Blocks := edgeBlocks% "full/vectors/1101-E-0042.bin"
private noncomputable def ep1101_43 : Blocks := edgeBlocks% "full/vectors/1101-E-0043.bin"
private noncomputable def ep1101_44 : Blocks := edgeBlocks% "full/vectors/1101-E-0044.bin"
private noncomputable def ep1101_45 : Blocks := edgeBlocks% "full/vectors/1101-E-0045.bin"
private noncomputable def ep1101_46 : Blocks := edgeBlocks% "full/vectors/1101-E-0046.bin"
private noncomputable def ep1101_47 : Blocks := edgeBlocks% "full/vectors/1101-E-0047.bin"
private noncomputable def ep1101_48 : Blocks := edgeBlocks% "full/vectors/1101-E-0048.bin"
private noncomputable def ep1101_49 : Blocks := edgeBlocks% "full/vectors/1101-E-0049.bin"
private noncomputable def ep1101_50 : Blocks := edgeBlocks% "full/vectors/1101-E-0050.bin"
private noncomputable def ep1101_51 : Blocks := edgeBlocks% "full/vectors/1101-E-0051.bin"
private noncomputable def ep1101_52 : Blocks := edgeBlocks% "full/vectors/1101-E-0052.bin"
private noncomputable def ep1101_53 : Blocks := edgeBlocks% "full/vectors/1101-E-0053.bin"
private noncomputable def ep1101_54 : Blocks := edgeBlocks% "full/vectors/1101-E-0054.bin"
private noncomputable def ep1101_55 : Blocks := edgeBlocks% "full/vectors/1101-E-0055.bin"
private noncomputable def ep1101_56 : Blocks := edgeBlocks% "full/vectors/1101-E-0056.bin"
private noncomputable def ep1101_57 : Blocks := edgeBlocks% "full/vectors/1101-E-0057.bin"
private noncomputable def ep1101_58 : Blocks := edgeBlocks% "full/vectors/1101-E-0058.bin"
private noncomputable def ep1101_59 : Blocks := edgeBlocks% "full/vectors/1101-E-0059.bin"
private noncomputable def ep1101_60 : Blocks := edgeBlocks% "full/vectors/1101-E-0060.bin"
private noncomputable def ep1101_61 : Blocks := edgeBlocks% "full/vectors/1101-E-0061.bin"
private noncomputable def ep1101_62 : Blocks := edgeBlocks% "full/vectors/1101-E-0062.bin"
private noncomputable def ep1101_63 : Blocks := edgeBlocks% "full/vectors/1101-E-0063.bin"
private noncomputable def ep1101_64 : Blocks := edgeBlocks% "full/vectors/1101-E-0064.bin"
private noncomputable def ep1101_65 : Blocks := edgeBlocks% "full/vectors/1101-E-0065.bin"
private noncomputable def ep1101_66 : Blocks := edgeBlocks% "full/vectors/1101-E-0066.bin"
private noncomputable def ep1101_67 : Blocks := edgeBlocks% "full/vectors/1101-E-0067.bin"
private noncomputable def ep1101_68 : Blocks := edgeBlocks% "full/vectors/1101-E-0068.bin"
private noncomputable def ep1101_69 : Blocks := edgeBlocks% "full/vectors/1101-E-0069.bin"
private noncomputable def ep1101_70 : Blocks := edgeBlocks% "full/vectors/1101-E-0070.bin"
private noncomputable def ep1101_71 : Blocks := edgeBlocks% "full/vectors/1101-E-0071.bin"
private noncomputable def ep1101_72 : Blocks := edgeBlocks% "full/vectors/1101-E-0072.bin"
private noncomputable def ep1101_73 : Blocks := edgeBlocks% "full/vectors/1101-E-0073.bin"
private noncomputable def ep1101_74 : Blocks := edgeBlocks% "full/vectors/1101-E-0074.bin"
private noncomputable def ep1101_75 : Blocks := edgeBlocks% "full/vectors/1101-E-0075.bin"
private noncomputable def ep1101_76 : Blocks := edgeBlocks% "full/vectors/1101-E-0076.bin"
private noncomputable def ep1101_77 : Blocks := edgeBlocks% "full/vectors/1101-E-0077.bin"
noncomputable def ep1101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1101_0 ep1101_1) (Blocks.join ep1101_2 ep1101_3)) (Blocks.join (Blocks.join ep1101_4 ep1101_5) (Blocks.join ep1101_6 (Blocks.join ep1101_7 ep1101_8)))) (Blocks.join (Blocks.join (Blocks.join ep1101_9 ep1101_10) (Blocks.join ep1101_11 (Blocks.join ep1101_12 ep1101_13))) (Blocks.join (Blocks.join ep1101_14 ep1101_15) (Blocks.join ep1101_16 (Blocks.join ep1101_17 ep1101_18))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1101_19 ep1101_20) (Blocks.join ep1101_21 (Blocks.join ep1101_22 ep1101_23))) (Blocks.join (Blocks.join ep1101_24 ep1101_25) (Blocks.join ep1101_26 (Blocks.join ep1101_27 ep1101_28)))) (Blocks.join (Blocks.join (Blocks.join ep1101_29 ep1101_30) (Blocks.join ep1101_31 (Blocks.join ep1101_32 ep1101_33))) (Blocks.join (Blocks.join ep1101_34 ep1101_35) (Blocks.join ep1101_36 (Blocks.join ep1101_37 ep1101_38)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1101_39 ep1101_40) (Blocks.join ep1101_41 ep1101_42)) (Blocks.join (Blocks.join ep1101_43 ep1101_44) (Blocks.join ep1101_45 (Blocks.join ep1101_46 ep1101_47)))) (Blocks.join (Blocks.join (Blocks.join ep1101_48 ep1101_49) (Blocks.join ep1101_50 (Blocks.join ep1101_51 ep1101_52))) (Blocks.join (Blocks.join ep1101_53 ep1101_54) (Blocks.join ep1101_55 (Blocks.join ep1101_56 ep1101_57))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1101_58 ep1101_59) (Blocks.join ep1101_60 (Blocks.join ep1101_61 ep1101_62))) (Blocks.join (Blocks.join ep1101_63 ep1101_64) (Blocks.join ep1101_65 (Blocks.join ep1101_66 ep1101_67)))) (Blocks.join (Blocks.join (Blocks.join ep1101_68 ep1101_69) (Blocks.join ep1101_70 (Blocks.join ep1101_71 ep1101_72))) (Blocks.join (Blocks.join ep1101_73 ep1101_74) (Blocks.join ep1101_75 (Blocks.join ep1101_76 ep1101_77)))))))
private def ptsp1101 : List ℤ := [((2:ℤ)^1210+0),((2:ℤ)^1210+1),((2:ℤ)^1210+2),((2:ℤ)^1210+3),((2:ℤ)^1210+4),((2:ℤ)^1210+5),((2:ℤ)^1210+6),((2:ℤ)^1210+7),((2:ℤ)^1210+8),((2:ℤ)^1210+9),((2:ℤ)^1210+10),((2:ℤ)^1210+11),((2:ℤ)^1210+12),((2:ℤ)^1210+13)]
private theorem boundp1101 : 2^vp110.size*absSum vp110.list + ((2:ℤ)^12870*absSum vp1101.list+absSum ep1101.list) < (2:ℤ)^16373 := by decide +kernel
private theorem pointp1101_0 : fastHom 1 ((2:ℤ)^1210+0) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+0)+ep1101.subst ((2:ℤ)^1210+0) := by decide +kernel
private theorem pointp1101_1 : fastHom 1 ((2:ℤ)^1210+1) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+1)+ep1101.subst ((2:ℤ)^1210+1) := by decide +kernel
private theorem pointp1101_2 : fastHom 1 ((2:ℤ)^1210+2) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+2)+ep1101.subst ((2:ℤ)^1210+2) := by decide +kernel
private theorem pointp1101_3 : fastHom 1 ((2:ℤ)^1210+3) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+3)+ep1101.subst ((2:ℤ)^1210+3) := by decide +kernel
private theorem pointp1101_4 : fastHom 1 ((2:ℤ)^1210+4) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+4)+ep1101.subst ((2:ℤ)^1210+4) := by decide +kernel
private theorem pointp1101_5 : fastHom 1 ((2:ℤ)^1210+5) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+5)+ep1101.subst ((2:ℤ)^1210+5) := by decide +kernel
private theorem pointp1101_6 : fastHom 1 ((2:ℤ)^1210+6) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+6)+ep1101.subst ((2:ℤ)^1210+6) := by decide +kernel
private theorem pointp1101_7 : fastHom 1 ((2:ℤ)^1210+7) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+7)+ep1101.subst ((2:ℤ)^1210+7) := by decide +kernel
private theorem pointp1101_8 : fastHom 1 ((2:ℤ)^1210+8) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+8)+ep1101.subst ((2:ℤ)^1210+8) := by decide +kernel
private theorem pointp1101_9 : fastHom 1 ((2:ℤ)^1210+9) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+9)+ep1101.subst ((2:ℤ)^1210+9) := by decide +kernel
private theorem pointp1101_10 : fastHom 1 ((2:ℤ)^1210+10) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+10)+ep1101.subst ((2:ℤ)^1210+10) := by decide +kernel
private theorem pointp1101_11 : fastHom 1 ((2:ℤ)^1210+11) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+11)+ep1101.subst ((2:ℤ)^1210+11) := by decide +kernel
private theorem pointp1101_12 : fastHom 1 ((2:ℤ)^1210+12) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+12)+ep1101.subst ((2:ℤ)^1210+12) := by decide +kernel
private theorem pointp1101_13 : fastHom 1 ((2:ℤ)^1210+13) vp110 = ((2:ℤ)^12870)*vp1101.subst ((2:ℤ)^1210+13)+ep1101.subst ((2:ℤ)^1210+13) := by decide +kernel
private theorem checkp1101 (x:ℤ) (hx:x ∈ ptsp1101) : fastHom 1 x vp110 = ((2:ℤ)^12870)*vp1101.subst x+ep1101.subst x := by
  simp only [ptsp1101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp1101_0
  · exact pointp1101_1
  · exact pointp1101_2
  · exact pointp1101_3
  · exact pointp1101_4
  · exact pointp1101_5
  · exact pointp1101_6
  · exact pointp1101_7
  · exact pointp1101_8
  · exact pointp1101_9
  · exact pointp1101_10
  · exact pointp1101_11
  · exact pointp1101_12
  · exact pointp1101_13
private theorem idp1101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110.list =
    C ((2:ℤ)^12870) * horner X vp1101.list + horner X ep1101.list := by
  apply edge_identity (B := (2:ℤ)^16373) (by decide) (by positivity) (by positivity) boundp1101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp1101 (by decide +kernel)
  · have h : ptsp1101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp1101.trans_le (by decide +kernel)
  · exact checkp1101
private theorem bp1101 : Branch 1 (-6143761639/1024000000 : ℚ) vp110 := by
  apply branch_checked idp1101 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-6655761639/512000000 : ℚ) by norm_num]
  exact coverp1101
theorem coverp110 : Covers (-6143761639/1024000000 : ℚ) vp110 := join_branches bp1100 bp1101
end NextProof.EdgeFull

