import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00136
import NextProof.EdgeFull00137

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp101_0 : Blocks := edgeBlocks% "full/vectors/101-V-0000.bin"
private noncomputable def vp101_1 : Blocks := edgeBlocks% "full/vectors/101-V-0001.bin"
private noncomputable def vp101_2 : Blocks := edgeBlocks% "full/vectors/101-V-0002.bin"
private noncomputable def vp101_3 : Blocks := edgeBlocks% "full/vectors/101-V-0003.bin"
private noncomputable def vp101_4 : Blocks := edgeBlocks% "full/vectors/101-V-0004.bin"
private noncomputable def vp101_5 : Blocks := edgeBlocks% "full/vectors/101-V-0005.bin"
private noncomputable def vp101_6 : Blocks := edgeBlocks% "full/vectors/101-V-0006.bin"
private noncomputable def vp101_7 : Blocks := edgeBlocks% "full/vectors/101-V-0007.bin"
private noncomputable def vp101_8 : Blocks := edgeBlocks% "full/vectors/101-V-0008.bin"
private noncomputable def vp101_9 : Blocks := edgeBlocks% "full/vectors/101-V-0009.bin"
private noncomputable def vp101_10 : Blocks := edgeBlocks% "full/vectors/101-V-0010.bin"
private noncomputable def vp101_11 : Blocks := edgeBlocks% "full/vectors/101-V-0011.bin"
private noncomputable def vp101_12 : Blocks := edgeBlocks% "full/vectors/101-V-0012.bin"
private noncomputable def vp101_13 : Blocks := edgeBlocks% "full/vectors/101-V-0013.bin"
private noncomputable def vp101_14 : Blocks := edgeBlocks% "full/vectors/101-V-0014.bin"
private noncomputable def vp101_15 : Blocks := edgeBlocks% "full/vectors/101-V-0015.bin"
private noncomputable def vp101_16 : Blocks := edgeBlocks% "full/vectors/101-V-0016.bin"
private noncomputable def vp101_17 : Blocks := edgeBlocks% "full/vectors/101-V-0017.bin"
private noncomputable def vp101_18 : Blocks := edgeBlocks% "full/vectors/101-V-0018.bin"
private noncomputable def vp101_19 : Blocks := edgeBlocks% "full/vectors/101-V-0019.bin"
private noncomputable def vp101_20 : Blocks := edgeBlocks% "full/vectors/101-V-0020.bin"
private noncomputable def vp101_21 : Blocks := edgeBlocks% "full/vectors/101-V-0021.bin"
private noncomputable def vp101_22 : Blocks := edgeBlocks% "full/vectors/101-V-0022.bin"
private noncomputable def vp101_23 : Blocks := edgeBlocks% "full/vectors/101-V-0023.bin"
private noncomputable def vp101_24 : Blocks := edgeBlocks% "full/vectors/101-V-0024.bin"
private noncomputable def vp101_25 : Blocks := edgeBlocks% "full/vectors/101-V-0025.bin"
private noncomputable def vp101_26 : Blocks := edgeBlocks% "full/vectors/101-V-0026.bin"
private noncomputable def vp101_27 : Blocks := edgeBlocks% "full/vectors/101-V-0027.bin"
private noncomputable def vp101_28 : Blocks := edgeBlocks% "full/vectors/101-V-0028.bin"
private noncomputable def vp101_29 : Blocks := edgeBlocks% "full/vectors/101-V-0029.bin"
private noncomputable def vp101_30 : Blocks := edgeBlocks% "full/vectors/101-V-0030.bin"
private noncomputable def vp101_31 : Blocks := edgeBlocks% "full/vectors/101-V-0031.bin"
private noncomputable def vp101_32 : Blocks := edgeBlocks% "full/vectors/101-V-0032.bin"
private noncomputable def vp101_33 : Blocks := edgeBlocks% "full/vectors/101-V-0033.bin"
private noncomputable def vp101_34 : Blocks := edgeBlocks% "full/vectors/101-V-0034.bin"
private noncomputable def vp101_35 : Blocks := edgeBlocks% "full/vectors/101-V-0035.bin"
private noncomputable def vp101_36 : Blocks := edgeBlocks% "full/vectors/101-V-0036.bin"
private noncomputable def vp101_37 : Blocks := edgeBlocks% "full/vectors/101-V-0037.bin"
private noncomputable def vp101_38 : Blocks := edgeBlocks% "full/vectors/101-V-0038.bin"
private noncomputable def vp101_39 : Blocks := edgeBlocks% "full/vectors/101-V-0039.bin"
private noncomputable def vp101_40 : Blocks := edgeBlocks% "full/vectors/101-V-0040.bin"
private noncomputable def vp101_41 : Blocks := edgeBlocks% "full/vectors/101-V-0041.bin"
private noncomputable def vp101_42 : Blocks := edgeBlocks% "full/vectors/101-V-0042.bin"
private noncomputable def vp101_43 : Blocks := edgeBlocks% "full/vectors/101-V-0043.bin"
private noncomputable def vp101_44 : Blocks := edgeBlocks% "full/vectors/101-V-0044.bin"
private noncomputable def vp101_45 : Blocks := edgeBlocks% "full/vectors/101-V-0045.bin"
private noncomputable def vp101_46 : Blocks := edgeBlocks% "full/vectors/101-V-0046.bin"
private noncomputable def vp101_47 : Blocks := edgeBlocks% "full/vectors/101-V-0047.bin"
private noncomputable def vp101_48 : Blocks := edgeBlocks% "full/vectors/101-V-0048.bin"
private noncomputable def vp101_49 : Blocks := edgeBlocks% "full/vectors/101-V-0049.bin"
private noncomputable def vp101_50 : Blocks := edgeBlocks% "full/vectors/101-V-0050.bin"
private noncomputable def vp101_51 : Blocks := edgeBlocks% "full/vectors/101-V-0051.bin"
private noncomputable def vp101_52 : Blocks := edgeBlocks% "full/vectors/101-V-0052.bin"
private noncomputable def vp101_53 : Blocks := edgeBlocks% "full/vectors/101-V-0053.bin"
private noncomputable def vp101_54 : Blocks := edgeBlocks% "full/vectors/101-V-0054.bin"
private noncomputable def vp101_55 : Blocks := edgeBlocks% "full/vectors/101-V-0055.bin"
private noncomputable def vp101_56 : Blocks := edgeBlocks% "full/vectors/101-V-0056.bin"
private noncomputable def vp101_57 : Blocks := edgeBlocks% "full/vectors/101-V-0057.bin"
private noncomputable def vp101_58 : Blocks := edgeBlocks% "full/vectors/101-V-0058.bin"
private noncomputable def vp101_59 : Blocks := edgeBlocks% "full/vectors/101-V-0059.bin"
private noncomputable def vp101_60 : Blocks := edgeBlocks% "full/vectors/101-V-0060.bin"
private noncomputable def vp101_61 : Blocks := edgeBlocks% "full/vectors/101-V-0061.bin"
private noncomputable def vp101_62 : Blocks := edgeBlocks% "full/vectors/101-V-0062.bin"
private noncomputable def vp101_63 : Blocks := edgeBlocks% "full/vectors/101-V-0063.bin"
private noncomputable def vp101_64 : Blocks := edgeBlocks% "full/vectors/101-V-0064.bin"
private noncomputable def vp101_65 : Blocks := edgeBlocks% "full/vectors/101-V-0065.bin"
private noncomputable def vp101_66 : Blocks := edgeBlocks% "full/vectors/101-V-0066.bin"
private noncomputable def vp101_67 : Blocks := edgeBlocks% "full/vectors/101-V-0067.bin"
private noncomputable def vp101_68 : Blocks := edgeBlocks% "full/vectors/101-V-0068.bin"
private noncomputable def vp101_69 : Blocks := edgeBlocks% "full/vectors/101-V-0069.bin"
private noncomputable def vp101_70 : Blocks := edgeBlocks% "full/vectors/101-V-0070.bin"
private noncomputable def vp101_71 : Blocks := edgeBlocks% "full/vectors/101-V-0071.bin"
private noncomputable def vp101_72 : Blocks := edgeBlocks% "full/vectors/101-V-0072.bin"
private noncomputable def vp101_73 : Blocks := edgeBlocks% "full/vectors/101-V-0073.bin"
private noncomputable def vp101_74 : Blocks := edgeBlocks% "full/vectors/101-V-0074.bin"
private noncomputable def vp101_75 : Blocks := edgeBlocks% "full/vectors/101-V-0075.bin"
private noncomputable def vp101_76 : Blocks := edgeBlocks% "full/vectors/101-V-0076.bin"
private noncomputable def vp101_77 : Blocks := edgeBlocks% "full/vectors/101-V-0077.bin"
private noncomputable def vp101_78 : Blocks := edgeBlocks% "full/vectors/101-V-0078.bin"
private noncomputable def vp101_79 : Blocks := edgeBlocks% "full/vectors/101-V-0079.bin"
private noncomputable def vp101_80 : Blocks := edgeBlocks% "full/vectors/101-V-0080.bin"
private noncomputable def vp101_81 : Blocks := edgeBlocks% "full/vectors/101-V-0081.bin"
private noncomputable def vp101_82 : Blocks := edgeBlocks% "full/vectors/101-V-0082.bin"
private noncomputable def vp101_83 : Blocks := edgeBlocks% "full/vectors/101-V-0083.bin"
private noncomputable def vp101_84 : Blocks := edgeBlocks% "full/vectors/101-V-0084.bin"
private noncomputable def vp101_85 : Blocks := edgeBlocks% "full/vectors/101-V-0085.bin"
private noncomputable def vp101_86 : Blocks := edgeBlocks% "full/vectors/101-V-0086.bin"
private noncomputable def vp101_87 : Blocks := edgeBlocks% "full/vectors/101-V-0087.bin"
noncomputable def vp101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp101_0 vp101_1) (Blocks.join vp101_2 (Blocks.join vp101_3 vp101_4))) (Blocks.join (Blocks.join vp101_5 (Blocks.join vp101_6 vp101_7)) (Blocks.join vp101_8 (Blocks.join vp101_9 vp101_10)))) (Blocks.join (Blocks.join (Blocks.join vp101_11 vp101_12) (Blocks.join vp101_13 (Blocks.join vp101_14 vp101_15))) (Blocks.join (Blocks.join vp101_16 (Blocks.join vp101_17 vp101_18)) (Blocks.join vp101_19 (Blocks.join vp101_20 vp101_21))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp101_22 vp101_23) (Blocks.join vp101_24 (Blocks.join vp101_25 vp101_26))) (Blocks.join (Blocks.join vp101_27 (Blocks.join vp101_28 vp101_29)) (Blocks.join vp101_30 (Blocks.join vp101_31 vp101_32)))) (Blocks.join (Blocks.join (Blocks.join vp101_33 vp101_34) (Blocks.join vp101_35 (Blocks.join vp101_36 vp101_37))) (Blocks.join (Blocks.join vp101_38 (Blocks.join vp101_39 vp101_40)) (Blocks.join vp101_41 (Blocks.join vp101_42 vp101_43)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp101_44 vp101_45) (Blocks.join vp101_46 (Blocks.join vp101_47 vp101_48))) (Blocks.join (Blocks.join vp101_49 (Blocks.join vp101_50 vp101_51)) (Blocks.join vp101_52 (Blocks.join vp101_53 vp101_54)))) (Blocks.join (Blocks.join (Blocks.join vp101_55 vp101_56) (Blocks.join vp101_57 (Blocks.join vp101_58 vp101_59))) (Blocks.join (Blocks.join vp101_60 (Blocks.join vp101_61 vp101_62)) (Blocks.join vp101_63 (Blocks.join vp101_64 vp101_65))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp101_66 vp101_67) (Blocks.join vp101_68 (Blocks.join vp101_69 vp101_70))) (Blocks.join (Blocks.join vp101_71 (Blocks.join vp101_72 vp101_73)) (Blocks.join vp101_74 (Blocks.join vp101_75 vp101_76)))) (Blocks.join (Blocks.join (Blocks.join vp101_77 vp101_78) (Blocks.join vp101_79 (Blocks.join vp101_80 vp101_81))) (Blocks.join (Blocks.join vp101_82 (Blocks.join vp101_83 vp101_84)) (Blocks.join vp101_85 (Blocks.join vp101_86 vp101_87)))))))
private theorem bp1010 : Branch 0 (-5119761639/1024000000 : ℚ) vp101 := by
  apply branch_left_normalized (c:=vp1010) (k:=0) (m:=6318) (by decide +kernel)
  rw [show 2*(-5119761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/512000000 : ℚ) by norm_num]
  exact coverp1010
private noncomputable def ep1011_0 : Blocks := edgeBlocks% "full/vectors/1011-E-0000.bin"
private noncomputable def ep1011_1 : Blocks := edgeBlocks% "full/vectors/1011-E-0001.bin"
private noncomputable def ep1011_2 : Blocks := edgeBlocks% "full/vectors/1011-E-0002.bin"
private noncomputable def ep1011_3 : Blocks := edgeBlocks% "full/vectors/1011-E-0003.bin"
private noncomputable def ep1011_4 : Blocks := edgeBlocks% "full/vectors/1011-E-0004.bin"
private noncomputable def ep1011_5 : Blocks := edgeBlocks% "full/vectors/1011-E-0005.bin"
private noncomputable def ep1011_6 : Blocks := edgeBlocks% "full/vectors/1011-E-0006.bin"
private noncomputable def ep1011_7 : Blocks := edgeBlocks% "full/vectors/1011-E-0007.bin"
private noncomputable def ep1011_8 : Blocks := edgeBlocks% "full/vectors/1011-E-0008.bin"
private noncomputable def ep1011_9 : Blocks := edgeBlocks% "full/vectors/1011-E-0009.bin"
private noncomputable def ep1011_10 : Blocks := edgeBlocks% "full/vectors/1011-E-0010.bin"
private noncomputable def ep1011_11 : Blocks := edgeBlocks% "full/vectors/1011-E-0011.bin"
private noncomputable def ep1011_12 : Blocks := edgeBlocks% "full/vectors/1011-E-0012.bin"
private noncomputable def ep1011_13 : Blocks := edgeBlocks% "full/vectors/1011-E-0013.bin"
private noncomputable def ep1011_14 : Blocks := edgeBlocks% "full/vectors/1011-E-0014.bin"
private noncomputable def ep1011_15 : Blocks := edgeBlocks% "full/vectors/1011-E-0015.bin"
private noncomputable def ep1011_16 : Blocks := edgeBlocks% "full/vectors/1011-E-0016.bin"
private noncomputable def ep1011_17 : Blocks := edgeBlocks% "full/vectors/1011-E-0017.bin"
private noncomputable def ep1011_18 : Blocks := edgeBlocks% "full/vectors/1011-E-0018.bin"
private noncomputable def ep1011_19 : Blocks := edgeBlocks% "full/vectors/1011-E-0019.bin"
private noncomputable def ep1011_20 : Blocks := edgeBlocks% "full/vectors/1011-E-0020.bin"
private noncomputable def ep1011_21 : Blocks := edgeBlocks% "full/vectors/1011-E-0021.bin"
private noncomputable def ep1011_22 : Blocks := edgeBlocks% "full/vectors/1011-E-0022.bin"
private noncomputable def ep1011_23 : Blocks := edgeBlocks% "full/vectors/1011-E-0023.bin"
private noncomputable def ep1011_24 : Blocks := edgeBlocks% "full/vectors/1011-E-0024.bin"
private noncomputable def ep1011_25 : Blocks := edgeBlocks% "full/vectors/1011-E-0025.bin"
private noncomputable def ep1011_26 : Blocks := edgeBlocks% "full/vectors/1011-E-0026.bin"
private noncomputable def ep1011_27 : Blocks := edgeBlocks% "full/vectors/1011-E-0027.bin"
private noncomputable def ep1011_28 : Blocks := edgeBlocks% "full/vectors/1011-E-0028.bin"
private noncomputable def ep1011_29 : Blocks := edgeBlocks% "full/vectors/1011-E-0029.bin"
private noncomputable def ep1011_30 : Blocks := edgeBlocks% "full/vectors/1011-E-0030.bin"
private noncomputable def ep1011_31 : Blocks := edgeBlocks% "full/vectors/1011-E-0031.bin"
private noncomputable def ep1011_32 : Blocks := edgeBlocks% "full/vectors/1011-E-0032.bin"
private noncomputable def ep1011_33 : Blocks := edgeBlocks% "full/vectors/1011-E-0033.bin"
private noncomputable def ep1011_34 : Blocks := edgeBlocks% "full/vectors/1011-E-0034.bin"
private noncomputable def ep1011_35 : Blocks := edgeBlocks% "full/vectors/1011-E-0035.bin"
private noncomputable def ep1011_36 : Blocks := edgeBlocks% "full/vectors/1011-E-0036.bin"
private noncomputable def ep1011_37 : Blocks := edgeBlocks% "full/vectors/1011-E-0037.bin"
private noncomputable def ep1011_38 : Blocks := edgeBlocks% "full/vectors/1011-E-0038.bin"
private noncomputable def ep1011_39 : Blocks := edgeBlocks% "full/vectors/1011-E-0039.bin"
private noncomputable def ep1011_40 : Blocks := edgeBlocks% "full/vectors/1011-E-0040.bin"
private noncomputable def ep1011_41 : Blocks := edgeBlocks% "full/vectors/1011-E-0041.bin"
private noncomputable def ep1011_42 : Blocks := edgeBlocks% "full/vectors/1011-E-0042.bin"
private noncomputable def ep1011_43 : Blocks := edgeBlocks% "full/vectors/1011-E-0043.bin"
private noncomputable def ep1011_44 : Blocks := edgeBlocks% "full/vectors/1011-E-0044.bin"
private noncomputable def ep1011_45 : Blocks := edgeBlocks% "full/vectors/1011-E-0045.bin"
private noncomputable def ep1011_46 : Blocks := edgeBlocks% "full/vectors/1011-E-0046.bin"
private noncomputable def ep1011_47 : Blocks := edgeBlocks% "full/vectors/1011-E-0047.bin"
private noncomputable def ep1011_48 : Blocks := edgeBlocks% "full/vectors/1011-E-0048.bin"
private noncomputable def ep1011_49 : Blocks := edgeBlocks% "full/vectors/1011-E-0049.bin"
private noncomputable def ep1011_50 : Blocks := edgeBlocks% "full/vectors/1011-E-0050.bin"
private noncomputable def ep1011_51 : Blocks := edgeBlocks% "full/vectors/1011-E-0051.bin"
private noncomputable def ep1011_52 : Blocks := edgeBlocks% "full/vectors/1011-E-0052.bin"
private noncomputable def ep1011_53 : Blocks := edgeBlocks% "full/vectors/1011-E-0053.bin"
private noncomputable def ep1011_54 : Blocks := edgeBlocks% "full/vectors/1011-E-0054.bin"
private noncomputable def ep1011_55 : Blocks := edgeBlocks% "full/vectors/1011-E-0055.bin"
private noncomputable def ep1011_56 : Blocks := edgeBlocks% "full/vectors/1011-E-0056.bin"
private noncomputable def ep1011_57 : Blocks := edgeBlocks% "full/vectors/1011-E-0057.bin"
private noncomputable def ep1011_58 : Blocks := edgeBlocks% "full/vectors/1011-E-0058.bin"
private noncomputable def ep1011_59 : Blocks := edgeBlocks% "full/vectors/1011-E-0059.bin"
private noncomputable def ep1011_60 : Blocks := edgeBlocks% "full/vectors/1011-E-0060.bin"
private noncomputable def ep1011_61 : Blocks := edgeBlocks% "full/vectors/1011-E-0061.bin"
private noncomputable def ep1011_62 : Blocks := edgeBlocks% "full/vectors/1011-E-0062.bin"
private noncomputable def ep1011_63 : Blocks := edgeBlocks% "full/vectors/1011-E-0063.bin"
private noncomputable def ep1011_64 : Blocks := edgeBlocks% "full/vectors/1011-E-0064.bin"
private noncomputable def ep1011_65 : Blocks := edgeBlocks% "full/vectors/1011-E-0065.bin"
private noncomputable def ep1011_66 : Blocks := edgeBlocks% "full/vectors/1011-E-0066.bin"
private noncomputable def ep1011_67 : Blocks := edgeBlocks% "full/vectors/1011-E-0067.bin"
private noncomputable def ep1011_68 : Blocks := edgeBlocks% "full/vectors/1011-E-0068.bin"
private noncomputable def ep1011_69 : Blocks := edgeBlocks% "full/vectors/1011-E-0069.bin"
private noncomputable def ep1011_70 : Blocks := edgeBlocks% "full/vectors/1011-E-0070.bin"
private noncomputable def ep1011_71 : Blocks := edgeBlocks% "full/vectors/1011-E-0071.bin"
private noncomputable def ep1011_72 : Blocks := edgeBlocks% "full/vectors/1011-E-0072.bin"
private noncomputable def ep1011_73 : Blocks := edgeBlocks% "full/vectors/1011-E-0073.bin"
private noncomputable def ep1011_74 : Blocks := edgeBlocks% "full/vectors/1011-E-0074.bin"
private noncomputable def ep1011_75 : Blocks := edgeBlocks% "full/vectors/1011-E-0075.bin"
private noncomputable def ep1011_76 : Blocks := edgeBlocks% "full/vectors/1011-E-0076.bin"
private noncomputable def ep1011_77 : Blocks := edgeBlocks% "full/vectors/1011-E-0077.bin"
private noncomputable def ep1011_78 : Blocks := edgeBlocks% "full/vectors/1011-E-0078.bin"
private noncomputable def ep1011_79 : Blocks := edgeBlocks% "full/vectors/1011-E-0079.bin"
private noncomputable def ep1011_80 : Blocks := edgeBlocks% "full/vectors/1011-E-0080.bin"
private noncomputable def ep1011_81 : Blocks := edgeBlocks% "full/vectors/1011-E-0081.bin"
private noncomputable def ep1011_82 : Blocks := edgeBlocks% "full/vectors/1011-E-0082.bin"
private noncomputable def ep1011_83 : Blocks := edgeBlocks% "full/vectors/1011-E-0083.bin"
private noncomputable def ep1011_84 : Blocks := edgeBlocks% "full/vectors/1011-E-0084.bin"
private noncomputable def ep1011_85 : Blocks := edgeBlocks% "full/vectors/1011-E-0085.bin"
private noncomputable def ep1011_86 : Blocks := edgeBlocks% "full/vectors/1011-E-0086.bin"
private noncomputable def ep1011_87 : Blocks := edgeBlocks% "full/vectors/1011-E-0087.bin"
noncomputable def ep1011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1011_0 ep1011_1) (Blocks.join ep1011_2 (Blocks.join ep1011_3 ep1011_4))) (Blocks.join (Blocks.join ep1011_5 (Blocks.join ep1011_6 ep1011_7)) (Blocks.join ep1011_8 (Blocks.join ep1011_9 ep1011_10)))) (Blocks.join (Blocks.join (Blocks.join ep1011_11 ep1011_12) (Blocks.join ep1011_13 (Blocks.join ep1011_14 ep1011_15))) (Blocks.join (Blocks.join ep1011_16 (Blocks.join ep1011_17 ep1011_18)) (Blocks.join ep1011_19 (Blocks.join ep1011_20 ep1011_21))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1011_22 ep1011_23) (Blocks.join ep1011_24 (Blocks.join ep1011_25 ep1011_26))) (Blocks.join (Blocks.join ep1011_27 (Blocks.join ep1011_28 ep1011_29)) (Blocks.join ep1011_30 (Blocks.join ep1011_31 ep1011_32)))) (Blocks.join (Blocks.join (Blocks.join ep1011_33 ep1011_34) (Blocks.join ep1011_35 (Blocks.join ep1011_36 ep1011_37))) (Blocks.join (Blocks.join ep1011_38 (Blocks.join ep1011_39 ep1011_40)) (Blocks.join ep1011_41 (Blocks.join ep1011_42 ep1011_43)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1011_44 ep1011_45) (Blocks.join ep1011_46 (Blocks.join ep1011_47 ep1011_48))) (Blocks.join (Blocks.join ep1011_49 (Blocks.join ep1011_50 ep1011_51)) (Blocks.join ep1011_52 (Blocks.join ep1011_53 ep1011_54)))) (Blocks.join (Blocks.join (Blocks.join ep1011_55 ep1011_56) (Blocks.join ep1011_57 (Blocks.join ep1011_58 ep1011_59))) (Blocks.join (Blocks.join ep1011_60 (Blocks.join ep1011_61 ep1011_62)) (Blocks.join ep1011_63 (Blocks.join ep1011_64 ep1011_65))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1011_66 ep1011_67) (Blocks.join ep1011_68 (Blocks.join ep1011_69 ep1011_70))) (Blocks.join (Blocks.join ep1011_71 (Blocks.join ep1011_72 ep1011_73)) (Blocks.join ep1011_74 (Blocks.join ep1011_75 ep1011_76)))) (Blocks.join (Blocks.join (Blocks.join ep1011_77 ep1011_78) (Blocks.join ep1011_79 (Blocks.join ep1011_80 ep1011_81))) (Blocks.join (Blocks.join ep1011_82 (Blocks.join ep1011_83 ep1011_84)) (Blocks.join ep1011_85 (Blocks.join ep1011_86 ep1011_87)))))))
private def ptsp1011 : List ℤ := [((2:ℤ)^1076+0),((2:ℤ)^1076+1),((2:ℤ)^1076+2),((2:ℤ)^1076+3),((2:ℤ)^1076+4),((2:ℤ)^1076+5),((2:ℤ)^1076+6),((2:ℤ)^1076+7),((2:ℤ)^1076+8),((2:ℤ)^1076+9),((2:ℤ)^1076+10),((2:ℤ)^1076+11),((2:ℤ)^1076+12),((2:ℤ)^1076+13),((2:ℤ)^1076+14),((2:ℤ)^1076+15),((2:ℤ)^1076+16)]
private theorem boundp1011 : 2^vp101.size*absSum vp101.list + ((2:ℤ)^14107*absSum vp1011.list+absSum ep1011.list) < (2:ℤ)^18169 := by decide +kernel
private theorem pointp1011_0 : fastHom 1 ((2:ℤ)^1076+0) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+0)+ep1011.subst ((2:ℤ)^1076+0) := by decide +kernel
private theorem pointp1011_1 : fastHom 1 ((2:ℤ)^1076+1) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+1)+ep1011.subst ((2:ℤ)^1076+1) := by decide +kernel
private theorem pointp1011_2 : fastHom 1 ((2:ℤ)^1076+2) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+2)+ep1011.subst ((2:ℤ)^1076+2) := by decide +kernel
private theorem pointp1011_3 : fastHom 1 ((2:ℤ)^1076+3) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+3)+ep1011.subst ((2:ℤ)^1076+3) := by decide +kernel
private theorem pointp1011_4 : fastHom 1 ((2:ℤ)^1076+4) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+4)+ep1011.subst ((2:ℤ)^1076+4) := by decide +kernel
private theorem pointp1011_5 : fastHom 1 ((2:ℤ)^1076+5) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+5)+ep1011.subst ((2:ℤ)^1076+5) := by decide +kernel
private theorem pointp1011_6 : fastHom 1 ((2:ℤ)^1076+6) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+6)+ep1011.subst ((2:ℤ)^1076+6) := by decide +kernel
private theorem pointp1011_7 : fastHom 1 ((2:ℤ)^1076+7) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+7)+ep1011.subst ((2:ℤ)^1076+7) := by decide +kernel
private theorem pointp1011_8 : fastHom 1 ((2:ℤ)^1076+8) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+8)+ep1011.subst ((2:ℤ)^1076+8) := by decide +kernel
private theorem pointp1011_9 : fastHom 1 ((2:ℤ)^1076+9) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+9)+ep1011.subst ((2:ℤ)^1076+9) := by decide +kernel
private theorem pointp1011_10 : fastHom 1 ((2:ℤ)^1076+10) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+10)+ep1011.subst ((2:ℤ)^1076+10) := by decide +kernel
private theorem pointp1011_11 : fastHom 1 ((2:ℤ)^1076+11) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+11)+ep1011.subst ((2:ℤ)^1076+11) := by decide +kernel
private theorem pointp1011_12 : fastHom 1 ((2:ℤ)^1076+12) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+12)+ep1011.subst ((2:ℤ)^1076+12) := by decide +kernel
private theorem pointp1011_13 : fastHom 1 ((2:ℤ)^1076+13) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+13)+ep1011.subst ((2:ℤ)^1076+13) := by decide +kernel
private theorem pointp1011_14 : fastHom 1 ((2:ℤ)^1076+14) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+14)+ep1011.subst ((2:ℤ)^1076+14) := by decide +kernel
private theorem pointp1011_15 : fastHom 1 ((2:ℤ)^1076+15) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+15)+ep1011.subst ((2:ℤ)^1076+15) := by decide +kernel
private theorem pointp1011_16 : fastHom 1 ((2:ℤ)^1076+16) vp101 = ((2:ℤ)^14107)*vp1011.subst ((2:ℤ)^1076+16)+ep1011.subst ((2:ℤ)^1076+16) := by decide +kernel
private theorem checkp1011 (x:ℤ) (hx:x ∈ ptsp1011) : fastHom 1 x vp101 = ((2:ℤ)^14107)*vp1011.subst x+ep1011.subst x := by
  simp only [ptsp1011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp1011_0
  · exact pointp1011_1
  · exact pointp1011_2
  · exact pointp1011_3
  · exact pointp1011_4
  · exact pointp1011_5
  · exact pointp1011_6
  · exact pointp1011_7
  · exact pointp1011_8
  · exact pointp1011_9
  · exact pointp1011_10
  · exact pointp1011_11
  · exact pointp1011_12
  · exact pointp1011_13
  · exact pointp1011_14
  · exact pointp1011_15
  · exact pointp1011_16
private theorem idp1011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101.list =
    C ((2:ℤ)^14107) * horner X vp1011.list + horner X ep1011.list := by
  apply edge_identity (B := (2:ℤ)^18169) (by decide) (by positivity) (by positivity) boundp1011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp1011 (by decide +kernel)
  · have h : ptsp1011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp1011.trans_le (by decide +kernel)
  · exact checkp1011
private theorem bp1011 : Branch 1 (-5119761639/1024000000 : ℚ) vp101 := by
  apply branch_checked idp1011 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-5631761639/512000000 : ℚ) by norm_num]
  exact coverp1011
theorem coverp101 : Covers (-5119761639/1024000000 : ℚ) vp101 := join_branches bp1010 bp1011
end NextProof.EdgeFull

