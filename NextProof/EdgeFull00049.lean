import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00043
import NextProof.EdgeFull00048

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001_0 : Blocks := edgeBlocks% "full/vectors/000001-V-0000.bin"
private noncomputable def vp000001_1 : Blocks := edgeBlocks% "full/vectors/000001-V-0001.bin"
private noncomputable def vp000001_2 : Blocks := edgeBlocks% "full/vectors/000001-V-0002.bin"
private noncomputable def vp000001_3 : Blocks := edgeBlocks% "full/vectors/000001-V-0003.bin"
private noncomputable def vp000001_4 : Blocks := edgeBlocks% "full/vectors/000001-V-0004.bin"
private noncomputable def vp000001_5 : Blocks := edgeBlocks% "full/vectors/000001-V-0005.bin"
private noncomputable def vp000001_6 : Blocks := edgeBlocks% "full/vectors/000001-V-0006.bin"
private noncomputable def vp000001_7 : Blocks := edgeBlocks% "full/vectors/000001-V-0007.bin"
private noncomputable def vp000001_8 : Blocks := edgeBlocks% "full/vectors/000001-V-0008.bin"
private noncomputable def vp000001_9 : Blocks := edgeBlocks% "full/vectors/000001-V-0009.bin"
private noncomputable def vp000001_10 : Blocks := edgeBlocks% "full/vectors/000001-V-0010.bin"
private noncomputable def vp000001_11 : Blocks := edgeBlocks% "full/vectors/000001-V-0011.bin"
private noncomputable def vp000001_12 : Blocks := edgeBlocks% "full/vectors/000001-V-0012.bin"
private noncomputable def vp000001_13 : Blocks := edgeBlocks% "full/vectors/000001-V-0013.bin"
private noncomputable def vp000001_14 : Blocks := edgeBlocks% "full/vectors/000001-V-0014.bin"
private noncomputable def vp000001_15 : Blocks := edgeBlocks% "full/vectors/000001-V-0015.bin"
private noncomputable def vp000001_16 : Blocks := edgeBlocks% "full/vectors/000001-V-0016.bin"
private noncomputable def vp000001_17 : Blocks := edgeBlocks% "full/vectors/000001-V-0017.bin"
private noncomputable def vp000001_18 : Blocks := edgeBlocks% "full/vectors/000001-V-0018.bin"
private noncomputable def vp000001_19 : Blocks := edgeBlocks% "full/vectors/000001-V-0019.bin"
private noncomputable def vp000001_20 : Blocks := edgeBlocks% "full/vectors/000001-V-0020.bin"
private noncomputable def vp000001_21 : Blocks := edgeBlocks% "full/vectors/000001-V-0021.bin"
private noncomputable def vp000001_22 : Blocks := edgeBlocks% "full/vectors/000001-V-0022.bin"
private noncomputable def vp000001_23 : Blocks := edgeBlocks% "full/vectors/000001-V-0023.bin"
private noncomputable def vp000001_24 : Blocks := edgeBlocks% "full/vectors/000001-V-0024.bin"
private noncomputable def vp000001_25 : Blocks := edgeBlocks% "full/vectors/000001-V-0025.bin"
private noncomputable def vp000001_26 : Blocks := edgeBlocks% "full/vectors/000001-V-0026.bin"
private noncomputable def vp000001_27 : Blocks := edgeBlocks% "full/vectors/000001-V-0027.bin"
private noncomputable def vp000001_28 : Blocks := edgeBlocks% "full/vectors/000001-V-0028.bin"
private noncomputable def vp000001_29 : Blocks := edgeBlocks% "full/vectors/000001-V-0029.bin"
private noncomputable def vp000001_30 : Blocks := edgeBlocks% "full/vectors/000001-V-0030.bin"
private noncomputable def vp000001_31 : Blocks := edgeBlocks% "full/vectors/000001-V-0031.bin"
private noncomputable def vp000001_32 : Blocks := edgeBlocks% "full/vectors/000001-V-0032.bin"
private noncomputable def vp000001_33 : Blocks := edgeBlocks% "full/vectors/000001-V-0033.bin"
private noncomputable def vp000001_34 : Blocks := edgeBlocks% "full/vectors/000001-V-0034.bin"
private noncomputable def vp000001_35 : Blocks := edgeBlocks% "full/vectors/000001-V-0035.bin"
private noncomputable def vp000001_36 : Blocks := edgeBlocks% "full/vectors/000001-V-0036.bin"
private noncomputable def vp000001_37 : Blocks := edgeBlocks% "full/vectors/000001-V-0037.bin"
private noncomputable def vp000001_38 : Blocks := edgeBlocks% "full/vectors/000001-V-0038.bin"
private noncomputable def vp000001_39 : Blocks := edgeBlocks% "full/vectors/000001-V-0039.bin"
private noncomputable def vp000001_40 : Blocks := edgeBlocks% "full/vectors/000001-V-0040.bin"
private noncomputable def vp000001_41 : Blocks := edgeBlocks% "full/vectors/000001-V-0041.bin"
private noncomputable def vp000001_42 : Blocks := edgeBlocks% "full/vectors/000001-V-0042.bin"
private noncomputable def vp000001_43 : Blocks := edgeBlocks% "full/vectors/000001-V-0043.bin"
private noncomputable def vp000001_44 : Blocks := edgeBlocks% "full/vectors/000001-V-0044.bin"
private noncomputable def vp000001_45 : Blocks := edgeBlocks% "full/vectors/000001-V-0045.bin"
private noncomputable def vp000001_46 : Blocks := edgeBlocks% "full/vectors/000001-V-0046.bin"
private noncomputable def vp000001_47 : Blocks := edgeBlocks% "full/vectors/000001-V-0047.bin"
private noncomputable def vp000001_48 : Blocks := edgeBlocks% "full/vectors/000001-V-0048.bin"
private noncomputable def vp000001_49 : Blocks := edgeBlocks% "full/vectors/000001-V-0049.bin"
private noncomputable def vp000001_50 : Blocks := edgeBlocks% "full/vectors/000001-V-0050.bin"
private noncomputable def vp000001_51 : Blocks := edgeBlocks% "full/vectors/000001-V-0051.bin"
private noncomputable def vp000001_52 : Blocks := edgeBlocks% "full/vectors/000001-V-0052.bin"
private noncomputable def vp000001_53 : Blocks := edgeBlocks% "full/vectors/000001-V-0053.bin"
private noncomputable def vp000001_54 : Blocks := edgeBlocks% "full/vectors/000001-V-0054.bin"
private noncomputable def vp000001_55 : Blocks := edgeBlocks% "full/vectors/000001-V-0055.bin"
private noncomputable def vp000001_56 : Blocks := edgeBlocks% "full/vectors/000001-V-0056.bin"
private noncomputable def vp000001_57 : Blocks := edgeBlocks% "full/vectors/000001-V-0057.bin"
private noncomputable def vp000001_58 : Blocks := edgeBlocks% "full/vectors/000001-V-0058.bin"
private noncomputable def vp000001_59 : Blocks := edgeBlocks% "full/vectors/000001-V-0059.bin"
private noncomputable def vp000001_60 : Blocks := edgeBlocks% "full/vectors/000001-V-0060.bin"
private noncomputable def vp000001_61 : Blocks := edgeBlocks% "full/vectors/000001-V-0061.bin"
private noncomputable def vp000001_62 : Blocks := edgeBlocks% "full/vectors/000001-V-0062.bin"
private noncomputable def vp000001_63 : Blocks := edgeBlocks% "full/vectors/000001-V-0063.bin"
private noncomputable def vp000001_64 : Blocks := edgeBlocks% "full/vectors/000001-V-0064.bin"
private noncomputable def vp000001_65 : Blocks := edgeBlocks% "full/vectors/000001-V-0065.bin"
private noncomputable def vp000001_66 : Blocks := edgeBlocks% "full/vectors/000001-V-0066.bin"
private noncomputable def vp000001_67 : Blocks := edgeBlocks% "full/vectors/000001-V-0067.bin"
noncomputable def vp000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000001_0 vp000001_1) (Blocks.join vp000001_2 vp000001_3)) (Blocks.join (Blocks.join vp000001_4 vp000001_5) (Blocks.join vp000001_6 vp000001_7))) (Blocks.join (Blocks.join (Blocks.join vp000001_8 vp000001_9) (Blocks.join vp000001_10 vp000001_11)) (Blocks.join (Blocks.join vp000001_12 vp000001_13) (Blocks.join vp000001_14 (Blocks.join vp000001_15 vp000001_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000001_17 vp000001_18) (Blocks.join vp000001_19 vp000001_20)) (Blocks.join (Blocks.join vp000001_21 vp000001_22) (Blocks.join vp000001_23 vp000001_24))) (Blocks.join (Blocks.join (Blocks.join vp000001_25 vp000001_26) (Blocks.join vp000001_27 vp000001_28)) (Blocks.join (Blocks.join vp000001_29 vp000001_30) (Blocks.join vp000001_31 (Blocks.join vp000001_32 vp000001_33)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000001_34 vp000001_35) (Blocks.join vp000001_36 vp000001_37)) (Blocks.join (Blocks.join vp000001_38 vp000001_39) (Blocks.join vp000001_40 vp000001_41))) (Blocks.join (Blocks.join (Blocks.join vp000001_42 vp000001_43) (Blocks.join vp000001_44 vp000001_45)) (Blocks.join (Blocks.join vp000001_46 vp000001_47) (Blocks.join vp000001_48 (Blocks.join vp000001_49 vp000001_50))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000001_51 vp000001_52) (Blocks.join vp000001_53 vp000001_54)) (Blocks.join (Blocks.join vp000001_55 vp000001_56) (Blocks.join vp000001_57 vp000001_58))) (Blocks.join (Blocks.join (Blocks.join vp000001_59 vp000001_60) (Blocks.join vp000001_61 vp000001_62)) (Blocks.join (Blocks.join vp000001_63 vp000001_64) (Blocks.join vp000001_65 (Blocks.join vp000001_66 vp000001_67)))))))
private theorem bp0000010 : Branch 0 (-127761639/128000000 : ℚ) vp000001 := by
  apply branch_left_normalized (c:=vp0000010) (k:=0) (m:=5113) (by decide +kernel)
  rw [show 2*(-127761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/64000000 : ℚ) by norm_num]
  exact coverp0000010
private noncomputable def ep0000011_0 : Blocks := edgeBlocks% "full/vectors/0000011-E-0000.bin"
private noncomputable def ep0000011_1 : Blocks := edgeBlocks% "full/vectors/0000011-E-0001.bin"
private noncomputable def ep0000011_2 : Blocks := edgeBlocks% "full/vectors/0000011-E-0002.bin"
private noncomputable def ep0000011_3 : Blocks := edgeBlocks% "full/vectors/0000011-E-0003.bin"
private noncomputable def ep0000011_4 : Blocks := edgeBlocks% "full/vectors/0000011-E-0004.bin"
private noncomputable def ep0000011_5 : Blocks := edgeBlocks% "full/vectors/0000011-E-0005.bin"
private noncomputable def ep0000011_6 : Blocks := edgeBlocks% "full/vectors/0000011-E-0006.bin"
private noncomputable def ep0000011_7 : Blocks := edgeBlocks% "full/vectors/0000011-E-0007.bin"
private noncomputable def ep0000011_8 : Blocks := edgeBlocks% "full/vectors/0000011-E-0008.bin"
private noncomputable def ep0000011_9 : Blocks := edgeBlocks% "full/vectors/0000011-E-0009.bin"
private noncomputable def ep0000011_10 : Blocks := edgeBlocks% "full/vectors/0000011-E-0010.bin"
private noncomputable def ep0000011_11 : Blocks := edgeBlocks% "full/vectors/0000011-E-0011.bin"
private noncomputable def ep0000011_12 : Blocks := edgeBlocks% "full/vectors/0000011-E-0012.bin"
private noncomputable def ep0000011_13 : Blocks := edgeBlocks% "full/vectors/0000011-E-0013.bin"
private noncomputable def ep0000011_14 : Blocks := edgeBlocks% "full/vectors/0000011-E-0014.bin"
private noncomputable def ep0000011_15 : Blocks := edgeBlocks% "full/vectors/0000011-E-0015.bin"
private noncomputable def ep0000011_16 : Blocks := edgeBlocks% "full/vectors/0000011-E-0016.bin"
private noncomputable def ep0000011_17 : Blocks := edgeBlocks% "full/vectors/0000011-E-0017.bin"
private noncomputable def ep0000011_18 : Blocks := edgeBlocks% "full/vectors/0000011-E-0018.bin"
private noncomputable def ep0000011_19 : Blocks := edgeBlocks% "full/vectors/0000011-E-0019.bin"
private noncomputable def ep0000011_20 : Blocks := edgeBlocks% "full/vectors/0000011-E-0020.bin"
private noncomputable def ep0000011_21 : Blocks := edgeBlocks% "full/vectors/0000011-E-0021.bin"
private noncomputable def ep0000011_22 : Blocks := edgeBlocks% "full/vectors/0000011-E-0022.bin"
private noncomputable def ep0000011_23 : Blocks := edgeBlocks% "full/vectors/0000011-E-0023.bin"
private noncomputable def ep0000011_24 : Blocks := edgeBlocks% "full/vectors/0000011-E-0024.bin"
private noncomputable def ep0000011_25 : Blocks := edgeBlocks% "full/vectors/0000011-E-0025.bin"
private noncomputable def ep0000011_26 : Blocks := edgeBlocks% "full/vectors/0000011-E-0026.bin"
private noncomputable def ep0000011_27 : Blocks := edgeBlocks% "full/vectors/0000011-E-0027.bin"
private noncomputable def ep0000011_28 : Blocks := edgeBlocks% "full/vectors/0000011-E-0028.bin"
private noncomputable def ep0000011_29 : Blocks := edgeBlocks% "full/vectors/0000011-E-0029.bin"
private noncomputable def ep0000011_30 : Blocks := edgeBlocks% "full/vectors/0000011-E-0030.bin"
private noncomputable def ep0000011_31 : Blocks := edgeBlocks% "full/vectors/0000011-E-0031.bin"
private noncomputable def ep0000011_32 : Blocks := edgeBlocks% "full/vectors/0000011-E-0032.bin"
private noncomputable def ep0000011_33 : Blocks := edgeBlocks% "full/vectors/0000011-E-0033.bin"
private noncomputable def ep0000011_34 : Blocks := edgeBlocks% "full/vectors/0000011-E-0034.bin"
private noncomputable def ep0000011_35 : Blocks := edgeBlocks% "full/vectors/0000011-E-0035.bin"
private noncomputable def ep0000011_36 : Blocks := edgeBlocks% "full/vectors/0000011-E-0036.bin"
private noncomputable def ep0000011_37 : Blocks := edgeBlocks% "full/vectors/0000011-E-0037.bin"
private noncomputable def ep0000011_38 : Blocks := edgeBlocks% "full/vectors/0000011-E-0038.bin"
private noncomputable def ep0000011_39 : Blocks := edgeBlocks% "full/vectors/0000011-E-0039.bin"
private noncomputable def ep0000011_40 : Blocks := edgeBlocks% "full/vectors/0000011-E-0040.bin"
private noncomputable def ep0000011_41 : Blocks := edgeBlocks% "full/vectors/0000011-E-0041.bin"
private noncomputable def ep0000011_42 : Blocks := edgeBlocks% "full/vectors/0000011-E-0042.bin"
private noncomputable def ep0000011_43 : Blocks := edgeBlocks% "full/vectors/0000011-E-0043.bin"
private noncomputable def ep0000011_44 : Blocks := edgeBlocks% "full/vectors/0000011-E-0044.bin"
private noncomputable def ep0000011_45 : Blocks := edgeBlocks% "full/vectors/0000011-E-0045.bin"
private noncomputable def ep0000011_46 : Blocks := edgeBlocks% "full/vectors/0000011-E-0046.bin"
private noncomputable def ep0000011_47 : Blocks := edgeBlocks% "full/vectors/0000011-E-0047.bin"
private noncomputable def ep0000011_48 : Blocks := edgeBlocks% "full/vectors/0000011-E-0048.bin"
private noncomputable def ep0000011_49 : Blocks := edgeBlocks% "full/vectors/0000011-E-0049.bin"
private noncomputable def ep0000011_50 : Blocks := edgeBlocks% "full/vectors/0000011-E-0050.bin"
private noncomputable def ep0000011_51 : Blocks := edgeBlocks% "full/vectors/0000011-E-0051.bin"
private noncomputable def ep0000011_52 : Blocks := edgeBlocks% "full/vectors/0000011-E-0052.bin"
private noncomputable def ep0000011_53 : Blocks := edgeBlocks% "full/vectors/0000011-E-0053.bin"
private noncomputable def ep0000011_54 : Blocks := edgeBlocks% "full/vectors/0000011-E-0054.bin"
private noncomputable def ep0000011_55 : Blocks := edgeBlocks% "full/vectors/0000011-E-0055.bin"
private noncomputable def ep0000011_56 : Blocks := edgeBlocks% "full/vectors/0000011-E-0056.bin"
private noncomputable def ep0000011_57 : Blocks := edgeBlocks% "full/vectors/0000011-E-0057.bin"
private noncomputable def ep0000011_58 : Blocks := edgeBlocks% "full/vectors/0000011-E-0058.bin"
private noncomputable def ep0000011_59 : Blocks := edgeBlocks% "full/vectors/0000011-E-0059.bin"
private noncomputable def ep0000011_60 : Blocks := edgeBlocks% "full/vectors/0000011-E-0060.bin"
private noncomputable def ep0000011_61 : Blocks := edgeBlocks% "full/vectors/0000011-E-0061.bin"
private noncomputable def ep0000011_62 : Blocks := edgeBlocks% "full/vectors/0000011-E-0062.bin"
private noncomputable def ep0000011_63 : Blocks := edgeBlocks% "full/vectors/0000011-E-0063.bin"
private noncomputable def ep0000011_64 : Blocks := edgeBlocks% "full/vectors/0000011-E-0064.bin"
private noncomputable def ep0000011_65 : Blocks := edgeBlocks% "full/vectors/0000011-E-0065.bin"
private noncomputable def ep0000011_66 : Blocks := edgeBlocks% "full/vectors/0000011-E-0066.bin"
private noncomputable def ep0000011_67 : Blocks := edgeBlocks% "full/vectors/0000011-E-0067.bin"
noncomputable def ep0000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000011_0 ep0000011_1) (Blocks.join ep0000011_2 ep0000011_3)) (Blocks.join (Blocks.join ep0000011_4 ep0000011_5) (Blocks.join ep0000011_6 ep0000011_7))) (Blocks.join (Blocks.join (Blocks.join ep0000011_8 ep0000011_9) (Blocks.join ep0000011_10 ep0000011_11)) (Blocks.join (Blocks.join ep0000011_12 ep0000011_13) (Blocks.join ep0000011_14 (Blocks.join ep0000011_15 ep0000011_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000011_17 ep0000011_18) (Blocks.join ep0000011_19 ep0000011_20)) (Blocks.join (Blocks.join ep0000011_21 ep0000011_22) (Blocks.join ep0000011_23 ep0000011_24))) (Blocks.join (Blocks.join (Blocks.join ep0000011_25 ep0000011_26) (Blocks.join ep0000011_27 ep0000011_28)) (Blocks.join (Blocks.join ep0000011_29 ep0000011_30) (Blocks.join ep0000011_31 (Blocks.join ep0000011_32 ep0000011_33)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000011_34 ep0000011_35) (Blocks.join ep0000011_36 ep0000011_37)) (Blocks.join (Blocks.join ep0000011_38 ep0000011_39) (Blocks.join ep0000011_40 ep0000011_41))) (Blocks.join (Blocks.join (Blocks.join ep0000011_42 ep0000011_43) (Blocks.join ep0000011_44 ep0000011_45)) (Blocks.join (Blocks.join ep0000011_46 ep0000011_47) (Blocks.join ep0000011_48 (Blocks.join ep0000011_49 ep0000011_50))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000011_51 ep0000011_52) (Blocks.join ep0000011_53 ep0000011_54)) (Blocks.join (Blocks.join ep0000011_55 ep0000011_56) (Blocks.join ep0000011_57 ep0000011_58))) (Blocks.join (Blocks.join (Blocks.join ep0000011_59 ep0000011_60) (Blocks.join ep0000011_61 ep0000011_62)) (Blocks.join (Blocks.join ep0000011_63 ep0000011_64) (Blocks.join ep0000011_65 (Blocks.join ep0000011_66 ep0000011_67)))))))
private def ptsp0000011 : List ℤ := [((2:ℤ)^1389+0),((2:ℤ)^1389+1),((2:ℤ)^1389+2),((2:ℤ)^1389+3),((2:ℤ)^1389+4),((2:ℤ)^1389+5),((2:ℤ)^1389+6),((2:ℤ)^1389+7),((2:ℤ)^1389+8),((2:ℤ)^1389+9),((2:ℤ)^1389+10)]
private theorem boundp0000011 : 2^vp000001.size*absSum vp000001.list + ((2:ℤ)^8994*absSum vp0000011.list+absSum ep0000011.list) < (2:ℤ)^14282 := by decide +kernel
private theorem pointp0000011_0 : fastHom 1 ((2:ℤ)^1389+0) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+0)+ep0000011.subst ((2:ℤ)^1389+0) := by decide +kernel
private theorem pointp0000011_1 : fastHom 1 ((2:ℤ)^1389+1) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+1)+ep0000011.subst ((2:ℤ)^1389+1) := by decide +kernel
private theorem pointp0000011_2 : fastHom 1 ((2:ℤ)^1389+2) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+2)+ep0000011.subst ((2:ℤ)^1389+2) := by decide +kernel
private theorem pointp0000011_3 : fastHom 1 ((2:ℤ)^1389+3) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+3)+ep0000011.subst ((2:ℤ)^1389+3) := by decide +kernel
private theorem pointp0000011_4 : fastHom 1 ((2:ℤ)^1389+4) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+4)+ep0000011.subst ((2:ℤ)^1389+4) := by decide +kernel
private theorem pointp0000011_5 : fastHom 1 ((2:ℤ)^1389+5) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+5)+ep0000011.subst ((2:ℤ)^1389+5) := by decide +kernel
private theorem pointp0000011_6 : fastHom 1 ((2:ℤ)^1389+6) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+6)+ep0000011.subst ((2:ℤ)^1389+6) := by decide +kernel
private theorem pointp0000011_7 : fastHom 1 ((2:ℤ)^1389+7) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+7)+ep0000011.subst ((2:ℤ)^1389+7) := by decide +kernel
private theorem pointp0000011_8 : fastHom 1 ((2:ℤ)^1389+8) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+8)+ep0000011.subst ((2:ℤ)^1389+8) := by decide +kernel
private theorem pointp0000011_9 : fastHom 1 ((2:ℤ)^1389+9) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+9)+ep0000011.subst ((2:ℤ)^1389+9) := by decide +kernel
private theorem pointp0000011_10 : fastHom 1 ((2:ℤ)^1389+10) vp000001 = ((2:ℤ)^8994)*vp0000011.subst ((2:ℤ)^1389+10)+ep0000011.subst ((2:ℤ)^1389+10) := by decide +kernel
private theorem checkp0000011 (x:ℤ) (hx:x ∈ ptsp0000011) : fastHom 1 x vp000001 = ((2:ℤ)^8994)*vp0000011.subst x+ep0000011.subst x := by
  simp only [ptsp0000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp0000011_0
  · exact pointp0000011_1
  · exact pointp0000011_2
  · exact pointp0000011_3
  · exact pointp0000011_4
  · exact pointp0000011_5
  · exact pointp0000011_6
  · exact pointp0000011_7
  · exact pointp0000011_8
  · exact pointp0000011_9
  · exact pointp0000011_10
private theorem idp0000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001.list =
    C ((2:ℤ)^8994) * horner X vp0000011.list + horner X ep0000011.list := by
  apply edge_identity (B := (2:ℤ)^14282) (by decide) (by positivity) (by positivity) boundp0000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000011 (by decide +kernel)
  · have h : ptsp0000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000011.trans_le (by decide +kernel)
  · exact checkp0000011
private theorem bp0000011 : Branch 1 (-127761639/128000000 : ℚ) vp000001 := by
  apply branch_checked idp0000011 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-191761639/64000000 : ℚ) by norm_num]
  exact coverp0000011
theorem coverp000001 : Covers (-127761639/128000000 : ℚ) vp000001 := join_branches bp0000010 bp0000011
end NextProof.EdgeFull

