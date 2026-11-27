import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00066
import NextProof.EdgeFull00068

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000100_0 : Blocks := edgeBlocks% "full/vectors/000100-V-0000.bin"
private noncomputable def vp000100_1 : Blocks := edgeBlocks% "full/vectors/000100-V-0001.bin"
private noncomputable def vp000100_2 : Blocks := edgeBlocks% "full/vectors/000100-V-0002.bin"
private noncomputable def vp000100_3 : Blocks := edgeBlocks% "full/vectors/000100-V-0003.bin"
private noncomputable def vp000100_4 : Blocks := edgeBlocks% "full/vectors/000100-V-0004.bin"
private noncomputable def vp000100_5 : Blocks := edgeBlocks% "full/vectors/000100-V-0005.bin"
private noncomputable def vp000100_6 : Blocks := edgeBlocks% "full/vectors/000100-V-0006.bin"
private noncomputable def vp000100_7 : Blocks := edgeBlocks% "full/vectors/000100-V-0007.bin"
private noncomputable def vp000100_8 : Blocks := edgeBlocks% "full/vectors/000100-V-0008.bin"
private noncomputable def vp000100_9 : Blocks := edgeBlocks% "full/vectors/000100-V-0009.bin"
private noncomputable def vp000100_10 : Blocks := edgeBlocks% "full/vectors/000100-V-0010.bin"
private noncomputable def vp000100_11 : Blocks := edgeBlocks% "full/vectors/000100-V-0011.bin"
private noncomputable def vp000100_12 : Blocks := edgeBlocks% "full/vectors/000100-V-0012.bin"
private noncomputable def vp000100_13 : Blocks := edgeBlocks% "full/vectors/000100-V-0013.bin"
private noncomputable def vp000100_14 : Blocks := edgeBlocks% "full/vectors/000100-V-0014.bin"
private noncomputable def vp000100_15 : Blocks := edgeBlocks% "full/vectors/000100-V-0015.bin"
private noncomputable def vp000100_16 : Blocks := edgeBlocks% "full/vectors/000100-V-0016.bin"
private noncomputable def vp000100_17 : Blocks := edgeBlocks% "full/vectors/000100-V-0017.bin"
private noncomputable def vp000100_18 : Blocks := edgeBlocks% "full/vectors/000100-V-0018.bin"
private noncomputable def vp000100_19 : Blocks := edgeBlocks% "full/vectors/000100-V-0019.bin"
private noncomputable def vp000100_20 : Blocks := edgeBlocks% "full/vectors/000100-V-0020.bin"
private noncomputable def vp000100_21 : Blocks := edgeBlocks% "full/vectors/000100-V-0021.bin"
private noncomputable def vp000100_22 : Blocks := edgeBlocks% "full/vectors/000100-V-0022.bin"
private noncomputable def vp000100_23 : Blocks := edgeBlocks% "full/vectors/000100-V-0023.bin"
private noncomputable def vp000100_24 : Blocks := edgeBlocks% "full/vectors/000100-V-0024.bin"
private noncomputable def vp000100_25 : Blocks := edgeBlocks% "full/vectors/000100-V-0025.bin"
private noncomputable def vp000100_26 : Blocks := edgeBlocks% "full/vectors/000100-V-0026.bin"
private noncomputable def vp000100_27 : Blocks := edgeBlocks% "full/vectors/000100-V-0027.bin"
private noncomputable def vp000100_28 : Blocks := edgeBlocks% "full/vectors/000100-V-0028.bin"
private noncomputable def vp000100_29 : Blocks := edgeBlocks% "full/vectors/000100-V-0029.bin"
private noncomputable def vp000100_30 : Blocks := edgeBlocks% "full/vectors/000100-V-0030.bin"
private noncomputable def vp000100_31 : Blocks := edgeBlocks% "full/vectors/000100-V-0031.bin"
private noncomputable def vp000100_32 : Blocks := edgeBlocks% "full/vectors/000100-V-0032.bin"
private noncomputable def vp000100_33 : Blocks := edgeBlocks% "full/vectors/000100-V-0033.bin"
private noncomputable def vp000100_34 : Blocks := edgeBlocks% "full/vectors/000100-V-0034.bin"
private noncomputable def vp000100_35 : Blocks := edgeBlocks% "full/vectors/000100-V-0035.bin"
private noncomputable def vp000100_36 : Blocks := edgeBlocks% "full/vectors/000100-V-0036.bin"
private noncomputable def vp000100_37 : Blocks := edgeBlocks% "full/vectors/000100-V-0037.bin"
private noncomputable def vp000100_38 : Blocks := edgeBlocks% "full/vectors/000100-V-0038.bin"
private noncomputable def vp000100_39 : Blocks := edgeBlocks% "full/vectors/000100-V-0039.bin"
noncomputable def vp000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000100_0 vp000100_1) (Blocks.join vp000100_2 (Blocks.join vp000100_3 vp000100_4))) (Blocks.join (Blocks.join vp000100_5 vp000100_6) (Blocks.join vp000100_7 (Blocks.join vp000100_8 vp000100_9)))) (Blocks.join (Blocks.join (Blocks.join vp000100_10 vp000100_11) (Blocks.join vp000100_12 (Blocks.join vp000100_13 vp000100_14))) (Blocks.join (Blocks.join vp000100_15 vp000100_16) (Blocks.join vp000100_17 (Blocks.join vp000100_18 vp000100_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000100_20 vp000100_21) (Blocks.join vp000100_22 (Blocks.join vp000100_23 vp000100_24))) (Blocks.join (Blocks.join vp000100_25 vp000100_26) (Blocks.join vp000100_27 (Blocks.join vp000100_28 vp000100_29)))) (Blocks.join (Blocks.join (Blocks.join vp000100_30 vp000100_31) (Blocks.join vp000100_32 (Blocks.join vp000100_33 vp000100_34))) (Blocks.join (Blocks.join vp000100_35 vp000100_36) (Blocks.join vp000100_37 (Blocks.join vp000100_38 vp000100_39))))))
private theorem bp0001000 : Branch 0 (-511761639/128000000 : ℚ) vp000100 := by
  apply branch_left_normalized (c:=vp0001000) (k:=0) (m:=2681) (by decide +kernel)
  rw [show 2*(-511761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/64000000 : ℚ) by norm_num]
  exact coverp0001000
private noncomputable def ep0001001_0 : Blocks := edgeBlocks% "full/vectors/0001001-E-0000.bin"
private noncomputable def ep0001001_1 : Blocks := edgeBlocks% "full/vectors/0001001-E-0001.bin"
private noncomputable def ep0001001_2 : Blocks := edgeBlocks% "full/vectors/0001001-E-0002.bin"
private noncomputable def ep0001001_3 : Blocks := edgeBlocks% "full/vectors/0001001-E-0003.bin"
private noncomputable def ep0001001_4 : Blocks := edgeBlocks% "full/vectors/0001001-E-0004.bin"
private noncomputable def ep0001001_5 : Blocks := edgeBlocks% "full/vectors/0001001-E-0005.bin"
private noncomputable def ep0001001_6 : Blocks := edgeBlocks% "full/vectors/0001001-E-0006.bin"
private noncomputable def ep0001001_7 : Blocks := edgeBlocks% "full/vectors/0001001-E-0007.bin"
private noncomputable def ep0001001_8 : Blocks := edgeBlocks% "full/vectors/0001001-E-0008.bin"
private noncomputable def ep0001001_9 : Blocks := edgeBlocks% "full/vectors/0001001-E-0009.bin"
private noncomputable def ep0001001_10 : Blocks := edgeBlocks% "full/vectors/0001001-E-0010.bin"
private noncomputable def ep0001001_11 : Blocks := edgeBlocks% "full/vectors/0001001-E-0011.bin"
private noncomputable def ep0001001_12 : Blocks := edgeBlocks% "full/vectors/0001001-E-0012.bin"
private noncomputable def ep0001001_13 : Blocks := edgeBlocks% "full/vectors/0001001-E-0013.bin"
private noncomputable def ep0001001_14 : Blocks := edgeBlocks% "full/vectors/0001001-E-0014.bin"
private noncomputable def ep0001001_15 : Blocks := edgeBlocks% "full/vectors/0001001-E-0015.bin"
private noncomputable def ep0001001_16 : Blocks := edgeBlocks% "full/vectors/0001001-E-0016.bin"
private noncomputable def ep0001001_17 : Blocks := edgeBlocks% "full/vectors/0001001-E-0017.bin"
private noncomputable def ep0001001_18 : Blocks := edgeBlocks% "full/vectors/0001001-E-0018.bin"
private noncomputable def ep0001001_19 : Blocks := edgeBlocks% "full/vectors/0001001-E-0019.bin"
private noncomputable def ep0001001_20 : Blocks := edgeBlocks% "full/vectors/0001001-E-0020.bin"
private noncomputable def ep0001001_21 : Blocks := edgeBlocks% "full/vectors/0001001-E-0021.bin"
private noncomputable def ep0001001_22 : Blocks := edgeBlocks% "full/vectors/0001001-E-0022.bin"
private noncomputable def ep0001001_23 : Blocks := edgeBlocks% "full/vectors/0001001-E-0023.bin"
private noncomputable def ep0001001_24 : Blocks := edgeBlocks% "full/vectors/0001001-E-0024.bin"
private noncomputable def ep0001001_25 : Blocks := edgeBlocks% "full/vectors/0001001-E-0025.bin"
private noncomputable def ep0001001_26 : Blocks := edgeBlocks% "full/vectors/0001001-E-0026.bin"
private noncomputable def ep0001001_27 : Blocks := edgeBlocks% "full/vectors/0001001-E-0027.bin"
private noncomputable def ep0001001_28 : Blocks := edgeBlocks% "full/vectors/0001001-E-0028.bin"
private noncomputable def ep0001001_29 : Blocks := edgeBlocks% "full/vectors/0001001-E-0029.bin"
private noncomputable def ep0001001_30 : Blocks := edgeBlocks% "full/vectors/0001001-E-0030.bin"
private noncomputable def ep0001001_31 : Blocks := edgeBlocks% "full/vectors/0001001-E-0031.bin"
private noncomputable def ep0001001_32 : Blocks := edgeBlocks% "full/vectors/0001001-E-0032.bin"
private noncomputable def ep0001001_33 : Blocks := edgeBlocks% "full/vectors/0001001-E-0033.bin"
private noncomputable def ep0001001_34 : Blocks := edgeBlocks% "full/vectors/0001001-E-0034.bin"
private noncomputable def ep0001001_35 : Blocks := edgeBlocks% "full/vectors/0001001-E-0035.bin"
private noncomputable def ep0001001_36 : Blocks := edgeBlocks% "full/vectors/0001001-E-0036.bin"
private noncomputable def ep0001001_37 : Blocks := edgeBlocks% "full/vectors/0001001-E-0037.bin"
private noncomputable def ep0001001_38 : Blocks := edgeBlocks% "full/vectors/0001001-E-0038.bin"
private noncomputable def ep0001001_39 : Blocks := edgeBlocks% "full/vectors/0001001-E-0039.bin"
noncomputable def ep0001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001001_0 ep0001001_1) (Blocks.join ep0001001_2 (Blocks.join ep0001001_3 ep0001001_4))) (Blocks.join (Blocks.join ep0001001_5 ep0001001_6) (Blocks.join ep0001001_7 (Blocks.join ep0001001_8 ep0001001_9)))) (Blocks.join (Blocks.join (Blocks.join ep0001001_10 ep0001001_11) (Blocks.join ep0001001_12 (Blocks.join ep0001001_13 ep0001001_14))) (Blocks.join (Blocks.join ep0001001_15 ep0001001_16) (Blocks.join ep0001001_17 (Blocks.join ep0001001_18 ep0001001_19))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001001_20 ep0001001_21) (Blocks.join ep0001001_22 (Blocks.join ep0001001_23 ep0001001_24))) (Blocks.join (Blocks.join ep0001001_25 ep0001001_26) (Blocks.join ep0001001_27 (Blocks.join ep0001001_28 ep0001001_29)))) (Blocks.join (Blocks.join (Blocks.join ep0001001_30 ep0001001_31) (Blocks.join ep0001001_32 (Blocks.join ep0001001_33 ep0001001_34))) (Blocks.join (Blocks.join ep0001001_35 ep0001001_36) (Blocks.join ep0001001_37 (Blocks.join ep0001001_38 ep0001001_39))))))
private def ptsp0001001 : List ℤ := [((2:ℤ)^2345+0),((2:ℤ)^2345+1),((2:ℤ)^2345+2),((2:ℤ)^2345+3)]
private theorem boundp0001001 : 2^vp000100.size*absSum vp000100.list + ((2:ℤ)^5486*absSum vp0001001.list+absSum ep0001001.list) < (2:ℤ)^8072 := by decide +kernel
private theorem pointp0001001_0 : fastHom 1 ((2:ℤ)^2345+0) vp000100 = ((2:ℤ)^5486)*vp0001001.subst ((2:ℤ)^2345+0)+ep0001001.subst ((2:ℤ)^2345+0) := by decide +kernel
private theorem pointp0001001_1 : fastHom 1 ((2:ℤ)^2345+1) vp000100 = ((2:ℤ)^5486)*vp0001001.subst ((2:ℤ)^2345+1)+ep0001001.subst ((2:ℤ)^2345+1) := by decide +kernel
private theorem pointp0001001_2 : fastHom 1 ((2:ℤ)^2345+2) vp000100 = ((2:ℤ)^5486)*vp0001001.subst ((2:ℤ)^2345+2)+ep0001001.subst ((2:ℤ)^2345+2) := by decide +kernel
private theorem pointp0001001_3 : fastHom 1 ((2:ℤ)^2345+3) vp000100 = ((2:ℤ)^5486)*vp0001001.subst ((2:ℤ)^2345+3)+ep0001001.subst ((2:ℤ)^2345+3) := by decide +kernel
private theorem checkp0001001 (x:ℤ) (hx:x ∈ ptsp0001001) : fastHom 1 x vp000100 = ((2:ℤ)^5486)*vp0001001.subst x+ep0001001.subst x := by
  simp only [ptsp0001001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp0001001_0
  · exact pointp0001001_1
  · exact pointp0001001_2
  · exact pointp0001001_3
private theorem idp0001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100.list =
    C ((2:ℤ)^5486) * horner X vp0001001.list + horner X ep0001001.list := by
  apply edge_identity (B := (2:ℤ)^8072) (by decide) (by positivity) (by positivity) boundp0001001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0001001 (by decide +kernel)
  · have h : ptsp0001001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0001001.trans_le (by decide +kernel)
  · exact checkp0001001
private theorem bp0001001 : Branch 1 (-511761639/128000000 : ℚ) vp000100 := by
  apply branch_checked idp0001001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-575761639/64000000 : ℚ) by norm_num]
  exact coverp0001001
theorem coverp000100 : Covers (-511761639/128000000 : ℚ) vp000100 := join_branches bp0001000 bp0001001
end NextProof.EdgeFull

