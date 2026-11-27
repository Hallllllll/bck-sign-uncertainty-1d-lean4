import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00027
import NextProof.EdgeFull00029

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000001_0 : Blocks := edgeBlocks% "full/vectors/00000001-V-0000.bin"
private noncomputable def vp00000001_1 : Blocks := edgeBlocks% "full/vectors/00000001-V-0001.bin"
private noncomputable def vp00000001_2 : Blocks := edgeBlocks% "full/vectors/00000001-V-0002.bin"
private noncomputable def vp00000001_3 : Blocks := edgeBlocks% "full/vectors/00000001-V-0003.bin"
private noncomputable def vp00000001_4 : Blocks := edgeBlocks% "full/vectors/00000001-V-0004.bin"
private noncomputable def vp00000001_5 : Blocks := edgeBlocks% "full/vectors/00000001-V-0005.bin"
private noncomputable def vp00000001_6 : Blocks := edgeBlocks% "full/vectors/00000001-V-0006.bin"
private noncomputable def vp00000001_7 : Blocks := edgeBlocks% "full/vectors/00000001-V-0007.bin"
private noncomputable def vp00000001_8 : Blocks := edgeBlocks% "full/vectors/00000001-V-0008.bin"
private noncomputable def vp00000001_9 : Blocks := edgeBlocks% "full/vectors/00000001-V-0009.bin"
private noncomputable def vp00000001_10 : Blocks := edgeBlocks% "full/vectors/00000001-V-0010.bin"
private noncomputable def vp00000001_11 : Blocks := edgeBlocks% "full/vectors/00000001-V-0011.bin"
private noncomputable def vp00000001_12 : Blocks := edgeBlocks% "full/vectors/00000001-V-0012.bin"
private noncomputable def vp00000001_13 : Blocks := edgeBlocks% "full/vectors/00000001-V-0013.bin"
private noncomputable def vp00000001_14 : Blocks := edgeBlocks% "full/vectors/00000001-V-0014.bin"
private noncomputable def vp00000001_15 : Blocks := edgeBlocks% "full/vectors/00000001-V-0015.bin"
private noncomputable def vp00000001_16 : Blocks := edgeBlocks% "full/vectors/00000001-V-0016.bin"
private noncomputable def vp00000001_17 : Blocks := edgeBlocks% "full/vectors/00000001-V-0017.bin"
private noncomputable def vp00000001_18 : Blocks := edgeBlocks% "full/vectors/00000001-V-0018.bin"
private noncomputable def vp00000001_19 : Blocks := edgeBlocks% "full/vectors/00000001-V-0019.bin"
private noncomputable def vp00000001_20 : Blocks := edgeBlocks% "full/vectors/00000001-V-0020.bin"
private noncomputable def vp00000001_21 : Blocks := edgeBlocks% "full/vectors/00000001-V-0021.bin"
private noncomputable def vp00000001_22 : Blocks := edgeBlocks% "full/vectors/00000001-V-0022.bin"
private noncomputable def vp00000001_23 : Blocks := edgeBlocks% "full/vectors/00000001-V-0023.bin"
private noncomputable def vp00000001_24 : Blocks := edgeBlocks% "full/vectors/00000001-V-0024.bin"
private noncomputable def vp00000001_25 : Blocks := edgeBlocks% "full/vectors/00000001-V-0025.bin"
private noncomputable def vp00000001_26 : Blocks := edgeBlocks% "full/vectors/00000001-V-0026.bin"
private noncomputable def vp00000001_27 : Blocks := edgeBlocks% "full/vectors/00000001-V-0027.bin"
private noncomputable def vp00000001_28 : Blocks := edgeBlocks% "full/vectors/00000001-V-0028.bin"
private noncomputable def vp00000001_29 : Blocks := edgeBlocks% "full/vectors/00000001-V-0029.bin"
private noncomputable def vp00000001_30 : Blocks := edgeBlocks% "full/vectors/00000001-V-0030.bin"
private noncomputable def vp00000001_31 : Blocks := edgeBlocks% "full/vectors/00000001-V-0031.bin"
private noncomputable def vp00000001_32 : Blocks := edgeBlocks% "full/vectors/00000001-V-0032.bin"
private noncomputable def vp00000001_33 : Blocks := edgeBlocks% "full/vectors/00000001-V-0033.bin"
private noncomputable def vp00000001_34 : Blocks := edgeBlocks% "full/vectors/00000001-V-0034.bin"
private noncomputable def vp00000001_35 : Blocks := edgeBlocks% "full/vectors/00000001-V-0035.bin"
private noncomputable def vp00000001_36 : Blocks := edgeBlocks% "full/vectors/00000001-V-0036.bin"
noncomputable def vp00000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000001_0 vp00000001_1) (Blocks.join vp00000001_2 vp00000001_3)) (Blocks.join (Blocks.join vp00000001_4 vp00000001_5) (Blocks.join vp00000001_6 (Blocks.join vp00000001_7 vp00000001_8)))) (Blocks.join (Blocks.join (Blocks.join vp00000001_9 vp00000001_10) (Blocks.join vp00000001_11 vp00000001_12)) (Blocks.join (Blocks.join vp00000001_13 vp00000001_14) (Blocks.join vp00000001_15 (Blocks.join vp00000001_16 vp00000001_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000001_18 vp00000001_19) (Blocks.join vp00000001_20 vp00000001_21)) (Blocks.join (Blocks.join vp00000001_22 vp00000001_23) (Blocks.join vp00000001_24 (Blocks.join vp00000001_25 vp00000001_26)))) (Blocks.join (Blocks.join (Blocks.join vp00000001_27 vp00000001_28) (Blocks.join vp00000001_29 (Blocks.join vp00000001_30 vp00000001_31))) (Blocks.join (Blocks.join vp00000001_32 vp00000001_33) (Blocks.join vp00000001_34 (Blocks.join vp00000001_35 vp00000001_36))))))
private theorem bp000000010 : Branch 0 (-31761639/32000000 : ℚ) vp00000001 := by
  apply branch_left_normalized (c:=vp000000010) (k:=0) (m:=2689) (by decide +kernel)
  rw [show 2*(-31761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/16000000 : ℚ) by norm_num]
  exact coverp000000010
private noncomputable def ep000000011_0 : Blocks := edgeBlocks% "full/vectors/000000011-E-0000.bin"
private noncomputable def ep000000011_1 : Blocks := edgeBlocks% "full/vectors/000000011-E-0001.bin"
private noncomputable def ep000000011_2 : Blocks := edgeBlocks% "full/vectors/000000011-E-0002.bin"
private noncomputable def ep000000011_3 : Blocks := edgeBlocks% "full/vectors/000000011-E-0003.bin"
private noncomputable def ep000000011_4 : Blocks := edgeBlocks% "full/vectors/000000011-E-0004.bin"
private noncomputable def ep000000011_5 : Blocks := edgeBlocks% "full/vectors/000000011-E-0005.bin"
private noncomputable def ep000000011_6 : Blocks := edgeBlocks% "full/vectors/000000011-E-0006.bin"
private noncomputable def ep000000011_7 : Blocks := edgeBlocks% "full/vectors/000000011-E-0007.bin"
private noncomputable def ep000000011_8 : Blocks := edgeBlocks% "full/vectors/000000011-E-0008.bin"
private noncomputable def ep000000011_9 : Blocks := edgeBlocks% "full/vectors/000000011-E-0009.bin"
private noncomputable def ep000000011_10 : Blocks := edgeBlocks% "full/vectors/000000011-E-0010.bin"
private noncomputable def ep000000011_11 : Blocks := edgeBlocks% "full/vectors/000000011-E-0011.bin"
private noncomputable def ep000000011_12 : Blocks := edgeBlocks% "full/vectors/000000011-E-0012.bin"
private noncomputable def ep000000011_13 : Blocks := edgeBlocks% "full/vectors/000000011-E-0013.bin"
private noncomputable def ep000000011_14 : Blocks := edgeBlocks% "full/vectors/000000011-E-0014.bin"
private noncomputable def ep000000011_15 : Blocks := edgeBlocks% "full/vectors/000000011-E-0015.bin"
private noncomputable def ep000000011_16 : Blocks := edgeBlocks% "full/vectors/000000011-E-0016.bin"
private noncomputable def ep000000011_17 : Blocks := edgeBlocks% "full/vectors/000000011-E-0017.bin"
private noncomputable def ep000000011_18 : Blocks := edgeBlocks% "full/vectors/000000011-E-0018.bin"
private noncomputable def ep000000011_19 : Blocks := edgeBlocks% "full/vectors/000000011-E-0019.bin"
private noncomputable def ep000000011_20 : Blocks := edgeBlocks% "full/vectors/000000011-E-0020.bin"
private noncomputable def ep000000011_21 : Blocks := edgeBlocks% "full/vectors/000000011-E-0021.bin"
private noncomputable def ep000000011_22 : Blocks := edgeBlocks% "full/vectors/000000011-E-0022.bin"
private noncomputable def ep000000011_23 : Blocks := edgeBlocks% "full/vectors/000000011-E-0023.bin"
private noncomputable def ep000000011_24 : Blocks := edgeBlocks% "full/vectors/000000011-E-0024.bin"
private noncomputable def ep000000011_25 : Blocks := edgeBlocks% "full/vectors/000000011-E-0025.bin"
private noncomputable def ep000000011_26 : Blocks := edgeBlocks% "full/vectors/000000011-E-0026.bin"
private noncomputable def ep000000011_27 : Blocks := edgeBlocks% "full/vectors/000000011-E-0027.bin"
private noncomputable def ep000000011_28 : Blocks := edgeBlocks% "full/vectors/000000011-E-0028.bin"
private noncomputable def ep000000011_29 : Blocks := edgeBlocks% "full/vectors/000000011-E-0029.bin"
private noncomputable def ep000000011_30 : Blocks := edgeBlocks% "full/vectors/000000011-E-0030.bin"
private noncomputable def ep000000011_31 : Blocks := edgeBlocks% "full/vectors/000000011-E-0031.bin"
private noncomputable def ep000000011_32 : Blocks := edgeBlocks% "full/vectors/000000011-E-0032.bin"
private noncomputable def ep000000011_33 : Blocks := edgeBlocks% "full/vectors/000000011-E-0033.bin"
private noncomputable def ep000000011_34 : Blocks := edgeBlocks% "full/vectors/000000011-E-0034.bin"
private noncomputable def ep000000011_35 : Blocks := edgeBlocks% "full/vectors/000000011-E-0035.bin"
private noncomputable def ep000000011_36 : Blocks := edgeBlocks% "full/vectors/000000011-E-0036.bin"
noncomputable def ep000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000000011_0 ep000000011_1) (Blocks.join ep000000011_2 ep000000011_3)) (Blocks.join (Blocks.join ep000000011_4 ep000000011_5) (Blocks.join ep000000011_6 (Blocks.join ep000000011_7 ep000000011_8)))) (Blocks.join (Blocks.join (Blocks.join ep000000011_9 ep000000011_10) (Blocks.join ep000000011_11 ep000000011_12)) (Blocks.join (Blocks.join ep000000011_13 ep000000011_14) (Blocks.join ep000000011_15 (Blocks.join ep000000011_16 ep000000011_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000000011_18 ep000000011_19) (Blocks.join ep000000011_20 ep000000011_21)) (Blocks.join (Blocks.join ep000000011_22 ep000000011_23) (Blocks.join ep000000011_24 (Blocks.join ep000000011_25 ep000000011_26)))) (Blocks.join (Blocks.join (Blocks.join ep000000011_27 ep000000011_28) (Blocks.join ep000000011_29 (Blocks.join ep000000011_30 ep000000011_31))) (Blocks.join (Blocks.join ep000000011_32 ep000000011_33) (Blocks.join ep000000011_34 (Blocks.join ep000000011_35 ep000000011_36))))))
private def ptsp000000011 : List ℤ := [((2:ℤ)^2546+0),((2:ℤ)^2546+1),((2:ℤ)^2546+2),((2:ℤ)^2546+3)]
private theorem boundp000000011 : 2^vp00000001.size*absSum vp00000001.list + ((2:ℤ)^4805*absSum vp000000011.list+absSum ep000000011.list) < (2:ℤ)^7679 := by decide +kernel
private theorem pointp000000011_0 : fastHom 1 ((2:ℤ)^2546+0) vp00000001 = ((2:ℤ)^4805)*vp000000011.subst ((2:ℤ)^2546+0)+ep000000011.subst ((2:ℤ)^2546+0) := by decide +kernel
private theorem pointp000000011_1 : fastHom 1 ((2:ℤ)^2546+1) vp00000001 = ((2:ℤ)^4805)*vp000000011.subst ((2:ℤ)^2546+1)+ep000000011.subst ((2:ℤ)^2546+1) := by decide +kernel
private theorem pointp000000011_2 : fastHom 1 ((2:ℤ)^2546+2) vp00000001 = ((2:ℤ)^4805)*vp000000011.subst ((2:ℤ)^2546+2)+ep000000011.subst ((2:ℤ)^2546+2) := by decide +kernel
private theorem pointp000000011_3 : fastHom 1 ((2:ℤ)^2546+3) vp00000001 = ((2:ℤ)^4805)*vp000000011.subst ((2:ℤ)^2546+3)+ep000000011.subst ((2:ℤ)^2546+3) := by decide +kernel
private theorem checkp000000011 (x:ℤ) (hx:x ∈ ptsp000000011) : fastHom 1 x vp00000001 = ((2:ℤ)^4805)*vp000000011.subst x+ep000000011.subst x := by
  simp only [ptsp000000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp000000011_0
  · exact pointp000000011_1
  · exact pointp000000011_2
  · exact pointp000000011_3
private theorem idp000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001.list =
    C ((2:ℤ)^4805) * horner X vp000000011.list + horner X ep000000011.list := by
  apply edge_identity (B := (2:ℤ)^7679) (by decide) (by positivity) (by positivity) boundp000000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp000000011 (by decide +kernel)
  · have h : ptsp000000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp000000011.trans_le (by decide +kernel)
  · exact checkp000000011
private theorem bp000000011 : Branch 1 (-31761639/32000000 : ℚ) vp00000001 := by
  apply branch_checked idp000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-47761639/16000000 : ℚ) by norm_num]
  exact coverp000000011
theorem coverp00000001 : Covers (-31761639/32000000 : ℚ) vp00000001 := join_branches bp000000010 bp000000011
end NextProof.EdgeFull

