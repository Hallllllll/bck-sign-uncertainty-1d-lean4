import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00045
import NextProof.EdgeFull00047

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000011_0 : Blocks := edgeBlocks% "full/vectors/0000011-V-0000.bin"
private noncomputable def vp0000011_1 : Blocks := edgeBlocks% "full/vectors/0000011-V-0001.bin"
private noncomputable def vp0000011_2 : Blocks := edgeBlocks% "full/vectors/0000011-V-0002.bin"
private noncomputable def vp0000011_3 : Blocks := edgeBlocks% "full/vectors/0000011-V-0003.bin"
private noncomputable def vp0000011_4 : Blocks := edgeBlocks% "full/vectors/0000011-V-0004.bin"
private noncomputable def vp0000011_5 : Blocks := edgeBlocks% "full/vectors/0000011-V-0005.bin"
private noncomputable def vp0000011_6 : Blocks := edgeBlocks% "full/vectors/0000011-V-0006.bin"
private noncomputable def vp0000011_7 : Blocks := edgeBlocks% "full/vectors/0000011-V-0007.bin"
private noncomputable def vp0000011_8 : Blocks := edgeBlocks% "full/vectors/0000011-V-0008.bin"
private noncomputable def vp0000011_9 : Blocks := edgeBlocks% "full/vectors/0000011-V-0009.bin"
private noncomputable def vp0000011_10 : Blocks := edgeBlocks% "full/vectors/0000011-V-0010.bin"
private noncomputable def vp0000011_11 : Blocks := edgeBlocks% "full/vectors/0000011-V-0011.bin"
private noncomputable def vp0000011_12 : Blocks := edgeBlocks% "full/vectors/0000011-V-0012.bin"
private noncomputable def vp0000011_13 : Blocks := edgeBlocks% "full/vectors/0000011-V-0013.bin"
private noncomputable def vp0000011_14 : Blocks := edgeBlocks% "full/vectors/0000011-V-0014.bin"
private noncomputable def vp0000011_15 : Blocks := edgeBlocks% "full/vectors/0000011-V-0015.bin"
private noncomputable def vp0000011_16 : Blocks := edgeBlocks% "full/vectors/0000011-V-0016.bin"
private noncomputable def vp0000011_17 : Blocks := edgeBlocks% "full/vectors/0000011-V-0017.bin"
private noncomputable def vp0000011_18 : Blocks := edgeBlocks% "full/vectors/0000011-V-0018.bin"
private noncomputable def vp0000011_19 : Blocks := edgeBlocks% "full/vectors/0000011-V-0019.bin"
private noncomputable def vp0000011_20 : Blocks := edgeBlocks% "full/vectors/0000011-V-0020.bin"
private noncomputable def vp0000011_21 : Blocks := edgeBlocks% "full/vectors/0000011-V-0021.bin"
private noncomputable def vp0000011_22 : Blocks := edgeBlocks% "full/vectors/0000011-V-0022.bin"
private noncomputable def vp0000011_23 : Blocks := edgeBlocks% "full/vectors/0000011-V-0023.bin"
private noncomputable def vp0000011_24 : Blocks := edgeBlocks% "full/vectors/0000011-V-0024.bin"
private noncomputable def vp0000011_25 : Blocks := edgeBlocks% "full/vectors/0000011-V-0025.bin"
private noncomputable def vp0000011_26 : Blocks := edgeBlocks% "full/vectors/0000011-V-0026.bin"
private noncomputable def vp0000011_27 : Blocks := edgeBlocks% "full/vectors/0000011-V-0027.bin"
private noncomputable def vp0000011_28 : Blocks := edgeBlocks% "full/vectors/0000011-V-0028.bin"
private noncomputable def vp0000011_29 : Blocks := edgeBlocks% "full/vectors/0000011-V-0029.bin"
private noncomputable def vp0000011_30 : Blocks := edgeBlocks% "full/vectors/0000011-V-0030.bin"
private noncomputable def vp0000011_31 : Blocks := edgeBlocks% "full/vectors/0000011-V-0031.bin"
private noncomputable def vp0000011_32 : Blocks := edgeBlocks% "full/vectors/0000011-V-0032.bin"
private noncomputable def vp0000011_33 : Blocks := edgeBlocks% "full/vectors/0000011-V-0033.bin"
noncomputable def vp0000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000011_0 vp0000011_1) (Blocks.join vp0000011_2 vp0000011_3)) (Blocks.join (Blocks.join vp0000011_4 vp0000011_5) (Blocks.join vp0000011_6 vp0000011_7))) (Blocks.join (Blocks.join (Blocks.join vp0000011_8 vp0000011_9) (Blocks.join vp0000011_10 vp0000011_11)) (Blocks.join (Blocks.join vp0000011_12 vp0000011_13) (Blocks.join vp0000011_14 (Blocks.join vp0000011_15 vp0000011_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000011_17 vp0000011_18) (Blocks.join vp0000011_19 vp0000011_20)) (Blocks.join (Blocks.join vp0000011_21 vp0000011_22) (Blocks.join vp0000011_23 vp0000011_24))) (Blocks.join (Blocks.join (Blocks.join vp0000011_25 vp0000011_26) (Blocks.join vp0000011_27 vp0000011_28)) (Blocks.join (Blocks.join vp0000011_29 vp0000011_30) (Blocks.join vp0000011_31 (Blocks.join vp0000011_32 vp0000011_33))))))
private theorem bp00000110 : Branch 0 (-191761639/64000000 : ℚ) vp0000011 := by
  apply branch_left_normalized (c:=vp00000110) (k:=0) (m:=2215) (by decide +kernel)
  rw [show 2*(-191761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/32000000 : ℚ) by norm_num]
  exact coverp00000110
private noncomputable def ep00000111_0 : Blocks := edgeBlocks% "full/vectors/00000111-E-0000.bin"
private noncomputable def ep00000111_1 : Blocks := edgeBlocks% "full/vectors/00000111-E-0001.bin"
private noncomputable def ep00000111_2 : Blocks := edgeBlocks% "full/vectors/00000111-E-0002.bin"
private noncomputable def ep00000111_3 : Blocks := edgeBlocks% "full/vectors/00000111-E-0003.bin"
private noncomputable def ep00000111_4 : Blocks := edgeBlocks% "full/vectors/00000111-E-0004.bin"
private noncomputable def ep00000111_5 : Blocks := edgeBlocks% "full/vectors/00000111-E-0005.bin"
private noncomputable def ep00000111_6 : Blocks := edgeBlocks% "full/vectors/00000111-E-0006.bin"
private noncomputable def ep00000111_7 : Blocks := edgeBlocks% "full/vectors/00000111-E-0007.bin"
private noncomputable def ep00000111_8 : Blocks := edgeBlocks% "full/vectors/00000111-E-0008.bin"
private noncomputable def ep00000111_9 : Blocks := edgeBlocks% "full/vectors/00000111-E-0009.bin"
private noncomputable def ep00000111_10 : Blocks := edgeBlocks% "full/vectors/00000111-E-0010.bin"
private noncomputable def ep00000111_11 : Blocks := edgeBlocks% "full/vectors/00000111-E-0011.bin"
private noncomputable def ep00000111_12 : Blocks := edgeBlocks% "full/vectors/00000111-E-0012.bin"
private noncomputable def ep00000111_13 : Blocks := edgeBlocks% "full/vectors/00000111-E-0013.bin"
private noncomputable def ep00000111_14 : Blocks := edgeBlocks% "full/vectors/00000111-E-0014.bin"
private noncomputable def ep00000111_15 : Blocks := edgeBlocks% "full/vectors/00000111-E-0015.bin"
private noncomputable def ep00000111_16 : Blocks := edgeBlocks% "full/vectors/00000111-E-0016.bin"
private noncomputable def ep00000111_17 : Blocks := edgeBlocks% "full/vectors/00000111-E-0017.bin"
private noncomputable def ep00000111_18 : Blocks := edgeBlocks% "full/vectors/00000111-E-0018.bin"
private noncomputable def ep00000111_19 : Blocks := edgeBlocks% "full/vectors/00000111-E-0019.bin"
private noncomputable def ep00000111_20 : Blocks := edgeBlocks% "full/vectors/00000111-E-0020.bin"
private noncomputable def ep00000111_21 : Blocks := edgeBlocks% "full/vectors/00000111-E-0021.bin"
private noncomputable def ep00000111_22 : Blocks := edgeBlocks% "full/vectors/00000111-E-0022.bin"
private noncomputable def ep00000111_23 : Blocks := edgeBlocks% "full/vectors/00000111-E-0023.bin"
private noncomputable def ep00000111_24 : Blocks := edgeBlocks% "full/vectors/00000111-E-0024.bin"
private noncomputable def ep00000111_25 : Blocks := edgeBlocks% "full/vectors/00000111-E-0025.bin"
private noncomputable def ep00000111_26 : Blocks := edgeBlocks% "full/vectors/00000111-E-0026.bin"
private noncomputable def ep00000111_27 : Blocks := edgeBlocks% "full/vectors/00000111-E-0027.bin"
private noncomputable def ep00000111_28 : Blocks := edgeBlocks% "full/vectors/00000111-E-0028.bin"
private noncomputable def ep00000111_29 : Blocks := edgeBlocks% "full/vectors/00000111-E-0029.bin"
private noncomputable def ep00000111_30 : Blocks := edgeBlocks% "full/vectors/00000111-E-0030.bin"
private noncomputable def ep00000111_31 : Blocks := edgeBlocks% "full/vectors/00000111-E-0031.bin"
private noncomputable def ep00000111_32 : Blocks := edgeBlocks% "full/vectors/00000111-E-0032.bin"
private noncomputable def ep00000111_33 : Blocks := edgeBlocks% "full/vectors/00000111-E-0033.bin"
noncomputable def ep00000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000111_0 ep00000111_1) (Blocks.join ep00000111_2 ep00000111_3)) (Blocks.join (Blocks.join ep00000111_4 ep00000111_5) (Blocks.join ep00000111_6 ep00000111_7))) (Blocks.join (Blocks.join (Blocks.join ep00000111_8 ep00000111_9) (Blocks.join ep00000111_10 ep00000111_11)) (Blocks.join (Blocks.join ep00000111_12 ep00000111_13) (Blocks.join ep00000111_14 (Blocks.join ep00000111_15 ep00000111_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000111_17 ep00000111_18) (Blocks.join ep00000111_19 ep00000111_20)) (Blocks.join (Blocks.join ep00000111_21 ep00000111_22) (Blocks.join ep00000111_23 ep00000111_24))) (Blocks.join (Blocks.join (Blocks.join ep00000111_25 ep00000111_26) (Blocks.join ep00000111_27 ep00000111_28)) (Blocks.join (Blocks.join ep00000111_29 ep00000111_30) (Blocks.join ep00000111_31 (Blocks.join ep00000111_32 ep00000111_33))))))
private def ptsp00000111 : List ℤ := [((2:ℤ)^2819+0),((2:ℤ)^2819+1),((2:ℤ)^2819+2)]
private theorem boundp00000111 : 2^vp0000011.size*absSum vp0000011.list + ((2:ℤ)^4439*absSum vp00000111.list+absSum ep00000111.list) < (2:ℤ)^6710 := by decide +kernel
private theorem pointp00000111_0 : fastHom 1 ((2:ℤ)^2819+0) vp0000011 = ((2:ℤ)^4439)*vp00000111.subst ((2:ℤ)^2819+0)+ep00000111.subst ((2:ℤ)^2819+0) := by decide +kernel
private theorem pointp00000111_1 : fastHom 1 ((2:ℤ)^2819+1) vp0000011 = ((2:ℤ)^4439)*vp00000111.subst ((2:ℤ)^2819+1)+ep00000111.subst ((2:ℤ)^2819+1) := by decide +kernel
private theorem pointp00000111_2 : fastHom 1 ((2:ℤ)^2819+2) vp0000011 = ((2:ℤ)^4439)*vp00000111.subst ((2:ℤ)^2819+2)+ep00000111.subst ((2:ℤ)^2819+2) := by decide +kernel
private theorem checkp00000111 (x:ℤ) (hx:x ∈ ptsp00000111) : fastHom 1 x vp0000011 = ((2:ℤ)^4439)*vp00000111.subst x+ep00000111.subst x := by
  simp only [ptsp00000111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp00000111_0
  · exact pointp00000111_1
  · exact pointp00000111_2
private theorem idp00000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011.list =
    C ((2:ℤ)^4439) * horner X vp00000111.list + horner X ep00000111.list := by
  apply edge_identity (B := (2:ℤ)^6710) (by decide) (by positivity) (by positivity) boundp00000111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00000111 (by decide +kernel)
  · have h : ptsp00000111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00000111.trans_le (by decide +kernel)
  · exact checkp00000111
private theorem bp00000111 : Branch 1 (-191761639/64000000 : ℚ) vp0000011 := by
  apply branch_checked idp00000111 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-223761639/32000000 : ℚ) by norm_num]
  exact coverp00000111
theorem coverp0000011 : Covers (-191761639/64000000 : ℚ) vp0000011 := join_branches bp00000110 bp00000111
end NextProof.EdgeFull

