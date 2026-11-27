import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00021
import NextProof.EdgeFull00023

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000001_0 : Blocks := edgeBlocks% "full/vectors/000000001-V-0000.bin"
private noncomputable def vp000000001_1 : Blocks := edgeBlocks% "full/vectors/000000001-V-0001.bin"
private noncomputable def vp000000001_2 : Blocks := edgeBlocks% "full/vectors/000000001-V-0002.bin"
private noncomputable def vp000000001_3 : Blocks := edgeBlocks% "full/vectors/000000001-V-0003.bin"
private noncomputable def vp000000001_4 : Blocks := edgeBlocks% "full/vectors/000000001-V-0004.bin"
private noncomputable def vp000000001_5 : Blocks := edgeBlocks% "full/vectors/000000001-V-0005.bin"
private noncomputable def vp000000001_6 : Blocks := edgeBlocks% "full/vectors/000000001-V-0006.bin"
private noncomputable def vp000000001_7 : Blocks := edgeBlocks% "full/vectors/000000001-V-0007.bin"
private noncomputable def vp000000001_8 : Blocks := edgeBlocks% "full/vectors/000000001-V-0008.bin"
private noncomputable def vp000000001_9 : Blocks := edgeBlocks% "full/vectors/000000001-V-0009.bin"
private noncomputable def vp000000001_10 : Blocks := edgeBlocks% "full/vectors/000000001-V-0010.bin"
private noncomputable def vp000000001_11 : Blocks := edgeBlocks% "full/vectors/000000001-V-0011.bin"
private noncomputable def vp000000001_12 : Blocks := edgeBlocks% "full/vectors/000000001-V-0012.bin"
private noncomputable def vp000000001_13 : Blocks := edgeBlocks% "full/vectors/000000001-V-0013.bin"
private noncomputable def vp000000001_14 : Blocks := edgeBlocks% "full/vectors/000000001-V-0014.bin"
private noncomputable def vp000000001_15 : Blocks := edgeBlocks% "full/vectors/000000001-V-0015.bin"
private noncomputable def vp000000001_16 : Blocks := edgeBlocks% "full/vectors/000000001-V-0016.bin"
private noncomputable def vp000000001_17 : Blocks := edgeBlocks% "full/vectors/000000001-V-0017.bin"
private noncomputable def vp000000001_18 : Blocks := edgeBlocks% "full/vectors/000000001-V-0018.bin"
private noncomputable def vp000000001_19 : Blocks := edgeBlocks% "full/vectors/000000001-V-0019.bin"
private noncomputable def vp000000001_20 : Blocks := edgeBlocks% "full/vectors/000000001-V-0020.bin"
private noncomputable def vp000000001_21 : Blocks := edgeBlocks% "full/vectors/000000001-V-0021.bin"
private noncomputable def vp000000001_22 : Blocks := edgeBlocks% "full/vectors/000000001-V-0022.bin"
private noncomputable def vp000000001_23 : Blocks := edgeBlocks% "full/vectors/000000001-V-0023.bin"
private noncomputable def vp000000001_24 : Blocks := edgeBlocks% "full/vectors/000000001-V-0024.bin"
private noncomputable def vp000000001_25 : Blocks := edgeBlocks% "full/vectors/000000001-V-0025.bin"
private noncomputable def vp000000001_26 : Blocks := edgeBlocks% "full/vectors/000000001-V-0026.bin"
noncomputable def vp000000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000000001_0 (Blocks.join vp000000001_1 vp000000001_2)) (Blocks.join vp000000001_3 (Blocks.join vp000000001_4 vp000000001_5))) (Blocks.join (Blocks.join vp000000001_6 (Blocks.join vp000000001_7 vp000000001_8)) (Blocks.join (Blocks.join vp000000001_9 vp000000001_10) (Blocks.join vp000000001_11 vp000000001_12)))) (Blocks.join (Blocks.join (Blocks.join vp000000001_13 (Blocks.join vp000000001_14 vp000000001_15)) (Blocks.join (Blocks.join vp000000001_16 vp000000001_17) (Blocks.join vp000000001_18 vp000000001_19))) (Blocks.join (Blocks.join vp000000001_20 (Blocks.join vp000000001_21 vp000000001_22)) (Blocks.join (Blocks.join vp000000001_23 vp000000001_24) (Blocks.join vp000000001_25 vp000000001_26)))))
private theorem bp0000000010 : Branch 0 (-15761639/16000000 : ℚ) vp000000001 := by
  apply branch_left_normalized (c:=vp0000000010) (k:=0) (m:=1933) (by decide +kernel)
  rw [show 2*(-15761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-15761639/8000000 : ℚ) by norm_num]
  exact coverp0000000010
private noncomputable def ep0000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0000.bin"
private noncomputable def ep0000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0001.bin"
private noncomputable def ep0000000011_2 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0002.bin"
private noncomputable def ep0000000011_3 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0003.bin"
private noncomputable def ep0000000011_4 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0004.bin"
private noncomputable def ep0000000011_5 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0005.bin"
private noncomputable def ep0000000011_6 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0006.bin"
private noncomputable def ep0000000011_7 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0007.bin"
private noncomputable def ep0000000011_8 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0008.bin"
private noncomputable def ep0000000011_9 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0009.bin"
private noncomputable def ep0000000011_10 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0010.bin"
private noncomputable def ep0000000011_11 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0011.bin"
private noncomputable def ep0000000011_12 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0012.bin"
private noncomputable def ep0000000011_13 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0013.bin"
private noncomputable def ep0000000011_14 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0014.bin"
private noncomputable def ep0000000011_15 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0015.bin"
private noncomputable def ep0000000011_16 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0016.bin"
private noncomputable def ep0000000011_17 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0017.bin"
private noncomputable def ep0000000011_18 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0018.bin"
private noncomputable def ep0000000011_19 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0019.bin"
private noncomputable def ep0000000011_20 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0020.bin"
private noncomputable def ep0000000011_21 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0021.bin"
private noncomputable def ep0000000011_22 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0022.bin"
private noncomputable def ep0000000011_23 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0023.bin"
private noncomputable def ep0000000011_24 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0024.bin"
private noncomputable def ep0000000011_25 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0025.bin"
private noncomputable def ep0000000011_26 : Blocks := edgeBlocks% "full/vectors/0000000011-E-0026.bin"
noncomputable def ep0000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000000011_0 (Blocks.join ep0000000011_1 ep0000000011_2)) (Blocks.join ep0000000011_3 (Blocks.join ep0000000011_4 ep0000000011_5))) (Blocks.join (Blocks.join ep0000000011_6 (Blocks.join ep0000000011_7 ep0000000011_8)) (Blocks.join (Blocks.join ep0000000011_9 ep0000000011_10) (Blocks.join ep0000000011_11 ep0000000011_12)))) (Blocks.join (Blocks.join (Blocks.join ep0000000011_13 (Blocks.join ep0000000011_14 ep0000000011_15)) (Blocks.join (Blocks.join ep0000000011_16 ep0000000011_17) (Blocks.join ep0000000011_18 ep0000000011_19))) (Blocks.join (Blocks.join ep0000000011_20 (Blocks.join ep0000000011_21 ep0000000011_22)) (Blocks.join (Blocks.join ep0000000011_23 ep0000000011_24) (Blocks.join ep0000000011_25 ep0000000011_26)))))
private def ptsp0000000011 : List ℤ := [((2:ℤ)^3510+0),((2:ℤ)^3510+1)]
private theorem boundp0000000011 : 2^vp000000001.size*absSum vp000000001.list + ((2:ℤ)^3479*absSum vp0000000011.list+absSum ep0000000011.list) < (2:ℤ)^5567 := by decide +kernel
private theorem pointp0000000011_0 : fastHom 1 ((2:ℤ)^3510+0) vp000000001 = ((2:ℤ)^3479)*vp0000000011.subst ((2:ℤ)^3510+0)+ep0000000011.subst ((2:ℤ)^3510+0) := by decide +kernel
private theorem pointp0000000011_1 : fastHom 1 ((2:ℤ)^3510+1) vp000000001 = ((2:ℤ)^3479)*vp0000000011.subst ((2:ℤ)^3510+1)+ep0000000011.subst ((2:ℤ)^3510+1) := by decide +kernel
private theorem checkp0000000011 (x:ℤ) (hx:x ∈ ptsp0000000011) : fastHom 1 x vp000000001 = ((2:ℤ)^3479)*vp0000000011.subst x+ep0000000011.subst x := by
  simp only [ptsp0000000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0000000011_0
  · exact pointp0000000011_1
private theorem idp0000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001.list =
    C ((2:ℤ)^3479) * horner X vp0000000011.list + horner X ep0000000011.list := by
  apply edge_identity (B := (2:ℤ)^5567) (by decide) (by positivity) (by positivity) boundp0000000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000000011 (by decide +kernel)
  · have h : ptsp0000000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000000011.trans_le (by decide +kernel)
  · exact checkp0000000011
private theorem bp0000000011 : Branch 1 (-15761639/16000000 : ℚ) vp000000001 := by
  apply branch_checked idp0000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-15761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-23761639/8000000 : ℚ) by norm_num]
  exact coverp0000000011
theorem coverp000000001 : Covers (-15761639/16000000 : ℚ) vp000000001 := join_branches bp0000000010 bp0000000011
end NextProof.EdgeFull

