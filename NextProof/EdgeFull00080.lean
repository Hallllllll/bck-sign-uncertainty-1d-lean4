import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00077
import NextProof.EdgeFull00079

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000110_0 : Blocks := edgeBlocks% "full/vectors/000110-V-0000.bin"
private noncomputable def vp000110_1 : Blocks := edgeBlocks% "full/vectors/000110-V-0001.bin"
private noncomputable def vp000110_2 : Blocks := edgeBlocks% "full/vectors/000110-V-0002.bin"
private noncomputable def vp000110_3 : Blocks := edgeBlocks% "full/vectors/000110-V-0003.bin"
private noncomputable def vp000110_4 : Blocks := edgeBlocks% "full/vectors/000110-V-0004.bin"
private noncomputable def vp000110_5 : Blocks := edgeBlocks% "full/vectors/000110-V-0005.bin"
private noncomputable def vp000110_6 : Blocks := edgeBlocks% "full/vectors/000110-V-0006.bin"
private noncomputable def vp000110_7 : Blocks := edgeBlocks% "full/vectors/000110-V-0007.bin"
private noncomputable def vp000110_8 : Blocks := edgeBlocks% "full/vectors/000110-V-0008.bin"
private noncomputable def vp000110_9 : Blocks := edgeBlocks% "full/vectors/000110-V-0009.bin"
private noncomputable def vp000110_10 : Blocks := edgeBlocks% "full/vectors/000110-V-0010.bin"
private noncomputable def vp000110_11 : Blocks := edgeBlocks% "full/vectors/000110-V-0011.bin"
private noncomputable def vp000110_12 : Blocks := edgeBlocks% "full/vectors/000110-V-0012.bin"
private noncomputable def vp000110_13 : Blocks := edgeBlocks% "full/vectors/000110-V-0013.bin"
private noncomputable def vp000110_14 : Blocks := edgeBlocks% "full/vectors/000110-V-0014.bin"
private noncomputable def vp000110_15 : Blocks := edgeBlocks% "full/vectors/000110-V-0015.bin"
private noncomputable def vp000110_16 : Blocks := edgeBlocks% "full/vectors/000110-V-0016.bin"
private noncomputable def vp000110_17 : Blocks := edgeBlocks% "full/vectors/000110-V-0017.bin"
private noncomputable def vp000110_18 : Blocks := edgeBlocks% "full/vectors/000110-V-0018.bin"
private noncomputable def vp000110_19 : Blocks := edgeBlocks% "full/vectors/000110-V-0019.bin"
private noncomputable def vp000110_20 : Blocks := edgeBlocks% "full/vectors/000110-V-0020.bin"
private noncomputable def vp000110_21 : Blocks := edgeBlocks% "full/vectors/000110-V-0021.bin"
private noncomputable def vp000110_22 : Blocks := edgeBlocks% "full/vectors/000110-V-0022.bin"
private noncomputable def vp000110_23 : Blocks := edgeBlocks% "full/vectors/000110-V-0023.bin"
private noncomputable def vp000110_24 : Blocks := edgeBlocks% "full/vectors/000110-V-0024.bin"
private noncomputable def vp000110_25 : Blocks := edgeBlocks% "full/vectors/000110-V-0025.bin"
private noncomputable def vp000110_26 : Blocks := edgeBlocks% "full/vectors/000110-V-0026.bin"
private noncomputable def vp000110_27 : Blocks := edgeBlocks% "full/vectors/000110-V-0027.bin"
private noncomputable def vp000110_28 : Blocks := edgeBlocks% "full/vectors/000110-V-0028.bin"
private noncomputable def vp000110_29 : Blocks := edgeBlocks% "full/vectors/000110-V-0029.bin"
private noncomputable def vp000110_30 : Blocks := edgeBlocks% "full/vectors/000110-V-0030.bin"
private noncomputable def vp000110_31 : Blocks := edgeBlocks% "full/vectors/000110-V-0031.bin"
private noncomputable def vp000110_32 : Blocks := edgeBlocks% "full/vectors/000110-V-0032.bin"
private noncomputable def vp000110_33 : Blocks := edgeBlocks% "full/vectors/000110-V-0033.bin"
noncomputable def vp000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000110_0 vp000110_1) (Blocks.join vp000110_2 vp000110_3)) (Blocks.join (Blocks.join vp000110_4 vp000110_5) (Blocks.join vp000110_6 vp000110_7))) (Blocks.join (Blocks.join (Blocks.join vp000110_8 vp000110_9) (Blocks.join vp000110_10 vp000110_11)) (Blocks.join (Blocks.join vp000110_12 vp000110_13) (Blocks.join vp000110_14 (Blocks.join vp000110_15 vp000110_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000110_17 vp000110_18) (Blocks.join vp000110_19 vp000110_20)) (Blocks.join (Blocks.join vp000110_21 vp000110_22) (Blocks.join vp000110_23 vp000110_24))) (Blocks.join (Blocks.join (Blocks.join vp000110_25 vp000110_26) (Blocks.join vp000110_27 vp000110_28)) (Blocks.join (Blocks.join vp000110_29 vp000110_30) (Blocks.join vp000110_31 (Blocks.join vp000110_32 vp000110_33))))))
private theorem bp0001100 : Branch 0 (-767761639/128000000 : ℚ) vp000110 := by
  apply branch_left_normalized (c:=vp0001100) (k:=0) (m:=2215) (by decide +kernel)
  rw [show 2*(-767761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/64000000 : ℚ) by norm_num]
  exact coverp0001100
private noncomputable def ep0001101_0 : Blocks := edgeBlocks% "full/vectors/0001101-E-0000.bin"
private noncomputable def ep0001101_1 : Blocks := edgeBlocks% "full/vectors/0001101-E-0001.bin"
private noncomputable def ep0001101_2 : Blocks := edgeBlocks% "full/vectors/0001101-E-0002.bin"
private noncomputable def ep0001101_3 : Blocks := edgeBlocks% "full/vectors/0001101-E-0003.bin"
private noncomputable def ep0001101_4 : Blocks := edgeBlocks% "full/vectors/0001101-E-0004.bin"
private noncomputable def ep0001101_5 : Blocks := edgeBlocks% "full/vectors/0001101-E-0005.bin"
private noncomputable def ep0001101_6 : Blocks := edgeBlocks% "full/vectors/0001101-E-0006.bin"
private noncomputable def ep0001101_7 : Blocks := edgeBlocks% "full/vectors/0001101-E-0007.bin"
private noncomputable def ep0001101_8 : Blocks := edgeBlocks% "full/vectors/0001101-E-0008.bin"
private noncomputable def ep0001101_9 : Blocks := edgeBlocks% "full/vectors/0001101-E-0009.bin"
private noncomputable def ep0001101_10 : Blocks := edgeBlocks% "full/vectors/0001101-E-0010.bin"
private noncomputable def ep0001101_11 : Blocks := edgeBlocks% "full/vectors/0001101-E-0011.bin"
private noncomputable def ep0001101_12 : Blocks := edgeBlocks% "full/vectors/0001101-E-0012.bin"
private noncomputable def ep0001101_13 : Blocks := edgeBlocks% "full/vectors/0001101-E-0013.bin"
private noncomputable def ep0001101_14 : Blocks := edgeBlocks% "full/vectors/0001101-E-0014.bin"
private noncomputable def ep0001101_15 : Blocks := edgeBlocks% "full/vectors/0001101-E-0015.bin"
private noncomputable def ep0001101_16 : Blocks := edgeBlocks% "full/vectors/0001101-E-0016.bin"
private noncomputable def ep0001101_17 : Blocks := edgeBlocks% "full/vectors/0001101-E-0017.bin"
private noncomputable def ep0001101_18 : Blocks := edgeBlocks% "full/vectors/0001101-E-0018.bin"
private noncomputable def ep0001101_19 : Blocks := edgeBlocks% "full/vectors/0001101-E-0019.bin"
private noncomputable def ep0001101_20 : Blocks := edgeBlocks% "full/vectors/0001101-E-0020.bin"
private noncomputable def ep0001101_21 : Blocks := edgeBlocks% "full/vectors/0001101-E-0021.bin"
private noncomputable def ep0001101_22 : Blocks := edgeBlocks% "full/vectors/0001101-E-0022.bin"
private noncomputable def ep0001101_23 : Blocks := edgeBlocks% "full/vectors/0001101-E-0023.bin"
private noncomputable def ep0001101_24 : Blocks := edgeBlocks% "full/vectors/0001101-E-0024.bin"
private noncomputable def ep0001101_25 : Blocks := edgeBlocks% "full/vectors/0001101-E-0025.bin"
private noncomputable def ep0001101_26 : Blocks := edgeBlocks% "full/vectors/0001101-E-0026.bin"
private noncomputable def ep0001101_27 : Blocks := edgeBlocks% "full/vectors/0001101-E-0027.bin"
private noncomputable def ep0001101_28 : Blocks := edgeBlocks% "full/vectors/0001101-E-0028.bin"
private noncomputable def ep0001101_29 : Blocks := edgeBlocks% "full/vectors/0001101-E-0029.bin"
private noncomputable def ep0001101_30 : Blocks := edgeBlocks% "full/vectors/0001101-E-0030.bin"
private noncomputable def ep0001101_31 : Blocks := edgeBlocks% "full/vectors/0001101-E-0031.bin"
private noncomputable def ep0001101_32 : Blocks := edgeBlocks% "full/vectors/0001101-E-0032.bin"
private noncomputable def ep0001101_33 : Blocks := edgeBlocks% "full/vectors/0001101-E-0033.bin"
noncomputable def ep0001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001101_0 ep0001101_1) (Blocks.join ep0001101_2 ep0001101_3)) (Blocks.join (Blocks.join ep0001101_4 ep0001101_5) (Blocks.join ep0001101_6 ep0001101_7))) (Blocks.join (Blocks.join (Blocks.join ep0001101_8 ep0001101_9) (Blocks.join ep0001101_10 ep0001101_11)) (Blocks.join (Blocks.join ep0001101_12 ep0001101_13) (Blocks.join ep0001101_14 (Blocks.join ep0001101_15 ep0001101_16))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001101_17 ep0001101_18) (Blocks.join ep0001101_19 ep0001101_20)) (Blocks.join (Blocks.join ep0001101_21 ep0001101_22) (Blocks.join ep0001101_23 ep0001101_24))) (Blocks.join (Blocks.join (Blocks.join ep0001101_25 ep0001101_26) (Blocks.join ep0001101_27 ep0001101_28)) (Blocks.join (Blocks.join ep0001101_29 ep0001101_30) (Blocks.join ep0001101_31 (Blocks.join ep0001101_32 ep0001101_33))))))
private def ptsp0001101 : List ℤ := [((2:ℤ)^2820+0),((2:ℤ)^2820+1),((2:ℤ)^2820+2)]
private theorem boundp0001101 : 2^vp000110.size*absSum vp000110.list + ((2:ℤ)^4633*absSum vp0001101.list+absSum ep0001101.list) < (2:ℤ)^6707 := by decide +kernel
private theorem pointp0001101_0 : fastHom 1 ((2:ℤ)^2820+0) vp000110 = ((2:ℤ)^4633)*vp0001101.subst ((2:ℤ)^2820+0)+ep0001101.subst ((2:ℤ)^2820+0) := by decide +kernel
private theorem pointp0001101_1 : fastHom 1 ((2:ℤ)^2820+1) vp000110 = ((2:ℤ)^4633)*vp0001101.subst ((2:ℤ)^2820+1)+ep0001101.subst ((2:ℤ)^2820+1) := by decide +kernel
private theorem pointp0001101_2 : fastHom 1 ((2:ℤ)^2820+2) vp000110 = ((2:ℤ)^4633)*vp0001101.subst ((2:ℤ)^2820+2)+ep0001101.subst ((2:ℤ)^2820+2) := by decide +kernel
private theorem checkp0001101 (x:ℤ) (hx:x ∈ ptsp0001101) : fastHom 1 x vp000110 = ((2:ℤ)^4633)*vp0001101.subst x+ep0001101.subst x := by
  simp only [ptsp0001101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp0001101_0
  · exact pointp0001101_1
  · exact pointp0001101_2
private theorem idp0001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110.list =
    C ((2:ℤ)^4633) * horner X vp0001101.list + horner X ep0001101.list := by
  apply edge_identity (B := (2:ℤ)^6707) (by decide) (by positivity) (by positivity) boundp0001101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0001101 (by decide +kernel)
  · have h : ptsp0001101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0001101.trans_le (by decide +kernel)
  · exact checkp0001101
private theorem bp0001101 : Branch 1 (-767761639/128000000 : ℚ) vp000110 := by
  apply branch_checked idp0001101 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-831761639/64000000 : ℚ) by norm_num]
  exact coverp0001101
theorem coverp000110 : Covers (-767761639/128000000 : ℚ) vp000110 := join_branches bp0001100 bp0001101
end NextProof.EdgeFull

