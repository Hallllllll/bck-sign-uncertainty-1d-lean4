import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00071
import NextProof.EdgeFull00073

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000101_0 : Blocks := edgeBlocks% "full/vectors/000101-V-0000.bin"
private noncomputable def vp000101_1 : Blocks := edgeBlocks% "full/vectors/000101-V-0001.bin"
private noncomputable def vp000101_2 : Blocks := edgeBlocks% "full/vectors/000101-V-0002.bin"
private noncomputable def vp000101_3 : Blocks := edgeBlocks% "full/vectors/000101-V-0003.bin"
private noncomputable def vp000101_4 : Blocks := edgeBlocks% "full/vectors/000101-V-0004.bin"
private noncomputable def vp000101_5 : Blocks := edgeBlocks% "full/vectors/000101-V-0005.bin"
private noncomputable def vp000101_6 : Blocks := edgeBlocks% "full/vectors/000101-V-0006.bin"
private noncomputable def vp000101_7 : Blocks := edgeBlocks% "full/vectors/000101-V-0007.bin"
private noncomputable def vp000101_8 : Blocks := edgeBlocks% "full/vectors/000101-V-0008.bin"
private noncomputable def vp000101_9 : Blocks := edgeBlocks% "full/vectors/000101-V-0009.bin"
private noncomputable def vp000101_10 : Blocks := edgeBlocks% "full/vectors/000101-V-0010.bin"
private noncomputable def vp000101_11 : Blocks := edgeBlocks% "full/vectors/000101-V-0011.bin"
private noncomputable def vp000101_12 : Blocks := edgeBlocks% "full/vectors/000101-V-0012.bin"
private noncomputable def vp000101_13 : Blocks := edgeBlocks% "full/vectors/000101-V-0013.bin"
private noncomputable def vp000101_14 : Blocks := edgeBlocks% "full/vectors/000101-V-0014.bin"
private noncomputable def vp000101_15 : Blocks := edgeBlocks% "full/vectors/000101-V-0015.bin"
private noncomputable def vp000101_16 : Blocks := edgeBlocks% "full/vectors/000101-V-0016.bin"
private noncomputable def vp000101_17 : Blocks := edgeBlocks% "full/vectors/000101-V-0017.bin"
private noncomputable def vp000101_18 : Blocks := edgeBlocks% "full/vectors/000101-V-0018.bin"
private noncomputable def vp000101_19 : Blocks := edgeBlocks% "full/vectors/000101-V-0019.bin"
private noncomputable def vp000101_20 : Blocks := edgeBlocks% "full/vectors/000101-V-0020.bin"
private noncomputable def vp000101_21 : Blocks := edgeBlocks% "full/vectors/000101-V-0021.bin"
private noncomputable def vp000101_22 : Blocks := edgeBlocks% "full/vectors/000101-V-0022.bin"
private noncomputable def vp000101_23 : Blocks := edgeBlocks% "full/vectors/000101-V-0023.bin"
private noncomputable def vp000101_24 : Blocks := edgeBlocks% "full/vectors/000101-V-0024.bin"
private noncomputable def vp000101_25 : Blocks := edgeBlocks% "full/vectors/000101-V-0025.bin"
private noncomputable def vp000101_26 : Blocks := edgeBlocks% "full/vectors/000101-V-0026.bin"
private noncomputable def vp000101_27 : Blocks := edgeBlocks% "full/vectors/000101-V-0027.bin"
private noncomputable def vp000101_28 : Blocks := edgeBlocks% "full/vectors/000101-V-0028.bin"
private noncomputable def vp000101_29 : Blocks := edgeBlocks% "full/vectors/000101-V-0029.bin"
private noncomputable def vp000101_30 : Blocks := edgeBlocks% "full/vectors/000101-V-0030.bin"
private noncomputable def vp000101_31 : Blocks := edgeBlocks% "full/vectors/000101-V-0031.bin"
private noncomputable def vp000101_32 : Blocks := edgeBlocks% "full/vectors/000101-V-0032.bin"
private noncomputable def vp000101_33 : Blocks := edgeBlocks% "full/vectors/000101-V-0033.bin"
private noncomputable def vp000101_34 : Blocks := edgeBlocks% "full/vectors/000101-V-0034.bin"
private noncomputable def vp000101_35 : Blocks := edgeBlocks% "full/vectors/000101-V-0035.bin"
private noncomputable def vp000101_36 : Blocks := edgeBlocks% "full/vectors/000101-V-0036.bin"
noncomputable def vp000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000101_0 vp000101_1) (Blocks.join vp000101_2 vp000101_3)) (Blocks.join (Blocks.join vp000101_4 vp000101_5) (Blocks.join vp000101_6 (Blocks.join vp000101_7 vp000101_8)))) (Blocks.join (Blocks.join (Blocks.join vp000101_9 vp000101_10) (Blocks.join vp000101_11 vp000101_12)) (Blocks.join (Blocks.join vp000101_13 vp000101_14) (Blocks.join vp000101_15 (Blocks.join vp000101_16 vp000101_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000101_18 vp000101_19) (Blocks.join vp000101_20 vp000101_21)) (Blocks.join (Blocks.join vp000101_22 vp000101_23) (Blocks.join vp000101_24 (Blocks.join vp000101_25 vp000101_26)))) (Blocks.join (Blocks.join (Blocks.join vp000101_27 vp000101_28) (Blocks.join vp000101_29 (Blocks.join vp000101_30 vp000101_31))) (Blocks.join (Blocks.join vp000101_32 vp000101_33) (Blocks.join vp000101_34 (Blocks.join vp000101_35 vp000101_36))))))
private theorem bp0001010 : Branch 0 (-639761639/128000000 : ℚ) vp000101 := by
  apply branch_left_normalized (c:=vp0001010) (k:=0) (m:=2418) (by decide +kernel)
  rw [show 2*(-639761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/64000000 : ℚ) by norm_num]
  exact coverp0001010
private noncomputable def ep0001011_0 : Blocks := edgeBlocks% "full/vectors/0001011-E-0000.bin"
private noncomputable def ep0001011_1 : Blocks := edgeBlocks% "full/vectors/0001011-E-0001.bin"
private noncomputable def ep0001011_2 : Blocks := edgeBlocks% "full/vectors/0001011-E-0002.bin"
private noncomputable def ep0001011_3 : Blocks := edgeBlocks% "full/vectors/0001011-E-0003.bin"
private noncomputable def ep0001011_4 : Blocks := edgeBlocks% "full/vectors/0001011-E-0004.bin"
private noncomputable def ep0001011_5 : Blocks := edgeBlocks% "full/vectors/0001011-E-0005.bin"
private noncomputable def ep0001011_6 : Blocks := edgeBlocks% "full/vectors/0001011-E-0006.bin"
private noncomputable def ep0001011_7 : Blocks := edgeBlocks% "full/vectors/0001011-E-0007.bin"
private noncomputable def ep0001011_8 : Blocks := edgeBlocks% "full/vectors/0001011-E-0008.bin"
private noncomputable def ep0001011_9 : Blocks := edgeBlocks% "full/vectors/0001011-E-0009.bin"
private noncomputable def ep0001011_10 : Blocks := edgeBlocks% "full/vectors/0001011-E-0010.bin"
private noncomputable def ep0001011_11 : Blocks := edgeBlocks% "full/vectors/0001011-E-0011.bin"
private noncomputable def ep0001011_12 : Blocks := edgeBlocks% "full/vectors/0001011-E-0012.bin"
private noncomputable def ep0001011_13 : Blocks := edgeBlocks% "full/vectors/0001011-E-0013.bin"
private noncomputable def ep0001011_14 : Blocks := edgeBlocks% "full/vectors/0001011-E-0014.bin"
private noncomputable def ep0001011_15 : Blocks := edgeBlocks% "full/vectors/0001011-E-0015.bin"
private noncomputable def ep0001011_16 : Blocks := edgeBlocks% "full/vectors/0001011-E-0016.bin"
private noncomputable def ep0001011_17 : Blocks := edgeBlocks% "full/vectors/0001011-E-0017.bin"
private noncomputable def ep0001011_18 : Blocks := edgeBlocks% "full/vectors/0001011-E-0018.bin"
private noncomputable def ep0001011_19 : Blocks := edgeBlocks% "full/vectors/0001011-E-0019.bin"
private noncomputable def ep0001011_20 : Blocks := edgeBlocks% "full/vectors/0001011-E-0020.bin"
private noncomputable def ep0001011_21 : Blocks := edgeBlocks% "full/vectors/0001011-E-0021.bin"
private noncomputable def ep0001011_22 : Blocks := edgeBlocks% "full/vectors/0001011-E-0022.bin"
private noncomputable def ep0001011_23 : Blocks := edgeBlocks% "full/vectors/0001011-E-0023.bin"
private noncomputable def ep0001011_24 : Blocks := edgeBlocks% "full/vectors/0001011-E-0024.bin"
private noncomputable def ep0001011_25 : Blocks := edgeBlocks% "full/vectors/0001011-E-0025.bin"
private noncomputable def ep0001011_26 : Blocks := edgeBlocks% "full/vectors/0001011-E-0026.bin"
private noncomputable def ep0001011_27 : Blocks := edgeBlocks% "full/vectors/0001011-E-0027.bin"
private noncomputable def ep0001011_28 : Blocks := edgeBlocks% "full/vectors/0001011-E-0028.bin"
private noncomputable def ep0001011_29 : Blocks := edgeBlocks% "full/vectors/0001011-E-0029.bin"
private noncomputable def ep0001011_30 : Blocks := edgeBlocks% "full/vectors/0001011-E-0030.bin"
private noncomputable def ep0001011_31 : Blocks := edgeBlocks% "full/vectors/0001011-E-0031.bin"
private noncomputable def ep0001011_32 : Blocks := edgeBlocks% "full/vectors/0001011-E-0032.bin"
private noncomputable def ep0001011_33 : Blocks := edgeBlocks% "full/vectors/0001011-E-0033.bin"
private noncomputable def ep0001011_34 : Blocks := edgeBlocks% "full/vectors/0001011-E-0034.bin"
private noncomputable def ep0001011_35 : Blocks := edgeBlocks% "full/vectors/0001011-E-0035.bin"
private noncomputable def ep0001011_36 : Blocks := edgeBlocks% "full/vectors/0001011-E-0036.bin"
noncomputable def ep0001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001011_0 ep0001011_1) (Blocks.join ep0001011_2 ep0001011_3)) (Blocks.join (Blocks.join ep0001011_4 ep0001011_5) (Blocks.join ep0001011_6 (Blocks.join ep0001011_7 ep0001011_8)))) (Blocks.join (Blocks.join (Blocks.join ep0001011_9 ep0001011_10) (Blocks.join ep0001011_11 ep0001011_12)) (Blocks.join (Blocks.join ep0001011_13 ep0001011_14) (Blocks.join ep0001011_15 (Blocks.join ep0001011_16 ep0001011_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0001011_18 ep0001011_19) (Blocks.join ep0001011_20 ep0001011_21)) (Blocks.join (Blocks.join ep0001011_22 ep0001011_23) (Blocks.join ep0001011_24 (Blocks.join ep0001011_25 ep0001011_26)))) (Blocks.join (Blocks.join (Blocks.join ep0001011_27 ep0001011_28) (Blocks.join ep0001011_29 (Blocks.join ep0001011_30 ep0001011_31))) (Blocks.join (Blocks.join ep0001011_32 ep0001011_33) (Blocks.join ep0001011_34 (Blocks.join ep0001011_35 ep0001011_36))))))
private def ptsp0001011 : List ℤ := [((2:ℤ)^2592+0),((2:ℤ)^2592+1),((2:ℤ)^2592+2)]
private theorem boundp0001011 : 2^vp000101.size*absSum vp000101.list + ((2:ℤ)^4998*absSum vp0001011.list+absSum ep0001011.list) < (2:ℤ)^7300 := by decide +kernel
private theorem pointp0001011_0 : fastHom 1 ((2:ℤ)^2592+0) vp000101 = ((2:ℤ)^4998)*vp0001011.subst ((2:ℤ)^2592+0)+ep0001011.subst ((2:ℤ)^2592+0) := by decide +kernel
private theorem pointp0001011_1 : fastHom 1 ((2:ℤ)^2592+1) vp000101 = ((2:ℤ)^4998)*vp0001011.subst ((2:ℤ)^2592+1)+ep0001011.subst ((2:ℤ)^2592+1) := by decide +kernel
private theorem pointp0001011_2 : fastHom 1 ((2:ℤ)^2592+2) vp000101 = ((2:ℤ)^4998)*vp0001011.subst ((2:ℤ)^2592+2)+ep0001011.subst ((2:ℤ)^2592+2) := by decide +kernel
private theorem checkp0001011 (x:ℤ) (hx:x ∈ ptsp0001011) : fastHom 1 x vp000101 = ((2:ℤ)^4998)*vp0001011.subst x+ep0001011.subst x := by
  simp only [ptsp0001011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp0001011_0
  · exact pointp0001011_1
  · exact pointp0001011_2
private theorem idp0001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101.list =
    C ((2:ℤ)^4998) * horner X vp0001011.list + horner X ep0001011.list := by
  apply edge_identity (B := (2:ℤ)^7300) (by decide) (by positivity) (by positivity) boundp0001011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0001011 (by decide +kernel)
  · have h : ptsp0001011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0001011.trans_le (by decide +kernel)
  · exact checkp0001011
private theorem bp0001011 : Branch 1 (-639761639/128000000 : ℚ) vp000101 := by
  apply branch_checked idp0001011 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-703761639/64000000 : ℚ) by norm_num]
  exact coverp0001011
theorem coverp000101 : Covers (-639761639/128000000 : ℚ) vp000101 := join_branches bp0001010 bp0001011
end NextProof.EdgeFull

