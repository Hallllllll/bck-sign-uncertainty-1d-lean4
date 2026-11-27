import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00059
import NextProof.EdgeFull00061

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000011_0 : Blocks := edgeBlocks% "full/vectors/000011-V-0000.bin"
private noncomputable def vp000011_1 : Blocks := edgeBlocks% "full/vectors/000011-V-0001.bin"
private noncomputable def vp000011_2 : Blocks := edgeBlocks% "full/vectors/000011-V-0002.bin"
private noncomputable def vp000011_3 : Blocks := edgeBlocks% "full/vectors/000011-V-0003.bin"
private noncomputable def vp000011_4 : Blocks := edgeBlocks% "full/vectors/000011-V-0004.bin"
private noncomputable def vp000011_5 : Blocks := edgeBlocks% "full/vectors/000011-V-0005.bin"
private noncomputable def vp000011_6 : Blocks := edgeBlocks% "full/vectors/000011-V-0006.bin"
private noncomputable def vp000011_7 : Blocks := edgeBlocks% "full/vectors/000011-V-0007.bin"
private noncomputable def vp000011_8 : Blocks := edgeBlocks% "full/vectors/000011-V-0008.bin"
private noncomputable def vp000011_9 : Blocks := edgeBlocks% "full/vectors/000011-V-0009.bin"
private noncomputable def vp000011_10 : Blocks := edgeBlocks% "full/vectors/000011-V-0010.bin"
private noncomputable def vp000011_11 : Blocks := edgeBlocks% "full/vectors/000011-V-0011.bin"
private noncomputable def vp000011_12 : Blocks := edgeBlocks% "full/vectors/000011-V-0012.bin"
private noncomputable def vp000011_13 : Blocks := edgeBlocks% "full/vectors/000011-V-0013.bin"
private noncomputable def vp000011_14 : Blocks := edgeBlocks% "full/vectors/000011-V-0014.bin"
private noncomputable def vp000011_15 : Blocks := edgeBlocks% "full/vectors/000011-V-0015.bin"
private noncomputable def vp000011_16 : Blocks := edgeBlocks% "full/vectors/000011-V-0016.bin"
private noncomputable def vp000011_17 : Blocks := edgeBlocks% "full/vectors/000011-V-0017.bin"
private noncomputable def vp000011_18 : Blocks := edgeBlocks% "full/vectors/000011-V-0018.bin"
private noncomputable def vp000011_19 : Blocks := edgeBlocks% "full/vectors/000011-V-0019.bin"
private noncomputable def vp000011_20 : Blocks := edgeBlocks% "full/vectors/000011-V-0020.bin"
private noncomputable def vp000011_21 : Blocks := edgeBlocks% "full/vectors/000011-V-0021.bin"
private noncomputable def vp000011_22 : Blocks := edgeBlocks% "full/vectors/000011-V-0022.bin"
private noncomputable def vp000011_23 : Blocks := edgeBlocks% "full/vectors/000011-V-0023.bin"
private noncomputable def vp000011_24 : Blocks := edgeBlocks% "full/vectors/000011-V-0024.bin"
private noncomputable def vp000011_25 : Blocks := edgeBlocks% "full/vectors/000011-V-0025.bin"
private noncomputable def vp000011_26 : Blocks := edgeBlocks% "full/vectors/000011-V-0026.bin"
private noncomputable def vp000011_27 : Blocks := edgeBlocks% "full/vectors/000011-V-0027.bin"
private noncomputable def vp000011_28 : Blocks := edgeBlocks% "full/vectors/000011-V-0028.bin"
private noncomputable def vp000011_29 : Blocks := edgeBlocks% "full/vectors/000011-V-0029.bin"
private noncomputable def vp000011_30 : Blocks := edgeBlocks% "full/vectors/000011-V-0030.bin"
private noncomputable def vp000011_31 : Blocks := edgeBlocks% "full/vectors/000011-V-0031.bin"
private noncomputable def vp000011_32 : Blocks := edgeBlocks% "full/vectors/000011-V-0032.bin"
private noncomputable def vp000011_33 : Blocks := edgeBlocks% "full/vectors/000011-V-0033.bin"
private noncomputable def vp000011_34 : Blocks := edgeBlocks% "full/vectors/000011-V-0034.bin"
private noncomputable def vp000011_35 : Blocks := edgeBlocks% "full/vectors/000011-V-0035.bin"
private noncomputable def vp000011_36 : Blocks := edgeBlocks% "full/vectors/000011-V-0036.bin"
private noncomputable def vp000011_37 : Blocks := edgeBlocks% "full/vectors/000011-V-0037.bin"
private noncomputable def vp000011_38 : Blocks := edgeBlocks% "full/vectors/000011-V-0038.bin"
private noncomputable def vp000011_39 : Blocks := edgeBlocks% "full/vectors/000011-V-0039.bin"
private noncomputable def vp000011_40 : Blocks := edgeBlocks% "full/vectors/000011-V-0040.bin"
private noncomputable def vp000011_41 : Blocks := edgeBlocks% "full/vectors/000011-V-0041.bin"
private noncomputable def vp000011_42 : Blocks := edgeBlocks% "full/vectors/000011-V-0042.bin"
private noncomputable def vp000011_43 : Blocks := edgeBlocks% "full/vectors/000011-V-0043.bin"
private noncomputable def vp000011_44 : Blocks := edgeBlocks% "full/vectors/000011-V-0044.bin"
private noncomputable def vp000011_45 : Blocks := edgeBlocks% "full/vectors/000011-V-0045.bin"
noncomputable def vp000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000011_0 vp000011_1) (Blocks.join vp000011_2 (Blocks.join vp000011_3 vp000011_4))) (Blocks.join (Blocks.join vp000011_5 (Blocks.join vp000011_6 vp000011_7)) (Blocks.join vp000011_8 (Blocks.join vp000011_9 vp000011_10)))) (Blocks.join (Blocks.join (Blocks.join vp000011_11 (Blocks.join vp000011_12 vp000011_13)) (Blocks.join vp000011_14 (Blocks.join vp000011_15 vp000011_16))) (Blocks.join (Blocks.join vp000011_17 (Blocks.join vp000011_18 vp000011_19)) (Blocks.join vp000011_20 (Blocks.join vp000011_21 vp000011_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000011_23 vp000011_24) (Blocks.join vp000011_25 (Blocks.join vp000011_26 vp000011_27))) (Blocks.join (Blocks.join vp000011_28 (Blocks.join vp000011_29 vp000011_30)) (Blocks.join vp000011_31 (Blocks.join vp000011_32 vp000011_33)))) (Blocks.join (Blocks.join (Blocks.join vp000011_34 (Blocks.join vp000011_35 vp000011_36)) (Blocks.join vp000011_37 (Blocks.join vp000011_38 vp000011_39))) (Blocks.join (Blocks.join vp000011_40 (Blocks.join vp000011_41 vp000011_42)) (Blocks.join vp000011_43 (Blocks.join vp000011_44 vp000011_45))))))
private theorem bp0000110 : Branch 0 (-383761639/128000000 : ℚ) vp000011 := by
  apply branch_left_normalized (c:=vp0000110) (k:=0) (m:=3079) (by decide +kernel)
  rw [show 2*(-383761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/64000000 : ℚ) by norm_num]
  exact coverp0000110
private noncomputable def ep0000111_0 : Blocks := edgeBlocks% "full/vectors/0000111-E-0000.bin"
private noncomputable def ep0000111_1 : Blocks := edgeBlocks% "full/vectors/0000111-E-0001.bin"
private noncomputable def ep0000111_2 : Blocks := edgeBlocks% "full/vectors/0000111-E-0002.bin"
private noncomputable def ep0000111_3 : Blocks := edgeBlocks% "full/vectors/0000111-E-0003.bin"
private noncomputable def ep0000111_4 : Blocks := edgeBlocks% "full/vectors/0000111-E-0004.bin"
private noncomputable def ep0000111_5 : Blocks := edgeBlocks% "full/vectors/0000111-E-0005.bin"
private noncomputable def ep0000111_6 : Blocks := edgeBlocks% "full/vectors/0000111-E-0006.bin"
private noncomputable def ep0000111_7 : Blocks := edgeBlocks% "full/vectors/0000111-E-0007.bin"
private noncomputable def ep0000111_8 : Blocks := edgeBlocks% "full/vectors/0000111-E-0008.bin"
private noncomputable def ep0000111_9 : Blocks := edgeBlocks% "full/vectors/0000111-E-0009.bin"
private noncomputable def ep0000111_10 : Blocks := edgeBlocks% "full/vectors/0000111-E-0010.bin"
private noncomputable def ep0000111_11 : Blocks := edgeBlocks% "full/vectors/0000111-E-0011.bin"
private noncomputable def ep0000111_12 : Blocks := edgeBlocks% "full/vectors/0000111-E-0012.bin"
private noncomputable def ep0000111_13 : Blocks := edgeBlocks% "full/vectors/0000111-E-0013.bin"
private noncomputable def ep0000111_14 : Blocks := edgeBlocks% "full/vectors/0000111-E-0014.bin"
private noncomputable def ep0000111_15 : Blocks := edgeBlocks% "full/vectors/0000111-E-0015.bin"
private noncomputable def ep0000111_16 : Blocks := edgeBlocks% "full/vectors/0000111-E-0016.bin"
private noncomputable def ep0000111_17 : Blocks := edgeBlocks% "full/vectors/0000111-E-0017.bin"
private noncomputable def ep0000111_18 : Blocks := edgeBlocks% "full/vectors/0000111-E-0018.bin"
private noncomputable def ep0000111_19 : Blocks := edgeBlocks% "full/vectors/0000111-E-0019.bin"
private noncomputable def ep0000111_20 : Blocks := edgeBlocks% "full/vectors/0000111-E-0020.bin"
private noncomputable def ep0000111_21 : Blocks := edgeBlocks% "full/vectors/0000111-E-0021.bin"
private noncomputable def ep0000111_22 : Blocks := edgeBlocks% "full/vectors/0000111-E-0022.bin"
private noncomputable def ep0000111_23 : Blocks := edgeBlocks% "full/vectors/0000111-E-0023.bin"
private noncomputable def ep0000111_24 : Blocks := edgeBlocks% "full/vectors/0000111-E-0024.bin"
private noncomputable def ep0000111_25 : Blocks := edgeBlocks% "full/vectors/0000111-E-0025.bin"
private noncomputable def ep0000111_26 : Blocks := edgeBlocks% "full/vectors/0000111-E-0026.bin"
private noncomputable def ep0000111_27 : Blocks := edgeBlocks% "full/vectors/0000111-E-0027.bin"
private noncomputable def ep0000111_28 : Blocks := edgeBlocks% "full/vectors/0000111-E-0028.bin"
private noncomputable def ep0000111_29 : Blocks := edgeBlocks% "full/vectors/0000111-E-0029.bin"
private noncomputable def ep0000111_30 : Blocks := edgeBlocks% "full/vectors/0000111-E-0030.bin"
private noncomputable def ep0000111_31 : Blocks := edgeBlocks% "full/vectors/0000111-E-0031.bin"
private noncomputable def ep0000111_32 : Blocks := edgeBlocks% "full/vectors/0000111-E-0032.bin"
private noncomputable def ep0000111_33 : Blocks := edgeBlocks% "full/vectors/0000111-E-0033.bin"
private noncomputable def ep0000111_34 : Blocks := edgeBlocks% "full/vectors/0000111-E-0034.bin"
private noncomputable def ep0000111_35 : Blocks := edgeBlocks% "full/vectors/0000111-E-0035.bin"
private noncomputable def ep0000111_36 : Blocks := edgeBlocks% "full/vectors/0000111-E-0036.bin"
private noncomputable def ep0000111_37 : Blocks := edgeBlocks% "full/vectors/0000111-E-0037.bin"
private noncomputable def ep0000111_38 : Blocks := edgeBlocks% "full/vectors/0000111-E-0038.bin"
private noncomputable def ep0000111_39 : Blocks := edgeBlocks% "full/vectors/0000111-E-0039.bin"
private noncomputable def ep0000111_40 : Blocks := edgeBlocks% "full/vectors/0000111-E-0040.bin"
private noncomputable def ep0000111_41 : Blocks := edgeBlocks% "full/vectors/0000111-E-0041.bin"
private noncomputable def ep0000111_42 : Blocks := edgeBlocks% "full/vectors/0000111-E-0042.bin"
private noncomputable def ep0000111_43 : Blocks := edgeBlocks% "full/vectors/0000111-E-0043.bin"
private noncomputable def ep0000111_44 : Blocks := edgeBlocks% "full/vectors/0000111-E-0044.bin"
private noncomputable def ep0000111_45 : Blocks := edgeBlocks% "full/vectors/0000111-E-0045.bin"
noncomputable def ep0000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000111_0 ep0000111_1) (Blocks.join ep0000111_2 (Blocks.join ep0000111_3 ep0000111_4))) (Blocks.join (Blocks.join ep0000111_5 (Blocks.join ep0000111_6 ep0000111_7)) (Blocks.join ep0000111_8 (Blocks.join ep0000111_9 ep0000111_10)))) (Blocks.join (Blocks.join (Blocks.join ep0000111_11 (Blocks.join ep0000111_12 ep0000111_13)) (Blocks.join ep0000111_14 (Blocks.join ep0000111_15 ep0000111_16))) (Blocks.join (Blocks.join ep0000111_17 (Blocks.join ep0000111_18 ep0000111_19)) (Blocks.join ep0000111_20 (Blocks.join ep0000111_21 ep0000111_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000111_23 ep0000111_24) (Blocks.join ep0000111_25 (Blocks.join ep0000111_26 ep0000111_27))) (Blocks.join (Blocks.join ep0000111_28 (Blocks.join ep0000111_29 ep0000111_30)) (Blocks.join ep0000111_31 (Blocks.join ep0000111_32 ep0000111_33)))) (Blocks.join (Blocks.join (Blocks.join ep0000111_34 (Blocks.join ep0000111_35 ep0000111_36)) (Blocks.join ep0000111_37 (Blocks.join ep0000111_38 ep0000111_39))) (Blocks.join (Blocks.join ep0000111_40 (Blocks.join ep0000111_41 ep0000111_42)) (Blocks.join ep0000111_43 (Blocks.join ep0000111_44 ep0000111_45))))))
private def ptsp0000111 : List ℤ := [((2:ℤ)^2058+0),((2:ℤ)^2058+1),((2:ℤ)^2058+2),((2:ℤ)^2058+3),((2:ℤ)^2058+4)]
private theorem boundp0000111 : 2^vp000011.size*absSum vp000011.list + ((2:ℤ)^6199*absSum vp0000111.list+absSum ep0000111.list) < (2:ℤ)^9223 := by decide +kernel
private theorem pointp0000111_0 : fastHom 1 ((2:ℤ)^2058+0) vp000011 = ((2:ℤ)^6199)*vp0000111.subst ((2:ℤ)^2058+0)+ep0000111.subst ((2:ℤ)^2058+0) := by decide +kernel
private theorem pointp0000111_1 : fastHom 1 ((2:ℤ)^2058+1) vp000011 = ((2:ℤ)^6199)*vp0000111.subst ((2:ℤ)^2058+1)+ep0000111.subst ((2:ℤ)^2058+1) := by decide +kernel
private theorem pointp0000111_2 : fastHom 1 ((2:ℤ)^2058+2) vp000011 = ((2:ℤ)^6199)*vp0000111.subst ((2:ℤ)^2058+2)+ep0000111.subst ((2:ℤ)^2058+2) := by decide +kernel
private theorem pointp0000111_3 : fastHom 1 ((2:ℤ)^2058+3) vp000011 = ((2:ℤ)^6199)*vp0000111.subst ((2:ℤ)^2058+3)+ep0000111.subst ((2:ℤ)^2058+3) := by decide +kernel
private theorem pointp0000111_4 : fastHom 1 ((2:ℤ)^2058+4) vp000011 = ((2:ℤ)^6199)*vp0000111.subst ((2:ℤ)^2058+4)+ep0000111.subst ((2:ℤ)^2058+4) := by decide +kernel
private theorem checkp0000111 (x:ℤ) (hx:x ∈ ptsp0000111) : fastHom 1 x vp000011 = ((2:ℤ)^6199)*vp0000111.subst x+ep0000111.subst x := by
  simp only [ptsp0000111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp0000111_0
  · exact pointp0000111_1
  · exact pointp0000111_2
  · exact pointp0000111_3
  · exact pointp0000111_4
private theorem idp0000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011.list =
    C ((2:ℤ)^6199) * horner X vp0000111.list + horner X ep0000111.list := by
  apply edge_identity (B := (2:ℤ)^9223) (by decide) (by positivity) (by positivity) boundp0000111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000111 (by decide +kernel)
  · have h : ptsp0000111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000111.trans_le (by decide +kernel)
  · exact checkp0000111
private theorem bp0000111 : Branch 1 (-383761639/128000000 : ℚ) vp000011 := by
  apply branch_checked idp0000111 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-447761639/64000000 : ℚ) by norm_num]
  exact coverp0000111
theorem coverp000011 : Covers (-383761639/128000000 : ℚ) vp000011 := join_branches bp0000110 bp0000111
end NextProof.EdgeFull

