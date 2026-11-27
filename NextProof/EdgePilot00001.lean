import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgePilot
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private def vp0000000100000011_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000011-V-0000.bin"
def vp0000000100000011 : Blocks := vp0000000100000011_0
theorem coverp0000000100000011 : Covers (-32136639/125000 : ℚ) vp0000000100000011 := cover_leaf (by decide +kernel)
private def vp0000000100000010_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000010-V-0000.bin"
def vp0000000100000010 : Blocks := vp0000000100000010_0
theorem coverp0000000100000010 : Covers (-32011639/125000 : ℚ) vp0000000100000010 := cover_leaf (by decide +kernel)
private def vp000000010000001_0 : Blocks := edgeBlocks% "pilot/vectors/000000010000001-V-0000.bin"
def vp000000010000001 : Blocks := vp000000010000001_0
private theorem bp0000000100000010 : Branch 0 (-32011639/250000 : ℚ) vp000000010000001 := by
  apply branch_left_normalized (c:=vp0000000100000010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-32011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-32011639/125000 : ℚ) by norm_num]
  exact coverp0000000100000010
private def ep0000000100000011_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000011-E-0000.bin"
def ep0000000100000011 : Blocks := ep0000000100000011_0
private def ptsp0000000100000011 : List ℤ := [((2:ℤ)^64+0),((2:ℤ)^64+1),((2:ℤ)^64+2),((2:ℤ)^64+3)]
private theorem boundp0000000100000011 : 2^vp000000010000001.size*absSum vp000000010000001.list + ((2:ℤ)^69*absSum vp0000000100000011.list+absSum ep0000000100000011.list) < (2:ℤ)^193 := by decide +kernel
private theorem pointp0000000100000011_0 : fastHom 1 ((2:ℤ)^64+0) vp000000010000001 = ((2:ℤ)^69)*vp0000000100000011.subst ((2:ℤ)^64+0)+ep0000000100000011.subst ((2:ℤ)^64+0) := by decide +kernel
private theorem pointp0000000100000011_1 : fastHom 1 ((2:ℤ)^64+1) vp000000010000001 = ((2:ℤ)^69)*vp0000000100000011.subst ((2:ℤ)^64+1)+ep0000000100000011.subst ((2:ℤ)^64+1) := by decide +kernel
private theorem pointp0000000100000011_2 : fastHom 1 ((2:ℤ)^64+2) vp000000010000001 = ((2:ℤ)^69)*vp0000000100000011.subst ((2:ℤ)^64+2)+ep0000000100000011.subst ((2:ℤ)^64+2) := by decide +kernel
private theorem pointp0000000100000011_3 : fastHom 1 ((2:ℤ)^64+3) vp000000010000001 = ((2:ℤ)^69)*vp0000000100000011.subst ((2:ℤ)^64+3)+ep0000000100000011.subst ((2:ℤ)^64+3) := by decide +kernel
private theorem checkp0000000100000011 (x:ℤ) (hx:x ∈ ptsp0000000100000011) : fastHom 1 x vp000000010000001 = ((2:ℤ)^69)*vp0000000100000011.subst x+ep0000000100000011.subst x := by
  simp only [ptsp0000000100000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp0000000100000011_0
  · exact pointp0000000100000011_1
  · exact pointp0000000100000011_2
  · exact pointp0000000100000011_3
private theorem idp0000000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000001.list =
    C ((2:ℤ)^69) * horner X vp0000000100000011.list + horner X ep0000000100000011.list := by
  apply edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity) boundp0000000100000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000000100000011 (by decide +kernel)
  · have h : ptsp0000000100000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000000100000011.trans_le (by decide +kernel)
  · exact checkp0000000100000011
private theorem bp0000000100000011 : Branch 1 (-32011639/250000 : ℚ) vp000000010000001 := by
  apply branch_checked idp0000000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-32011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-32136639/125000 : ℚ) by norm_num]
  exact coverp0000000100000011
theorem coverp000000010000001 : Covers (-32011639/250000 : ℚ) vp000000010000001 := join_branches bp0000000100000010 bp0000000100000011
private def vp00000001000000011_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000011-V-0000.bin"
def vp00000001000000011 : Blocks := vp00000001000000011_0
theorem coverp00000001000000011 : Covers (-31949139/62500 : ℚ) vp00000001000000011 := cover_leaf (by decide +kernel)
private def vp00000001000000010_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000010-V-0000.bin"
def vp00000001000000010 : Blocks := vp00000001000000010_0
theorem coverp00000001000000010 : Covers (-31886639/62500 : ℚ) vp00000001000000010 := cover_leaf (by decide +kernel)
private def vp0000000100000001_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000001-V-0000.bin"
def vp0000000100000001 : Blocks := vp0000000100000001_0
private theorem bp00000001000000010 : Branch 0 (-31886639/125000 : ℚ) vp0000000100000001 := by
  apply branch_left_normalized (c:=vp00000001000000010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-31886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31886639/62500 : ℚ) by norm_num]
  exact coverp00000001000000010
private def ep00000001000000011_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000011-E-0000.bin"
def ep00000001000000011 : Blocks := ep00000001000000011_0
private def ptsp00000001000000011 : List ℤ := [((2:ℤ)^73+0),((2:ℤ)^73+1),((2:ℤ)^73+2)]
private theorem boundp00000001000000011 : 2^vp0000000100000001.size*absSum vp0000000100000001.list + ((2:ℤ)^41*absSum vp00000001000000011.list+absSum ep00000001000000011.list) < (2:ℤ)^155 := by decide +kernel
private theorem pointp00000001000000011_0 : fastHom 1 ((2:ℤ)^73+0) vp0000000100000001 = ((2:ℤ)^41)*vp00000001000000011.subst ((2:ℤ)^73+0)+ep00000001000000011.subst ((2:ℤ)^73+0) := by decide +kernel
private theorem pointp00000001000000011_1 : fastHom 1 ((2:ℤ)^73+1) vp0000000100000001 = ((2:ℤ)^41)*vp00000001000000011.subst ((2:ℤ)^73+1)+ep00000001000000011.subst ((2:ℤ)^73+1) := by decide +kernel
private theorem pointp00000001000000011_2 : fastHom 1 ((2:ℤ)^73+2) vp0000000100000001 = ((2:ℤ)^41)*vp00000001000000011.subst ((2:ℤ)^73+2)+ep00000001000000011.subst ((2:ℤ)^73+2) := by decide +kernel
private theorem checkp00000001000000011 (x:ℤ) (hx:x ∈ ptsp00000001000000011) : fastHom 1 x vp0000000100000001 = ((2:ℤ)^41)*vp00000001000000011.subst x+ep00000001000000011.subst x := by
  simp only [ptsp00000001000000011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp00000001000000011_0
  · exact pointp00000001000000011_1
  · exact pointp00000001000000011_2
private theorem idp00000001000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000001.list =
    C ((2:ℤ)^41) * horner X vp00000001000000011.list + horner X ep00000001000000011.list := by
  apply edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity) boundp00000001000000011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00000001000000011 (by decide +kernel)
  · have h : ptsp00000001000000011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00000001000000011.trans_le (by decide +kernel)
  · exact checkp00000001000000011
private theorem bp00000001000000011 : Branch 1 (-31886639/125000 : ℚ) vp0000000100000001 := by
  apply branch_checked idp00000001000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-31886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31949139/62500 : ℚ) by norm_num]
  exact coverp00000001000000011
theorem coverp0000000100000001 : Covers (-31886639/125000 : ℚ) vp0000000100000001 := join_branches bp00000001000000010 bp00000001000000011
private def vp00000001000000001_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000001-V-0000.bin"
def vp00000001000000001 : Blocks := vp00000001000000001_0
theorem coverp00000001000000001 : Covers (-31824139/62500 : ℚ) vp00000001000000001 := cover_leaf (by decide +kernel)
private def vp00000001000000000_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000000-V-0000.bin"
def vp00000001000000000 : Blocks := vp00000001000000000_0
theorem coverp00000001000000000 : Covers (-31761639/62500 : ℚ) vp00000001000000000 := cover_leaf (by decide +kernel)
private def vp0000000100000000_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000000-V-0000.bin"
def vp0000000100000000 : Blocks := vp0000000100000000_0
private theorem bp00000001000000000 : Branch 0 (-31761639/125000 : ℚ) vp0000000100000000 := by
  apply branch_left_normalized (c:=vp00000001000000000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-31761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/62500 : ℚ) by norm_num]
  exact coverp00000001000000000
private def ep00000001000000001_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000001-E-0000.bin"
def ep00000001000000001 : Blocks := ep00000001000000001_0
private def ptsp00000001000000001 : List ℤ := [((2:ℤ)^73+0),((2:ℤ)^73+1),((2:ℤ)^73+2)]
private theorem boundp00000001000000001 : 2^vp0000000100000000.size*absSum vp0000000100000000.list + ((2:ℤ)^42*absSum vp00000001000000001.list+absSum ep00000001000000001.list) < (2:ℤ)^156 := by decide +kernel
private theorem pointp00000001000000001_0 : fastHom 1 ((2:ℤ)^73+0) vp0000000100000000 = ((2:ℤ)^42)*vp00000001000000001.subst ((2:ℤ)^73+0)+ep00000001000000001.subst ((2:ℤ)^73+0) := by decide +kernel
private theorem pointp00000001000000001_1 : fastHom 1 ((2:ℤ)^73+1) vp0000000100000000 = ((2:ℤ)^42)*vp00000001000000001.subst ((2:ℤ)^73+1)+ep00000001000000001.subst ((2:ℤ)^73+1) := by decide +kernel
private theorem pointp00000001000000001_2 : fastHom 1 ((2:ℤ)^73+2) vp0000000100000000 = ((2:ℤ)^42)*vp00000001000000001.subst ((2:ℤ)^73+2)+ep00000001000000001.subst ((2:ℤ)^73+2) := by decide +kernel
private theorem checkp00000001000000001 (x:ℤ) (hx:x ∈ ptsp00000001000000001) : fastHom 1 x vp0000000100000000 = ((2:ℤ)^42)*vp00000001000000001.subst x+ep00000001000000001.subst x := by
  simp only [ptsp00000001000000001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp00000001000000001_0
  · exact pointp00000001000000001_1
  · exact pointp00000001000000001_2
private theorem idp00000001000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000000.list =
    C ((2:ℤ)^42) * horner X vp00000001000000001.list + horner X ep00000001000000001.list := by
  apply edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity) boundp00000001000000001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00000001000000001 (by decide +kernel)
  · have h : ptsp00000001000000001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00000001000000001.trans_le (by decide +kernel)
  · exact checkp00000001000000001
private theorem bp00000001000000001 : Branch 1 (-31761639/125000 : ℚ) vp0000000100000000 := by
  apply branch_checked idp00000001000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31824139/62500 : ℚ) by norm_num]
  exact coverp00000001000000001
theorem coverp0000000100000000 : Covers (-31761639/125000 : ℚ) vp0000000100000000 := join_branches bp00000001000000000 bp00000001000000001
private def vp000000010000000_0 : Blocks := edgeBlocks% "pilot/vectors/000000010000000-V-0000.bin"
def vp000000010000000 : Blocks := vp000000010000000_0
private theorem bp0000000100000000 : Branch 0 (-31761639/250000 : ℚ) vp000000010000000 := by
  apply branch_left_normalized (c:=vp0000000100000000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-31761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/125000 : ℚ) by norm_num]
  exact coverp0000000100000000
private def ep0000000100000001_0 : Blocks := edgeBlocks% "pilot/vectors/0000000100000001-E-0000.bin"
def ep0000000100000001 : Blocks := ep0000000100000001_0
private def ptsp0000000100000001 : List ℤ := [((2:ℤ)^64+0),((2:ℤ)^64+1),((2:ℤ)^64+2)]
private theorem boundp0000000100000001 : 2^vp000000010000000.size*absSum vp000000010000000.list + ((2:ℤ)^66*absSum vp0000000100000001.list+absSum ep0000000100000001.list) < (2:ℤ)^191 := by decide +kernel
private theorem pointp0000000100000001_0 : fastHom 1 ((2:ℤ)^64+0) vp000000010000000 = ((2:ℤ)^66)*vp0000000100000001.subst ((2:ℤ)^64+0)+ep0000000100000001.subst ((2:ℤ)^64+0) := by decide +kernel
private theorem pointp0000000100000001_1 : fastHom 1 ((2:ℤ)^64+1) vp000000010000000 = ((2:ℤ)^66)*vp0000000100000001.subst ((2:ℤ)^64+1)+ep0000000100000001.subst ((2:ℤ)^64+1) := by decide +kernel
private theorem pointp0000000100000001_2 : fastHom 1 ((2:ℤ)^64+2) vp000000010000000 = ((2:ℤ)^66)*vp0000000100000001.subst ((2:ℤ)^64+2)+ep0000000100000001.subst ((2:ℤ)^64+2) := by decide +kernel
private theorem checkp0000000100000001 (x:ℤ) (hx:x ∈ ptsp0000000100000001) : fastHom 1 x vp000000010000000 = ((2:ℤ)^66)*vp0000000100000001.subst x+ep0000000100000001.subst x := by
  simp only [ptsp0000000100000001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp0000000100000001_0
  · exact pointp0000000100000001_1
  · exact pointp0000000100000001_2
private theorem idp0000000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000000.list =
    C ((2:ℤ)^66) * horner X vp0000000100000001.list + horner X ep0000000100000001.list := by
  apply edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity) boundp0000000100000001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0000000100000001 (by decide +kernel)
  · have h : ptsp0000000100000001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0000000100000001.trans_le (by decide +kernel)
  · exact checkp0000000100000001
private theorem bp0000000100000001 : Branch 1 (-31761639/250000 : ℚ) vp000000010000000 := by
  apply branch_checked idp0000000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-31886639/125000 : ℚ) by norm_num]
  exact coverp0000000100000001
theorem coverp000000010000000 : Covers (-31761639/250000 : ℚ) vp000000010000000 := join_branches bp0000000100000000 bp0000000100000001
private def vp00000001000000_0 : Blocks := edgeBlocks% "pilot/vectors/00000001000000-V-0000.bin"
def vp00000001000000 : Blocks := vp00000001000000_0
private theorem bp000000010000000 : Branch 0 (-31761639/500000 : ℚ) vp00000001000000 := by
  apply branch_left_normalized (c:=vp000000010000000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-31761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/250000 : ℚ) by norm_num]
  exact coverp000000010000000
private def ep000000010000001_0 : Blocks := edgeBlocks% "pilot/vectors/000000010000001-E-0000.bin"
def ep000000010000001 : Blocks := ep000000010000001_0
private def ptsp000000010000001 : List ℤ := [((2:ℤ)^64+0),((2:ℤ)^64+1),((2:ℤ)^64+2),((2:ℤ)^64+3),((2:ℤ)^64+4)]
private theorem boundp000000010000001 : 2^vp00000001000000.size*absSum vp00000001000000.list + ((2:ℤ)^110*absSum vp000000010000001.list+absSum ep000000010000001.list) < (2:ℤ)^259 := by decide +kernel
private theorem pointp000000010000001_0 : fastHom 1 ((2:ℤ)^64+0) vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst ((2:ℤ)^64+0)+ep000000010000001.subst ((2:ℤ)^64+0) := by decide +kernel
private theorem pointp000000010000001_1 : fastHom 1 ((2:ℤ)^64+1) vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst ((2:ℤ)^64+1)+ep000000010000001.subst ((2:ℤ)^64+1) := by decide +kernel
private theorem pointp000000010000001_2 : fastHom 1 ((2:ℤ)^64+2) vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst ((2:ℤ)^64+2)+ep000000010000001.subst ((2:ℤ)^64+2) := by decide +kernel
private theorem pointp000000010000001_3 : fastHom 1 ((2:ℤ)^64+3) vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst ((2:ℤ)^64+3)+ep000000010000001.subst ((2:ℤ)^64+3) := by decide +kernel
private theorem pointp000000010000001_4 : fastHom 1 ((2:ℤ)^64+4) vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst ((2:ℤ)^64+4)+ep000000010000001.subst ((2:ℤ)^64+4) := by decide +kernel
private theorem checkp000000010000001 (x:ℤ) (hx:x ∈ ptsp000000010000001) : fastHom 1 x vp00000001000000 = ((2:ℤ)^110)*vp000000010000001.subst x+ep000000010000001.subst x := by
  simp only [ptsp000000010000001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp000000010000001_0
  · exact pointp000000010000001_1
  · exact pointp000000010000001_2
  · exact pointp000000010000001_3
  · exact pointp000000010000001_4
private theorem idp000000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000000.list =
    C ((2:ℤ)^110) * horner X vp000000010000001.list + horner X ep000000010000001.list := by
  apply edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity) boundp000000010000001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp000000010000001 (by decide +kernel)
  · have h : ptsp000000010000001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp000000010000001.trans_le (by decide +kernel)
  · exact checkp000000010000001
private theorem bp000000010000001 : Branch 1 (-31761639/500000 : ℚ) vp00000001000000 := by
  apply branch_checked idp000000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-32011639/250000 : ℚ) by norm_num]
  exact coverp000000010000001
theorem coverp00000001000000 : Covers (-31761639/500000 : ℚ) vp00000001000000 := join_branches bp000000010000000 bp000000010000001
end NextProof.EdgePilot

#print axioms NextProof.EdgePilot.coverp00000001000000
