import NextProof.OptEdge00085Batch01
import NextProof.OptEdge00085Batch02
namespace NextProof.EdgeRecovery.R0001
open NextProof.Compact NextProof.Tail Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 150000
private noncomputable def samples : List ℤ := [(2:ℤ)^8192, (2:ℤ)^8193, (2:ℤ)^8194, (2:ℤ)^8195, (2:ℤ)^8196, (2:ℤ)^8197]
private theorem checkedBound : 2^P.data.size*absSum P.data.list + ((2:ℤ)^19325*absSum C.data.list+absSum E.data.list) < (2:ℤ)^44665 := by decide +kernel
theorem identity :
    halfForm (X:ℤ[X]) (Polynomial.C (1:ℤ)) P.data.list = Polynomial.C ((2:ℤ)^19325)*horner X C.data.list + horner X E.data.list := by
  apply edge_identity (B := (2:ℤ)^44665) (by decide) (by positivity) (by positivity) checkedBound
  apply edge_scalar_of_shards (by decide) (by positivity) samples (by decide +kernel)
  · have h : samples.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact checkedBound.trans_le (by decide +kernel)
  · intro x hx
    simp only [samples,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact point8192
    · exact point8193
    · exact point8194
    · exact point8195
    · exact point8196
    · exact point8197
end NextProof.EdgeRecovery.R0001
#print axioms NextProof.EdgeRecovery.R0001.identity
