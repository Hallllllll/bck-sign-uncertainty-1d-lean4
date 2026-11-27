import NextProof.DualData
import NextProof.EdgeArithmeticIO
import NextProof.EdgeArithmeticTactic
import NextProof.EdgePilot00001
import NextProof.ProjectedBound
import NextProof.RecordBridge
import NextProof.Tail16
import NextProof.Tail60
namespace NextProof

/-- Fully concrete control applying the same continuum specification. -/
theorem control_degree60_product : AplusSquared ≤ (101/50:ℝ)/(2*Real.pi) := by
  apply upper_from_polynomial Tail60.witness (101/50) (by norm_num) Tail60.self_fourier _ Tail60.origin.le
    (fun x hx => (Tail60.tail x hx).le)
  intro h
  have he : (radialGaussian Tail60.witness 0).re < 0 := by
    simpa [radialGaussian_apply] using Tail60.origin
  rw [h] at he
  simpa using he

end NextProof
#print axioms NextProof.control_degree60_product
#print axioms NextProof.projected_rational_upper
