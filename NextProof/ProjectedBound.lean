import NextProof.EdgeFull00147
import NextProof.TailShardRoot
import NextProof.WitnessResult

namespace NextProof
open Tail

/-- The two independently serialized integer coefficient tables agree exactly. -/
theorem projected_root_data : EdgeFull.vroot.list = Shards.literalPower := by
  set_option maxRecDepth 200000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem projected_rational_upper :
    AplusSquared ≤ (151745029530798611:ℝ)/500000000000000000 := by
  apply projected_upper_from_cover EdgeFull.vroot EdgeFull.coverroot
  intro z hz
  rw [projected_root_data]
  exact Shards.literalPower_le z hz

theorem projected_margin_published :
    (30349081:ℝ)/100000000 - AplusSquared ≥ 375469201389/500000000000000000 := by
  linarith [projected_rational_upper]

/-- Compare with the lower endpoint isolated for the public witness. -/
theorem projected_margin_baseline_endpoint :
    (10327251924471459878851645007538640968737106416668801:ℝ)/34028236692093846346337460743176821145600000000000000 - AplusSquared ≥
    12725641180479920815196532803884695479493068114673/21267647932558653966460912964485513216000000000000000000 := by
  linarith [projected_rational_upper]

end NextProof
#print axioms NextProof.projected_rational_upper
#print axioms NextProof.projected_margin_published
