import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData07

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p28 : Piece := ⟨256, tailInts% "28-g.bin", q28,
  tailInt% "28-s.bin", tailInt% "28-v.bin", tailInt% "28-u.bin", tailInt% "28-w.bin", tailInt% "28-den.bin", tailInt% "28-end.bin"⟩

private theorem local28 : Light.Local p28 7168 (Light.input 8192 3584 seed28 weights28) := by
  constructor <;> decide +kernel

theorem c28 : Light.Checked p28 7168 :=
  Light.of_local (Light.window_chunk (tail := rest29) seed_ok28 drop28 (by decide +kernel)) local28

noncomputable def p29 : Piece := ⟨256, tailInts% "29-g.bin", q29,
  tailInt% "29-s.bin", tailInt% "29-v.bin", tailInt% "29-u.bin", tailInt% "29-w.bin", tailInt% "29-den.bin", tailInt% "29-end.bin"⟩

private theorem local29 : Light.Local p29 7424 (Light.input 8192 3712 seed29 weights29) := by
  constructor <;> decide +kernel

theorem c29 : Light.Checked p29 7424 :=
  Light.of_local (Light.window_chunk (tail := rest30) seed_ok29 drop29 (by decide +kernel)) local29

noncomputable def p30 : Piece := ⟨256, tailInts% "30-g.bin", q30,
  tailInt% "30-s.bin", tailInt% "30-v.bin", tailInt% "30-u.bin", tailInt% "30-w.bin", tailInt% "30-den.bin", tailInt% "30-end.bin"⟩

private theorem local30 : Light.Local p30 7680 (Light.input 8192 3840 seed30 weights30) := by
  constructor <;> decide +kernel

theorem c30 : Light.Checked p30 7680 :=
  Light.of_local (Light.window_chunk (tail := rest31) seed_ok30 drop30 (by decide +kernel)) local30

noncomputable def p31 : Piece := ⟨256, tailInts% "31-g.bin", q31,
  tailInt% "31-s.bin", tailInt% "31-v.bin", tailInt% "31-u.bin", tailInt% "31-w.bin", tailInt% "31-den.bin", tailInt% "31-end.bin"⟩

private theorem local31 : Light.Local p31 7936 (Light.input 8192 3968 seed31 weights31) := by
  constructor <;> decide +kernel

theorem c31 : Light.Checked p31 7936 :=
  Light.of_local (Light.window_chunk (tail := rest32) seed_ok31 drop31 (by decide +kernel)) local31

end NextProof.Tail.Shards
