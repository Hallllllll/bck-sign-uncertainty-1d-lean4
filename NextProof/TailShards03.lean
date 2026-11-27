import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData03

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p12 : Piece := ⟨256, tailInts% "12-g.bin", q12,
  tailInt% "12-s.bin", tailInt% "12-v.bin", tailInt% "12-u.bin", tailInt% "12-w.bin", tailInt% "12-den.bin", tailInt% "12-end.bin"⟩

private theorem local12 : Light.Local p12 3072 (Light.input 8192 1536 seed12 weights12) := by
  constructor <;> decide +kernel

theorem c12 : Light.Checked p12 3072 :=
  Light.of_local (Light.window_chunk (tail := rest13) seed_ok12 drop12 (by decide +kernel)) local12

noncomputable def p13 : Piece := ⟨256, tailInts% "13-g.bin", q13,
  tailInt% "13-s.bin", tailInt% "13-v.bin", tailInt% "13-u.bin", tailInt% "13-w.bin", tailInt% "13-den.bin", tailInt% "13-end.bin"⟩

private theorem local13 : Light.Local p13 3328 (Light.input 8192 1664 seed13 weights13) := by
  constructor <;> decide +kernel

theorem c13 : Light.Checked p13 3328 :=
  Light.of_local (Light.window_chunk (tail := rest14) seed_ok13 drop13 (by decide +kernel)) local13

noncomputable def p14 : Piece := ⟨256, tailInts% "14-g.bin", q14,
  tailInt% "14-s.bin", tailInt% "14-v.bin", tailInt% "14-u.bin", tailInt% "14-w.bin", tailInt% "14-den.bin", tailInt% "14-end.bin"⟩

private theorem local14 : Light.Local p14 3584 (Light.input 8192 1792 seed14 weights14) := by
  constructor <;> decide +kernel

theorem c14 : Light.Checked p14 3584 :=
  Light.of_local (Light.window_chunk (tail := rest15) seed_ok14 drop14 (by decide +kernel)) local14

noncomputable def p15 : Piece := ⟨256, tailInts% "15-g.bin", q15,
  tailInt% "15-s.bin", tailInt% "15-v.bin", tailInt% "15-u.bin", tailInt% "15-w.bin", tailInt% "15-den.bin", tailInt% "15-end.bin"⟩

private theorem local15 : Light.Local p15 3840 (Light.input 8192 1920 seed15 weights15) := by
  constructor <;> decide +kernel

theorem c15 : Light.Checked p15 3840 :=
  Light.of_local (Light.window_chunk (tail := rest16) seed_ok15 drop15 (by decide +kernel)) local15

end NextProof.Tail.Shards
