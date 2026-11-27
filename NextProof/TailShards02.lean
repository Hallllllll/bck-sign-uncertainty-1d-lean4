import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData02

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p08 : Piece := ⟨256, tailInts% "08-g.bin", q08,
  tailInt% "08-s.bin", tailInt% "08-v.bin", tailInt% "08-u.bin", tailInt% "08-w.bin", tailInt% "08-den.bin", tailInt% "08-end.bin"⟩

private theorem local08 : Light.Local p08 2048 (Light.input 8192 1024 seed08 weights08) := by
  constructor <;> decide +kernel

theorem c08 : Light.Checked p08 2048 :=
  Light.of_local (Light.window_chunk (tail := rest09) seed_ok08 drop08 (by decide +kernel)) local08

noncomputable def p09 : Piece := ⟨256, tailInts% "09-g.bin", q09,
  tailInt% "09-s.bin", tailInt% "09-v.bin", tailInt% "09-u.bin", tailInt% "09-w.bin", tailInt% "09-den.bin", tailInt% "09-end.bin"⟩

private theorem local09 : Light.Local p09 2304 (Light.input 8192 1152 seed09 weights09) := by
  constructor <;> decide +kernel

theorem c09 : Light.Checked p09 2304 :=
  Light.of_local (Light.window_chunk (tail := rest10) seed_ok09 drop09 (by decide +kernel)) local09

noncomputable def p10 : Piece := ⟨256, tailInts% "10-g.bin", q10,
  tailInt% "10-s.bin", tailInt% "10-v.bin", tailInt% "10-u.bin", tailInt% "10-w.bin", tailInt% "10-den.bin", tailInt% "10-end.bin"⟩

private theorem local10 : Light.Local p10 2560 (Light.input 8192 1280 seed10 weights10) := by
  constructor <;> decide +kernel

theorem c10 : Light.Checked p10 2560 :=
  Light.of_local (Light.window_chunk (tail := rest11) seed_ok10 drop10 (by decide +kernel)) local10

noncomputable def p11 : Piece := ⟨256, tailInts% "11-g.bin", q11,
  tailInt% "11-s.bin", tailInt% "11-v.bin", tailInt% "11-u.bin", tailInt% "11-w.bin", tailInt% "11-den.bin", tailInt% "11-end.bin"⟩

private theorem local11 : Light.Local p11 2816 (Light.input 8192 1408 seed11 weights11) := by
  constructor <;> decide +kernel

theorem c11 : Light.Checked p11 2816 :=
  Light.of_local (Light.window_chunk (tail := rest12) seed_ok11 drop11 (by decide +kernel)) local11

end NextProof.Tail.Shards
