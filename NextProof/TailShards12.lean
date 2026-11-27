import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData12

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p48 : Piece := ⟨256, tailInts% "48-g.bin", q48,
  tailInt% "48-s.bin", tailInt% "48-v.bin", tailInt% "48-u.bin", tailInt% "48-w.bin", tailInt% "48-den.bin", tailInt% "48-end.bin"⟩

private theorem local48 : Light.Local p48 12288 (Light.input 8192 6144 seed48 weights48) := by
  constructor <;> decide +kernel

theorem c48 : Light.Checked p48 12288 :=
  Light.of_local (Light.window_chunk (tail := rest49) seed_ok48 drop48 (by decide +kernel)) local48

noncomputable def p49 : Piece := ⟨256, tailInts% "49-g.bin", q49,
  tailInt% "49-s.bin", tailInt% "49-v.bin", tailInt% "49-u.bin", tailInt% "49-w.bin", tailInt% "49-den.bin", tailInt% "49-end.bin"⟩

private theorem local49 : Light.Local p49 12544 (Light.input 8192 6272 seed49 weights49) := by
  constructor <;> decide +kernel

theorem c49 : Light.Checked p49 12544 :=
  Light.of_local (Light.window_chunk (tail := rest50) seed_ok49 drop49 (by decide +kernel)) local49

noncomputable def p50 : Piece := ⟨256, tailInts% "50-g.bin", q50,
  tailInt% "50-s.bin", tailInt% "50-v.bin", tailInt% "50-u.bin", tailInt% "50-w.bin", tailInt% "50-den.bin", tailInt% "50-end.bin"⟩

private theorem local50 : Light.Local p50 12800 (Light.input 8192 6400 seed50 weights50) := by
  constructor <;> decide +kernel

theorem c50 : Light.Checked p50 12800 :=
  Light.of_local (Light.window_chunk (tail := rest51) seed_ok50 drop50 (by decide +kernel)) local50

noncomputable def p51 : Piece := ⟨256, tailInts% "51-g.bin", q51,
  tailInt% "51-s.bin", tailInt% "51-v.bin", tailInt% "51-u.bin", tailInt% "51-w.bin", tailInt% "51-den.bin", tailInt% "51-end.bin"⟩

private theorem local51 : Light.Local p51 13056 (Light.input 8192 6528 seed51 weights51) := by
  constructor <;> decide +kernel

theorem c51 : Light.Checked p51 13056 :=
  Light.of_local (Light.window_chunk (tail := rest52) seed_ok51 drop51 (by decide +kernel)) local51

end NextProof.Tail.Shards
