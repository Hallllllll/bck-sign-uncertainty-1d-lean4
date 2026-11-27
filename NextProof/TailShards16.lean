import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData16

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p64 : Piece := ⟨2, tailInts% "64-g.bin", q64,
  tailInt% "64-s.bin", tailInt% "64-v.bin", tailInt% "64-u.bin", tailInt% "64-w.bin", tailInt% "64-den.bin", tailInt% "64-end.bin"⟩

private theorem local64 : Light.Local p64 16384 (Light.input 8192 8192 seed64 weights64) := by
  constructor <;> decide +kernel

theorem c64 : Light.Checked p64 16384 :=
  Light.of_local (Light.window_chunk (tail := rest65) seed_ok64 drop64 (by decide +kernel)) local64

end NextProof.Tail.Shards
