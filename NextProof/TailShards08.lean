import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData08

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p32 : Piece := ⟨256, tailInts% "32-g.bin", q32,
  tailInt% "32-s.bin", tailInt% "32-v.bin", tailInt% "32-u.bin", tailInt% "32-w.bin", tailInt% "32-den.bin", tailInt% "32-end.bin"⟩

private theorem local32 : Light.Local p32 8192 (Light.input 8192 4096 seed32 weights32) := by
  constructor <;> decide +kernel

theorem c32 : Light.Checked p32 8192 :=
  Light.of_local (Light.window_chunk (tail := rest33) seed_ok32 drop32 (by decide +kernel)) local32

noncomputable def p33 : Piece := ⟨256, tailInts% "33-g.bin", q33,
  tailInt% "33-s.bin", tailInt% "33-v.bin", tailInt% "33-u.bin", tailInt% "33-w.bin", tailInt% "33-den.bin", tailInt% "33-end.bin"⟩

private theorem local33 : Light.Local p33 8448 (Light.input 8192 4224 seed33 weights33) := by
  constructor <;> decide +kernel

theorem c33 : Light.Checked p33 8448 :=
  Light.of_local (Light.window_chunk (tail := rest34) seed_ok33 drop33 (by decide +kernel)) local33

noncomputable def p34 : Piece := ⟨256, tailInts% "34-g.bin", q34,
  tailInt% "34-s.bin", tailInt% "34-v.bin", tailInt% "34-u.bin", tailInt% "34-w.bin", tailInt% "34-den.bin", tailInt% "34-end.bin"⟩

private theorem local34 : Light.Local p34 8704 (Light.input 8192 4352 seed34 weights34) := by
  constructor <;> decide +kernel

theorem c34 : Light.Checked p34 8704 :=
  Light.of_local (Light.window_chunk (tail := rest35) seed_ok34 drop34 (by decide +kernel)) local34

noncomputable def p35 : Piece := ⟨256, tailInts% "35-g.bin", q35,
  tailInt% "35-s.bin", tailInt% "35-v.bin", tailInt% "35-u.bin", tailInt% "35-w.bin", tailInt% "35-den.bin", tailInt% "35-end.bin"⟩

private theorem local35 : Light.Local p35 8960 (Light.input 8192 4480 seed35 weights35) := by
  constructor <;> decide +kernel

theorem c35 : Light.Checked p35 8960 :=
  Light.of_local (Light.window_chunk (tail := rest36) seed_ok35 drop35 (by decide +kernel)) local35

end NextProof.Tail.Shards
