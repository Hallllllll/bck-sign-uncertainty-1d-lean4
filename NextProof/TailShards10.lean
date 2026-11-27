import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData10

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p40 : Piece := ⟨256, tailInts% "40-g.bin", q40,
  tailInt% "40-s.bin", tailInt% "40-v.bin", tailInt% "40-u.bin", tailInt% "40-w.bin", tailInt% "40-den.bin", tailInt% "40-end.bin"⟩

private theorem local40 : Light.Local p40 10240 (Light.input 8192 5120 seed40 weights40) := by
  constructor <;> decide +kernel

theorem c40 : Light.Checked p40 10240 :=
  Light.of_local (Light.window_chunk (tail := rest41) seed_ok40 drop40 (by decide +kernel)) local40

noncomputable def p41 : Piece := ⟨256, tailInts% "41-g.bin", q41,
  tailInt% "41-s.bin", tailInt% "41-v.bin", tailInt% "41-u.bin", tailInt% "41-w.bin", tailInt% "41-den.bin", tailInt% "41-end.bin"⟩

private theorem local41 : Light.Local p41 10496 (Light.input 8192 5248 seed41 weights41) := by
  constructor <;> decide +kernel

theorem c41 : Light.Checked p41 10496 :=
  Light.of_local (Light.window_chunk (tail := rest42) seed_ok41 drop41 (by decide +kernel)) local41

noncomputable def p42 : Piece := ⟨256, tailInts% "42-g.bin", q42,
  tailInt% "42-s.bin", tailInt% "42-v.bin", tailInt% "42-u.bin", tailInt% "42-w.bin", tailInt% "42-den.bin", tailInt% "42-end.bin"⟩

private theorem local42 : Light.Local p42 10752 (Light.input 8192 5376 seed42 weights42) := by
  constructor <;> decide +kernel

theorem c42 : Light.Checked p42 10752 :=
  Light.of_local (Light.window_chunk (tail := rest43) seed_ok42 drop42 (by decide +kernel)) local42

noncomputable def p43 : Piece := ⟨256, tailInts% "43-g.bin", q43,
  tailInt% "43-s.bin", tailInt% "43-v.bin", tailInt% "43-u.bin", tailInt% "43-w.bin", tailInt% "43-den.bin", tailInt% "43-end.bin"⟩

private theorem local43 : Light.Local p43 11008 (Light.input 8192 5504 seed43 weights43) := by
  constructor <;> decide +kernel

theorem c43 : Light.Checked p43 11008 :=
  Light.of_local (Light.window_chunk (tail := rest44) seed_ok43 drop43 (by decide +kernel)) local43

end NextProof.Tail.Shards
