import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData09

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p36 : Piece := ⟨256, tailInts% "36-g.bin", q36,
  tailInt% "36-s.bin", tailInt% "36-v.bin", tailInt% "36-u.bin", tailInt% "36-w.bin", tailInt% "36-den.bin", tailInt% "36-end.bin"⟩

private theorem local36 : Light.Local p36 9216 (Light.input 8192 4608 seed36 weights36) := by
  constructor <;> decide +kernel

theorem c36 : Light.Checked p36 9216 :=
  Light.of_local (Light.window_chunk (tail := rest37) seed_ok36 drop36 (by decide +kernel)) local36

noncomputable def p37 : Piece := ⟨256, tailInts% "37-g.bin", q37,
  tailInt% "37-s.bin", tailInt% "37-v.bin", tailInt% "37-u.bin", tailInt% "37-w.bin", tailInt% "37-den.bin", tailInt% "37-end.bin"⟩

private theorem local37 : Light.Local p37 9472 (Light.input 8192 4736 seed37 weights37) := by
  constructor <;> decide +kernel

theorem c37 : Light.Checked p37 9472 :=
  Light.of_local (Light.window_chunk (tail := rest38) seed_ok37 drop37 (by decide +kernel)) local37

noncomputable def p38 : Piece := ⟨256, tailInts% "38-g.bin", q38,
  tailInt% "38-s.bin", tailInt% "38-v.bin", tailInt% "38-u.bin", tailInt% "38-w.bin", tailInt% "38-den.bin", tailInt% "38-end.bin"⟩

private theorem local38 : Light.Local p38 9728 (Light.input 8192 4864 seed38 weights38) := by
  constructor <;> decide +kernel

theorem c38 : Light.Checked p38 9728 :=
  Light.of_local (Light.window_chunk (tail := rest39) seed_ok38 drop38 (by decide +kernel)) local38

noncomputable def p39 : Piece := ⟨256, tailInts% "39-g.bin", q39,
  tailInt% "39-s.bin", tailInt% "39-v.bin", tailInt% "39-u.bin", tailInt% "39-w.bin", tailInt% "39-den.bin", tailInt% "39-end.bin"⟩

private theorem local39 : Light.Local p39 9984 (Light.input 8192 4992 seed39 weights39) := by
  constructor <;> decide +kernel

theorem c39 : Light.Checked p39 9984 :=
  Light.of_local (Light.window_chunk (tail := rest40) seed_ok39 drop39 (by decide +kernel)) local39

end NextProof.Tail.Shards
