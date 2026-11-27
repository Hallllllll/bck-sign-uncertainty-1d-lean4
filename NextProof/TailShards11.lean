import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData11

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p44 : Piece := ⟨256, tailInts% "44-g.bin", q44,
  tailInt% "44-s.bin", tailInt% "44-v.bin", tailInt% "44-u.bin", tailInt% "44-w.bin", tailInt% "44-den.bin", tailInt% "44-end.bin"⟩

private theorem local44 : Light.Local p44 11264 (Light.input 8192 5632 seed44 weights44) := by
  constructor <;> decide +kernel

theorem c44 : Light.Checked p44 11264 :=
  Light.of_local (Light.window_chunk (tail := rest45) seed_ok44 drop44 (by decide +kernel)) local44

noncomputable def p45 : Piece := ⟨256, tailInts% "45-g.bin", q45,
  tailInt% "45-s.bin", tailInt% "45-v.bin", tailInt% "45-u.bin", tailInt% "45-w.bin", tailInt% "45-den.bin", tailInt% "45-end.bin"⟩

private theorem local45 : Light.Local p45 11520 (Light.input 8192 5760 seed45 weights45) := by
  constructor <;> decide +kernel

theorem c45 : Light.Checked p45 11520 :=
  Light.of_local (Light.window_chunk (tail := rest46) seed_ok45 drop45 (by decide +kernel)) local45

noncomputable def p46 : Piece := ⟨256, tailInts% "46-g.bin", q46,
  tailInt% "46-s.bin", tailInt% "46-v.bin", tailInt% "46-u.bin", tailInt% "46-w.bin", tailInt% "46-den.bin", tailInt% "46-end.bin"⟩

private theorem local46 : Light.Local p46 11776 (Light.input 8192 5888 seed46 weights46) := by
  constructor <;> decide +kernel

theorem c46 : Light.Checked p46 11776 :=
  Light.of_local (Light.window_chunk (tail := rest47) seed_ok46 drop46 (by decide +kernel)) local46

noncomputable def p47 : Piece := ⟨256, tailInts% "47-g.bin", q47,
  tailInt% "47-s.bin", tailInt% "47-v.bin", tailInt% "47-u.bin", tailInt% "47-w.bin", tailInt% "47-den.bin", tailInt% "47-end.bin"⟩

private theorem local47 : Light.Local p47 12032 (Light.input 8192 6016 seed47 weights47) := by
  constructor <;> decide +kernel

theorem c47 : Light.Checked p47 12032 :=
  Light.of_local (Light.window_chunk (tail := rest48) seed_ok47 drop47 (by decide +kernel)) local47

end NextProof.Tail.Shards
