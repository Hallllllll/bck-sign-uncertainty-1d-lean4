import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData01

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p04 : Piece := ⟨256, tailInts% "04-g.bin", q04,
  tailInt% "04-s.bin", tailInt% "04-v.bin", tailInt% "04-u.bin", tailInt% "04-w.bin", tailInt% "04-den.bin", tailInt% "04-end.bin"⟩

private theorem local04 : Light.Local p04 1024 (Light.input 8192 512 seed04 weights04) := by
  constructor <;> decide +kernel

theorem c04 : Light.Checked p04 1024 :=
  Light.of_local (Light.window_chunk (tail := rest05) seed_ok04 drop04 (by decide +kernel)) local04

noncomputable def p05 : Piece := ⟨256, tailInts% "05-g.bin", q05,
  tailInt% "05-s.bin", tailInt% "05-v.bin", tailInt% "05-u.bin", tailInt% "05-w.bin", tailInt% "05-den.bin", tailInt% "05-end.bin"⟩

private theorem local05 : Light.Local p05 1280 (Light.input 8192 640 seed05 weights05) := by
  constructor <;> decide +kernel

theorem c05 : Light.Checked p05 1280 :=
  Light.of_local (Light.window_chunk (tail := rest06) seed_ok05 drop05 (by decide +kernel)) local05

noncomputable def p06 : Piece := ⟨256, tailInts% "06-g.bin", q06,
  tailInt% "06-s.bin", tailInt% "06-v.bin", tailInt% "06-u.bin", tailInt% "06-w.bin", tailInt% "06-den.bin", tailInt% "06-end.bin"⟩

private theorem local06 : Light.Local p06 1536 (Light.input 8192 768 seed06 weights06) := by
  constructor <;> decide +kernel

theorem c06 : Light.Checked p06 1536 :=
  Light.of_local (Light.window_chunk (tail := rest07) seed_ok06 drop06 (by decide +kernel)) local06

noncomputable def p07 : Piece := ⟨256, tailInts% "07-g.bin", q07,
  tailInt% "07-s.bin", tailInt% "07-v.bin", tailInt% "07-u.bin", tailInt% "07-w.bin", tailInt% "07-den.bin", tailInt% "07-end.bin"⟩

private theorem local07 : Light.Local p07 1792 (Light.input 8192 896 seed07 weights07) := by
  constructor <;> decide +kernel

theorem c07 : Light.Checked p07 1792 :=
  Light.of_local (Light.window_chunk (tail := rest08) seed_ok07 drop07 (by decide +kernel)) local07

end NextProof.Tail.Shards
