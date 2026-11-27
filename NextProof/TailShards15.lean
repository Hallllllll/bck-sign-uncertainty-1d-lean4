import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData15

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p60 : Piece := ⟨256, tailInts% "60-g.bin", q60,
  tailInt% "60-s.bin", tailInt% "60-v.bin", tailInt% "60-u.bin", tailInt% "60-w.bin", tailInt% "60-den.bin", tailInt% "60-end.bin"⟩

private theorem local60 : Light.Local p60 15360 (Light.input 8192 7680 seed60 weights60) := by
  constructor <;> decide +kernel

theorem c60 : Light.Checked p60 15360 :=
  Light.of_local (Light.window_chunk (tail := rest61) seed_ok60 drop60 (by decide +kernel)) local60

noncomputable def p61 : Piece := ⟨256, tailInts% "61-g.bin", q61,
  tailInt% "61-s.bin", tailInt% "61-v.bin", tailInt% "61-u.bin", tailInt% "61-w.bin", tailInt% "61-den.bin", tailInt% "61-end.bin"⟩

private theorem local61 : Light.Local p61 15616 (Light.input 8192 7808 seed61 weights61) := by
  constructor <;> decide +kernel

theorem c61 : Light.Checked p61 15616 :=
  Light.of_local (Light.window_chunk (tail := rest62) seed_ok61 drop61 (by decide +kernel)) local61

noncomputable def p62 : Piece := ⟨256, tailInts% "62-g.bin", q62,
  tailInt% "62-s.bin", tailInt% "62-v.bin", tailInt% "62-u.bin", tailInt% "62-w.bin", tailInt% "62-den.bin", tailInt% "62-end.bin"⟩

private theorem local62 : Light.Local p62 15872 (Light.input 8192 7936 seed62 weights62) := by
  constructor <;> decide +kernel

theorem c62 : Light.Checked p62 15872 :=
  Light.of_local (Light.window_chunk (tail := rest63) seed_ok62 drop62 (by decide +kernel)) local62

noncomputable def p63 : Piece := ⟨256, tailInts% "63-g.bin", q63,
  tailInt% "63-s.bin", tailInt% "63-v.bin", tailInt% "63-u.bin", tailInt% "63-w.bin", tailInt% "63-den.bin", tailInt% "63-end.bin"⟩

private theorem local63 : Light.Local p63 16128 (Light.input 8192 8064 seed63 weights63) := by
  constructor <;> decide +kernel

theorem c63 : Light.Checked p63 16128 :=
  Light.of_local (Light.window_chunk (tail := rest64) seed_ok63 drop63 (by decide +kernel)) local63

end NextProof.Tail.Shards
