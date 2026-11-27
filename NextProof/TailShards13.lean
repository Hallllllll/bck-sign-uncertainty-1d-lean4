import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData13

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p52 : Piece := ⟨256, tailInts% "52-g.bin", q52,
  tailInt% "52-s.bin", tailInt% "52-v.bin", tailInt% "52-u.bin", tailInt% "52-w.bin", tailInt% "52-den.bin", tailInt% "52-end.bin"⟩

private theorem local52 : Light.Local p52 13312 (Light.input 8192 6656 seed52 weights52) := by
  constructor <;> decide +kernel

theorem c52 : Light.Checked p52 13312 :=
  Light.of_local (Light.window_chunk (tail := rest53) seed_ok52 drop52 (by decide +kernel)) local52

noncomputable def p53 : Piece := ⟨256, tailInts% "53-g.bin", q53,
  tailInt% "53-s.bin", tailInt% "53-v.bin", tailInt% "53-u.bin", tailInt% "53-w.bin", tailInt% "53-den.bin", tailInt% "53-end.bin"⟩

private theorem local53 : Light.Local p53 13568 (Light.input 8192 6784 seed53 weights53) := by
  constructor <;> decide +kernel

theorem c53 : Light.Checked p53 13568 :=
  Light.of_local (Light.window_chunk (tail := rest54) seed_ok53 drop53 (by decide +kernel)) local53

noncomputable def p54 : Piece := ⟨256, tailInts% "54-g.bin", q54,
  tailInt% "54-s.bin", tailInt% "54-v.bin", tailInt% "54-u.bin", tailInt% "54-w.bin", tailInt% "54-den.bin", tailInt% "54-end.bin"⟩

private theorem local54 : Light.Local p54 13824 (Light.input 8192 6912 seed54 weights54) := by
  constructor <;> decide +kernel

theorem c54 : Light.Checked p54 13824 :=
  Light.of_local (Light.window_chunk (tail := rest55) seed_ok54 drop54 (by decide +kernel)) local54

noncomputable def p55 : Piece := ⟨256, tailInts% "55-g.bin", q55,
  tailInt% "55-s.bin", tailInt% "55-v.bin", tailInt% "55-u.bin", tailInt% "55-w.bin", tailInt% "55-den.bin", tailInt% "55-end.bin"⟩

private theorem local55 : Light.Local p55 14080 (Light.input 8192 7040 seed55 weights55) := by
  constructor <;> decide +kernel

theorem c55 : Light.Checked p55 14080 :=
  Light.of_local (Light.window_chunk (tail := rest56) seed_ok55 drop55 (by decide +kernel)) local55

end NextProof.Tail.Shards
