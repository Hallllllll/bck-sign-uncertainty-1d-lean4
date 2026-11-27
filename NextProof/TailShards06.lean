import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData06

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p24 : Piece := ⟨256, tailInts% "24-g.bin", q24,
  tailInt% "24-s.bin", tailInt% "24-v.bin", tailInt% "24-u.bin", tailInt% "24-w.bin", tailInt% "24-den.bin", tailInt% "24-end.bin"⟩

private theorem local24 : Light.Local p24 6144 (Light.input 8192 3072 seed24 weights24) := by
  constructor <;> decide +kernel

theorem c24 : Light.Checked p24 6144 :=
  Light.of_local (Light.window_chunk (tail := rest25) seed_ok24 drop24 (by decide +kernel)) local24

noncomputable def p25 : Piece := ⟨256, tailInts% "25-g.bin", q25,
  tailInt% "25-s.bin", tailInt% "25-v.bin", tailInt% "25-u.bin", tailInt% "25-w.bin", tailInt% "25-den.bin", tailInt% "25-end.bin"⟩

private theorem local25 : Light.Local p25 6400 (Light.input 8192 3200 seed25 weights25) := by
  constructor <;> decide +kernel

theorem c25 : Light.Checked p25 6400 :=
  Light.of_local (Light.window_chunk (tail := rest26) seed_ok25 drop25 (by decide +kernel)) local25

noncomputable def p26 : Piece := ⟨256, tailInts% "26-g.bin", q26,
  tailInt% "26-s.bin", tailInt% "26-v.bin", tailInt% "26-u.bin", tailInt% "26-w.bin", tailInt% "26-den.bin", tailInt% "26-end.bin"⟩

private theorem local26 : Light.Local p26 6656 (Light.input 8192 3328 seed26 weights26) := by
  constructor <;> decide +kernel

theorem c26 : Light.Checked p26 6656 :=
  Light.of_local (Light.window_chunk (tail := rest27) seed_ok26 drop26 (by decide +kernel)) local26

noncomputable def p27 : Piece := ⟨256, tailInts% "27-g.bin", q27,
  tailInt% "27-s.bin", tailInt% "27-v.bin", tailInt% "27-u.bin", tailInt% "27-w.bin", tailInt% "27-den.bin", tailInt% "27-end.bin"⟩

private theorem local27 : Light.Local p27 6912 (Light.input 8192 3456 seed27 weights27) := by
  constructor <;> decide +kernel

theorem c27 : Light.Checked p27 6912 :=
  Light.of_local (Light.window_chunk (tail := rest28) seed_ok27 drop27 (by decide +kernel)) local27

end NextProof.Tail.Shards
