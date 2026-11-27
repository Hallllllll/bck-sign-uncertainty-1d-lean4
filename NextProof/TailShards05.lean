import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData05

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p20 : Piece := ⟨256, tailInts% "20-g.bin", q20,
  tailInt% "20-s.bin", tailInt% "20-v.bin", tailInt% "20-u.bin", tailInt% "20-w.bin", tailInt% "20-den.bin", tailInt% "20-end.bin"⟩

private theorem local20 : Light.Local p20 5120 (Light.input 8192 2560 seed20 weights20) := by
  constructor <;> decide +kernel

theorem c20 : Light.Checked p20 5120 :=
  Light.of_local (Light.window_chunk (tail := rest21) seed_ok20 drop20 (by decide +kernel)) local20

noncomputable def p21 : Piece := ⟨256, tailInts% "21-g.bin", q21,
  tailInt% "21-s.bin", tailInt% "21-v.bin", tailInt% "21-u.bin", tailInt% "21-w.bin", tailInt% "21-den.bin", tailInt% "21-end.bin"⟩

private theorem local21 : Light.Local p21 5376 (Light.input 8192 2688 seed21 weights21) := by
  constructor <;> decide +kernel

theorem c21 : Light.Checked p21 5376 :=
  Light.of_local (Light.window_chunk (tail := rest22) seed_ok21 drop21 (by decide +kernel)) local21

noncomputable def p22 : Piece := ⟨256, tailInts% "22-g.bin", q22,
  tailInt% "22-s.bin", tailInt% "22-v.bin", tailInt% "22-u.bin", tailInt% "22-w.bin", tailInt% "22-den.bin", tailInt% "22-end.bin"⟩

private theorem local22 : Light.Local p22 5632 (Light.input 8192 2816 seed22 weights22) := by
  constructor <;> decide +kernel

theorem c22 : Light.Checked p22 5632 :=
  Light.of_local (Light.window_chunk (tail := rest23) seed_ok22 drop22 (by decide +kernel)) local22

noncomputable def p23 : Piece := ⟨256, tailInts% "23-g.bin", q23,
  tailInt% "23-s.bin", tailInt% "23-v.bin", tailInt% "23-u.bin", tailInt% "23-w.bin", tailInt% "23-den.bin", tailInt% "23-end.bin"⟩

private theorem local23 : Light.Local p23 5888 (Light.input 8192 2944 seed23 weights23) := by
  constructor <;> decide +kernel

theorem c23 : Light.Checked p23 5888 :=
  Light.of_local (Light.window_chunk (tail := rest24) seed_ok23 drop23 (by decide +kernel)) local23

end NextProof.Tail.Shards
