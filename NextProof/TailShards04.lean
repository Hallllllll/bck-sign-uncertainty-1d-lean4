import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData04

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p16 : Piece := ⟨256, tailInts% "16-g.bin", q16,
  tailInt% "16-s.bin", tailInt% "16-v.bin", tailInt% "16-u.bin", tailInt% "16-w.bin", tailInt% "16-den.bin", tailInt% "16-end.bin"⟩

private theorem local16 : Light.Local p16 4096 (Light.input 8192 2048 seed16 weights16) := by
  constructor <;> decide +kernel

theorem c16 : Light.Checked p16 4096 :=
  Light.of_local (Light.window_chunk (tail := rest17) seed_ok16 drop16 (by decide +kernel)) local16

noncomputable def p17 : Piece := ⟨256, tailInts% "17-g.bin", q17,
  tailInt% "17-s.bin", tailInt% "17-v.bin", tailInt% "17-u.bin", tailInt% "17-w.bin", tailInt% "17-den.bin", tailInt% "17-end.bin"⟩

private theorem local17 : Light.Local p17 4352 (Light.input 8192 2176 seed17 weights17) := by
  constructor <;> decide +kernel

theorem c17 : Light.Checked p17 4352 :=
  Light.of_local (Light.window_chunk (tail := rest18) seed_ok17 drop17 (by decide +kernel)) local17

noncomputable def p18 : Piece := ⟨256, tailInts% "18-g.bin", q18,
  tailInt% "18-s.bin", tailInt% "18-v.bin", tailInt% "18-u.bin", tailInt% "18-w.bin", tailInt% "18-den.bin", tailInt% "18-end.bin"⟩

private theorem local18 : Light.Local p18 4608 (Light.input 8192 2304 seed18 weights18) := by
  constructor <;> decide +kernel

theorem c18 : Light.Checked p18 4608 :=
  Light.of_local (Light.window_chunk (tail := rest19) seed_ok18 drop18 (by decide +kernel)) local18

noncomputable def p19 : Piece := ⟨256, tailInts% "19-g.bin", q19,
  tailInt% "19-s.bin", tailInt% "19-v.bin", tailInt% "19-u.bin", tailInt% "19-w.bin", tailInt% "19-den.bin", tailInt% "19-end.bin"⟩

private theorem local19 : Light.Local p19 4864 (Light.input 8192 2432 seed19 weights19) := by
  constructor <;> decide +kernel

theorem c19 : Light.Checked p19 4864 :=
  Light.of_local (Light.window_chunk (tail := rest20) seed_ok19 drop19 (by decide +kernel)) local19

end NextProof.Tail.Shards
