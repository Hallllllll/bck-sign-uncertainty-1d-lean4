import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData00

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p00 : Piece := ⟨256, tailInts% "00-g.bin", q00,
  tailInt% "00-s.bin", tailInt% "00-v.bin", tailInt% "00-u.bin", tailInt% "00-w.bin", tailInt% "00-den.bin", tailInt% "00-end.bin"⟩

private theorem local00 : Light.Local p00 0 (Light.input 8192 0 seed00 weights00) := by
  constructor <;> decide +kernel

theorem c00 : Light.Checked p00 0 :=
  Light.of_local (Light.window_chunk (tail := rest01) seed_ok00 drop00 (by decide +kernel)) local00

noncomputable def p01 : Piece := ⟨256, tailInts% "01-g.bin", q01,
  tailInt% "01-s.bin", tailInt% "01-v.bin", tailInt% "01-u.bin", tailInt% "01-w.bin", tailInt% "01-den.bin", tailInt% "01-end.bin"⟩

private theorem local01 : Light.Local p01 256 (Light.input 8192 128 seed01 weights01) := by
  constructor <;> decide +kernel

theorem c01 : Light.Checked p01 256 :=
  Light.of_local (Light.window_chunk (tail := rest02) seed_ok01 drop01 (by decide +kernel)) local01

noncomputable def p02 : Piece := ⟨256, tailInts% "02-g.bin", q02,
  tailInt% "02-s.bin", tailInt% "02-v.bin", tailInt% "02-u.bin", tailInt% "02-w.bin", tailInt% "02-den.bin", tailInt% "02-end.bin"⟩

private theorem local02 : Light.Local p02 512 (Light.input 8192 256 seed02 weights02) := by
  constructor <;> decide +kernel

theorem c02 : Light.Checked p02 512 :=
  Light.of_local (Light.window_chunk (tail := rest03) seed_ok02 drop02 (by decide +kernel)) local02

noncomputable def p03 : Piece := ⟨256, tailInts% "03-g.bin", q03,
  tailInt% "03-s.bin", tailInt% "03-v.bin", tailInt% "03-u.bin", tailInt% "03-w.bin", tailInt% "03-den.bin", tailInt% "03-end.bin"⟩

private theorem local03 : Light.Local p03 768 (Light.input 8192 384 seed03 weights03) := by
  constructor <;> decide +kernel

theorem c03 : Light.Checked p03 768 :=
  Light.of_local (Light.window_chunk (tail := rest04) seed_ok03 drop03 (by decide +kernel)) local03

end NextProof.Tail.Shards
