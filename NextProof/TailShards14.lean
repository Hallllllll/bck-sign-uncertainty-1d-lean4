import NextProof.TailShardSeeds

import NextProof.TailShardWeights

import NextProof.TailQData14

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

noncomputable def p56 : Piece := ⟨256, tailInts% "56-g.bin", q56,
  tailInt% "56-s.bin", tailInt% "56-v.bin", tailInt% "56-u.bin", tailInt% "56-w.bin", tailInt% "56-den.bin", tailInt% "56-end.bin"⟩

private theorem local56 : Light.Local p56 14336 (Light.input 8192 7168 seed56 weights56) := by
  constructor <;> decide +kernel

theorem c56 : Light.Checked p56 14336 :=
  Light.of_local (Light.window_chunk (tail := rest57) seed_ok56 drop56 (by decide +kernel)) local56

noncomputable def p57 : Piece := ⟨256, tailInts% "57-g.bin", q57,
  tailInt% "57-s.bin", tailInt% "57-v.bin", tailInt% "57-u.bin", tailInt% "57-w.bin", tailInt% "57-den.bin", tailInt% "57-end.bin"⟩

private theorem local57 : Light.Local p57 14592 (Light.input 8192 7296 seed57 weights57) := by
  constructor <;> decide +kernel

theorem c57 : Light.Checked p57 14592 :=
  Light.of_local (Light.window_chunk (tail := rest58) seed_ok57 drop57 (by decide +kernel)) local57

noncomputable def p58 : Piece := ⟨256, tailInts% "58-g.bin", q58,
  tailInt% "58-s.bin", tailInt% "58-v.bin", tailInt% "58-u.bin", tailInt% "58-w.bin", tailInt% "58-den.bin", tailInt% "58-end.bin"⟩

private theorem local58 : Light.Local p58 14848 (Light.input 8192 7424 seed58 weights58) := by
  constructor <;> decide +kernel

theorem c58 : Light.Checked p58 14848 :=
  Light.of_local (Light.window_chunk (tail := rest59) seed_ok58 drop58 (by decide +kernel)) local58

noncomputable def p59 : Piece := ⟨256, tailInts% "59-g.bin", q59,
  tailInt% "59-s.bin", tailInt% "59-v.bin", tailInt% "59-u.bin", tailInt% "59-w.bin", tailInt% "59-den.bin", tailInt% "59-end.bin"⟩

private theorem local59 : Light.Local p59 15104 (Light.input 8192 7552 seed59 weights59) := by
  constructor <;> decide +kernel

theorem c59 : Light.Checked p59 15104 :=
  Light.of_local (Light.window_chunk (tail := rest60) seed_ok59 drop59 (by decide +kernel)) local59

end NextProof.Tail.Shards
