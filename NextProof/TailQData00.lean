import NextProof.TailShardIO

namespace NextProof.Tail.Shards

noncomputable def q00 : List Int := tailInts% "00-q.bin"

noncomputable def q01 : List Int := tailInts% "01-q.bin"

noncomputable def q02 : List Int := tailInts% "02-q.bin"

noncomputable def q03 : List Int := tailInts% "03-q.bin"

end NextProof.Tail.Shards
