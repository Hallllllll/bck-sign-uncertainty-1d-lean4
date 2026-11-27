import NextProof.OptEdge00130Data
import NextProof.EdgeDyadicLiteral
namespace NextProof.EdgeRecovery.R01.P.At8192
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk0 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk1 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk2 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk3 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk4 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk5 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk6 :=
  checked 7 2048 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .parent 8192 NextProof.EdgeRecovery.R01.P.chunk7 :=
  checked 7 2049 (dyadicValue% "parent" 8192 7 NextProof.EdgeRecovery.R01.P.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .parent 8192 NextProof.EdgeRecovery.R01.P.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.P.At8192
namespace NextProof.EdgeRecovery.R01.C.At8192
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8192 NextProof.EdgeRecovery.R01.C.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.C.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8192 NextProof.EdgeRecovery.R01.C.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.C.At8192
namespace NextProof.EdgeRecovery.R01.E.At8192
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8192 NextProof.EdgeRecovery.R01.E.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8192 7 NextProof.EdgeRecovery.R01.E.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8192 NextProof.EdgeRecovery.R01.E.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.E.At8192
namespace NextProof.EdgeRecovery.R01
open NextProof.Compact NextProof.Tail
set_option maxHeartbeats 0
set_option maxRecDepth 150000
theorem point8192 : fastHom 1 ((2:ℤ)^8192) P.data = (2:ℤ)^28182*C.data.subst ((2:ℤ)^8192)+E.data.subst ((2:ℤ)^8192) :=
  at_point 28182 P.At8192.result C.At8192.result E.At8192.result (by decide +kernel)
end NextProof.EdgeRecovery.R01
namespace NextProof.EdgeRecovery.R01.P.At8193
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk0 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk1 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk2 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk3 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk4 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk5 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk6 :=
  checked 7 2048 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .parent 8193 NextProof.EdgeRecovery.R01.P.chunk7 :=
  checked 7 2049 (dyadicValue% "parent" 8193 7 NextProof.EdgeRecovery.R01.P.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .parent 8193 NextProof.EdgeRecovery.R01.P.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.P.At8193
namespace NextProof.EdgeRecovery.R01.C.At8193
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8193 NextProof.EdgeRecovery.R01.C.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.C.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8193 NextProof.EdgeRecovery.R01.C.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.C.At8193
namespace NextProof.EdgeRecovery.R01.E.At8193
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8193 NextProof.EdgeRecovery.R01.E.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8193 7 NextProof.EdgeRecovery.R01.E.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8193 NextProof.EdgeRecovery.R01.E.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.E.At8193
namespace NextProof.EdgeRecovery.R01
open NextProof.Compact NextProof.Tail
set_option maxHeartbeats 0
set_option maxRecDepth 150000
theorem point8193 : fastHom 1 ((2:ℤ)^8193) P.data = (2:ℤ)^28182*C.data.subst ((2:ℤ)^8193)+E.data.subst ((2:ℤ)^8193) :=
  at_point 28182 P.At8193.result C.At8193.result E.At8193.result (by decide +kernel)
end NextProof.EdgeRecovery.R01
namespace NextProof.EdgeRecovery.R01.P.At8194
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk0 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk1 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk2 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk3 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk4 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk5 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk6 :=
  checked 7 2048 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .parent 8194 NextProof.EdgeRecovery.R01.P.chunk7 :=
  checked 7 2049 (dyadicValue% "parent" 8194 7 NextProof.EdgeRecovery.R01.P.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .parent 8194 NextProof.EdgeRecovery.R01.P.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.P.At8194
namespace NextProof.EdgeRecovery.R01.C.At8194
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8194 NextProof.EdgeRecovery.R01.C.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.C.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8194 NextProof.EdgeRecovery.R01.C.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.C.At8194
namespace NextProof.EdgeRecovery.R01.E.At8194
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8194 NextProof.EdgeRecovery.R01.E.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8194 7 NextProof.EdgeRecovery.R01.E.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8194 NextProof.EdgeRecovery.R01.E.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.E.At8194
namespace NextProof.EdgeRecovery.R01
open NextProof.Compact NextProof.Tail
set_option maxHeartbeats 0
set_option maxRecDepth 150000
theorem point8194 : fastHom 1 ((2:ℤ)^8194) P.data = (2:ℤ)^28182*C.data.subst ((2:ℤ)^8194)+E.data.subst ((2:ℤ)^8194) :=
  at_point 28182 P.At8194.result C.At8194.result E.At8194.result (by decide +kernel)
end NextProof.EdgeRecovery.R01
namespace NextProof.EdgeRecovery.R01.P.At8195
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk0 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk1 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk2 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk3 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk4 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk5 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk6 :=
  checked 7 2048 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .parent 8195 NextProof.EdgeRecovery.R01.P.chunk7 :=
  checked 7 2049 (dyadicValue% "parent" 8195 7 NextProof.EdgeRecovery.R01.P.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .parent 8195 NextProof.EdgeRecovery.R01.P.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.P.At8195
namespace NextProof.EdgeRecovery.R01.C.At8195
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8195 NextProof.EdgeRecovery.R01.C.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.C.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8195 NextProof.EdgeRecovery.R01.C.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.C.At8195
namespace NextProof.EdgeRecovery.R01.E.At8195
open NextProof.Tail
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 150000
set_option exponentiation.threshold 1000000
noncomputable def piece0 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk0 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk0) (by decide +kernel) (by decide +kernel)
noncomputable def piece1 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk1 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk1) (by decide +kernel) (by decide +kernel)
noncomputable def piece2 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk2 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk2) (by decide +kernel) (by decide +kernel)
noncomputable def piece3 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk3 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk3) (by decide +kernel) (by decide +kernel)
noncomputable def piece4 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk4 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk4) (by decide +kernel) (by decide +kernel)
noncomputable def piece5 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk5 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk5) (by decide +kernel) (by decide +kernel)
noncomputable def piece6 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk6 :=
  checked 7 2048 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk6) (by decide +kernel) (by decide +kernel)
noncomputable def piece7 : Part .plain 8195 NextProof.EdgeRecovery.R01.E.chunk7 :=
  checked 7 2049 (dyadicValue% "plain" 8195 7 NextProof.EdgeRecovery.R01.E.chunk7) (by decide +kernel) (by decide +kernel)
noncomputable def result : Part .plain 8195 NextProof.EdgeRecovery.R01.E.data := (merge (merge (merge piece0 piece1) (merge piece2 piece3)) (merge (merge piece4 piece5) (merge piece6 piece7)))
end
end NextProof.EdgeRecovery.R01.E.At8195
namespace NextProof.EdgeRecovery.R01
open NextProof.Compact NextProof.Tail
set_option maxHeartbeats 0
set_option maxRecDepth 150000
theorem point8195 : fastHom 1 ((2:ℤ)^8195) P.data = (2:ℤ)^28182*C.data.subst ((2:ℤ)^8195)+E.data.subst ((2:ℤ)^8195) :=
  at_point 28182 P.At8195.result C.At8195.result E.At8195.result (by decide +kernel)
end NextProof.EdgeRecovery.R01
