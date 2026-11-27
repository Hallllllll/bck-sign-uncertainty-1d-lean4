import NextProof.TailShardLight

namespace NextProof.Tail.Shards.Light

def bump (k c : ℕ) : ℕ :=
  let step (j v : ℕ) := 2*(2*j+1)*v/(j+1)
  step (2*k+1) (step (2*k) c)

def seed : ℕ → ℕ
  | 0 => 1
  | n+1 => bump n (seed n)

def advance (k c : ℕ) : ℕ → ℕ
  | 0 => c
  | n+1 => bump (k+n) (advance k c n)

theorem seed_add (k n : ℕ) : seed (k+n) = advance k (seed k) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (bump (k+n)) ih

private theorem input_drop (N k a : ℕ) (ws : List ℤ) :
    (input N k (seed k) ws).drop (2*a) = input N (k+a) (seed (k+a)) (ws.drop a) := by
  induction a generalizing k ws with
  | zero => simp
  | succ a ih =>
    cases ws with
    | nil => simp [input]
    | cons w ws =>
      rw [Nat.mul_succ]
      change (input N (k+1) (seed (k+1)) ws).drop (2*a) = _
      rw [ih]
      rw [show k+1+a = k+(a+1) by omega]
      rfl

theorem window_at (a n c : ℕ) (hs : seed a = c) :
    window (2*a) n = (input 8192 a c (Exterior.Data16384.weights.drop a)).take n := by
  unfold window
  rw [show (1:ℕ)=seed 0 by rfl, input_drop, Nat.zero_add, hs]

private theorem take_input (N k c : ℕ) (ws t : List ℤ) :
    (input N k c (ws++t)).take (2*ws.length) = input N k c ws := by
  induction ws generalizing k c with
  | nil => simp [input]
  | cons w ws ih =>
    simp only [List.length_cons, Nat.mul_succ,List.cons_append,input,List.take_succ_cons,ih]

theorem window_chunk {i n c : ℕ} {w tail : List ℤ} (hc : seed i=c)
    (hw : Exterior.Data16384.weights.drop i = w ++ tail) (hn : n=2*w.length) :
    window (2*i) n = input 8192 i c w := by
  rw [window_at i n c hc,hw,hn,take_input]

structure Local (p : Piece) (k : ℕ) (src : List ℤ) : Prop where
  width : src.length=p.n
  widthG : p.g.length=p.n
  input : value (1+radix) 9 src=p.inputVal
  output : value radix 9 p.g=p.outputVal
  inputBound : value 2 9 (src.map (fun a => (a.natAbs : ℤ)))=p.inputMajor
  outputBound : value 1 9 (p.g.map (fun a => (a.natAbs : ℤ)))=p.outputMajor
  floor : floors p.g k (2^100*(-131072)^k) p.firstDen=p.q
  endD : endDen p.n k p.firstDen=p.afterDen

theorem of_local {p : Piece} {k : ℕ} {src : List ℤ}
    (he : window k p.n = src) (h : Local p k src) : Checked p k := by
  subst src
  exact ⟨h.width,h.widthG,h.input,h.output,h.inputBound,h.outputBound,h.floor,h.endD⟩

end NextProof.Tail.Shards.Light
