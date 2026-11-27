import NextProof.TailShardIO
import NextProof.ExteriorData16384

set_option autoImplicit false

namespace NextProof.Tail.Shards

def radix : ℤ := 2^50000

structure Piece where
  n : ℕ
  g : List ℤ
  q : List ℤ
  inputVal : ℤ
  outputVal : ℤ
  inputMajor : ℤ
  outputMajor : ℤ
  firstDen : ℤ
  afterDen : ℤ

def endDen : ℕ → ℕ → ℤ → ℤ
  | 0, _, d => d
  | n+1, k, d => endDen n (k+1) (d*(2*k+1))

/-- Keep the top equality as arithmetic on ordinary, separately checked block
values. No declaration stores the value of the entire packed polynomial. -/
def join (p q : Piece) : Piece where
  n := p.n+q.n
  g := p.g++q.g
  q := p.q++q.q
  inputVal := p.inputVal + (1+radix)^p.n * q.inputVal
  outputVal := p.outputVal + (q.outputVal <<< (50000*p.n))
  inputMajor := p.inputMajor + 2^p.n*q.inputMajor
  outputMajor := p.outputMajor+q.outputMajor
  firstDen := p.firstDen
  afterDen := q.afterDen

namespace Light

def input (N k c : ℕ) : List ℤ → List ℤ
  | [] => []
  | w::ws =>
    let step (j b : ℕ) := (2*(2*j+1)*b)/(j+1)
    w*c*4^(2*N-2*k) :: 0 :: input N (k+1) (step (2*k+1) (step (2*k) c)) ws

def window (k n : ℕ) := ((input 8192 0 1 Exterior.Data16384.weights).drop k).take n

def slow (x : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::ws => a+x*slow x ws

def value (x : ℤ) : ℕ → List ℤ → ℤ
  | 0, ws => slow x ws
  | d+1, ws =>
    if ws.length ≤ 1 then slow x ws else
      let k := ws.length / 2
      value x d (ws.take k) + x^k * value x d (ws.drop k)

def floors : List ℤ → ℕ → ℤ → ℤ → List ℤ
  | [], _, _, _ => []
  | w::ws, k, m, d => w*m/d :: floors ws (k+1) (m*(-131072)) (d*(2*k+1))

structure Checked (p : Piece) (k : ℕ) : Prop where
  width : (window k p.n).length=p.n
  widthG : p.g.length=p.n
  input : value (1+radix) 9 (window k p.n)=p.inputVal
  output : value radix 9 p.g=p.outputVal
  inputBound : value 2 9 ((window k p.n).map (fun a => (a.natAbs : ℤ)))=p.inputMajor
  outputBound : value 1 9 (p.g.map (fun a => (a.natAbs : ℤ)))=p.outputMajor
  floor : floors p.g k (2^100*(-131072)^k) p.firstDen=p.q
  endD : endDen p.n k p.firstDen=p.afterDen

end Light
end NextProof.Tail.Shards
