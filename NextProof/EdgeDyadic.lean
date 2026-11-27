import NextProof.EdgeArithmetic

namespace NextProof.EdgeRecovery
open NextProof.Tail NextProof.Compact

/-- Evaluation at a power of two. Each join shifts its high block. -/
def pack (b : ℕ) : Blocks → ℤ
  | .empty => 0
  | .leaf a => a
  | .join lo hi => pack b lo + (pack b hi <<< (b*lo.size))

theorem pack_eq (b : ℕ) (p : Blocks) : pack b p = p.subst ((2:ℤ)^b) := by
  induction p with
  | empty => rfl
  | leaf => rfl
  | join lo hi hl hh =>
    simp only [pack, Blocks.subst, hl, hh, Int.shiftLeft_eq, pow_mul]
    ring

/-- Within a small tile, multiplication by 1+2^b needs an addition and a shift. -/
def tile (b : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: rest =>
    let u := tile b rest
    (a <<< (rest.length+1)) + u + (u <<< b)

theorem tile_eq (b : ℕ) (xs : List ℤ) : tile b xs = halfForm ((2:ℤ)^b) 1 xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [tile,halfForm,ih,Int.shiftLeft_eq,Int.cast_id]
    ring

/-- Use general products only above the tile boundary. -/
def hom (b : ℕ) : ℕ → Blocks → ℤ
  | 0, p => tile b p.list
  | _+1, .empty => 0
  | _+1, .leaf a => 2*a
  | d+1, .join lo hi =>
    (hom b d lo <<< hi.size) + ((2:ℤ)^b+1)^lo.size * hom b d hi

theorem hom_eq (b d : ℕ) (p : Blocks) : hom b d p = fastHom 1 ((2:ℤ)^b) p := by
  induction d generalizing p with
  | zero => exact (tile_eq b p.list).trans (fastHom_spec 1 _ p).symm
  | succ d ih =>
    cases p with
    | empty => rfl
    | leaf => rfl
    | join lo hi =>
      simp only [hom,fastHom,ih,Int.shiftLeft_eq]
      ring

inductive Kind | parent | plain

def read (m : Kind) (b : ℕ) (p : Blocks) : ℤ :=
  match m with
  | .parent => fastHom 1 ((2:ℤ)^b) p
  | .plain => p.subst ((2:ℤ)^b)

def ground (m : Kind) (b depth : ℕ) (p : Blocks) : ℤ :=
  match m with
  | .parent => hom b depth p
  | .plain => pack b p

theorem ground_eq (m : Kind) (b depth : ℕ) (p : Blocks) : ground m b depth p = read m b p := by
  cases m with
  | parent => exact hom_eq b depth p
  | plain => exact pack_eq b p

def combine (m : Kind) (b nLo nHi : ℕ) (lo hi : ℤ) : ℤ :=
  match m with
  | .parent => (lo <<< nHi) + ((2:ℤ)^b+1)^nLo * hi
  | .plain => lo + (hi <<< (b*nLo))

theorem read_join (m : Kind) (b : ℕ) (l r : Blocks) :
    read m b (.join l r) = combine m b l.size r.size (read m b l) (read m b r) := by
  cases m <;> simp only [read,combine,fastHom,Blocks.subst,Int.shiftLeft_eq,pow_mul] <;> ring

structure Part (m : Kind) (b : ℕ) (p : Blocks) where
  width : ℕ
  value : ℤ
  width_eq : p.size = width
  value_eq : read m b p = value

def checked {p : Blocks} {m : Kind} {b : ℕ} (d n : ℕ) (v : ℤ)
    (hn : p.size = n) (hv : ground m b d p = v) : Part m b p :=
  ⟨n, v, hn, (ground_eq m b d p).symm.trans hv⟩

def merge {p q : Blocks} {m : Kind} {b : ℕ}
    (l : Part m b p) (r : Part m b q) : Part m b (.join p q) where
  width := l.width+r.width
  value := combine m b l.width r.width l.value r.value
  width_eq := by simp only [Blocks.size,l.width_eq,r.width_eq]
  value_eq := by rw [read_join,l.width_eq,r.width_eq,l.value_eq,r.value_eq]

theorem at_point {p c e : Blocks} {b : ℕ} (k : ℕ)
    (hp : Part .parent b p) (hc : Part .plain b c) (he : Part .plain b e)
    (ok : hp.value = (hc.value <<< k) + he.value) :
    fastHom 1 ((2:ℤ)^b) p = (2:ℤ)^k*c.subst ((2:ℤ)^b)+e.subst ((2:ℤ)^b) := by
  change read .parent b p = (2:ℤ)^k * read .plain b c + read .plain b e
  rw [hp.value_eq,hc.value_eq,he.value_eq,ok,Int.shiftLeft_eq,mul_comm hc.value]

end NextProof.EdgeRecovery
