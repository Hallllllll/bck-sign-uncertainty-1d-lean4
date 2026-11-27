import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace NextProof.Dual

/-- The n-th and (n+1)-st integer-scaled Laguerre values at a grid node. -/
def advance (q y : ℤ) (n : ℕ) (ab : ℤ × ℤ) : ℤ × ℤ :=
  (ab.2, ((4*(n:ℤ)+5)*q-2*y)*ab.2 - ((2*(n:ℤ)+2)*(2*(n:ℤ)+1))*q^2*ab.1)

def pair (q y : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, q-2*y)
  | n+1 => advance q y n (pair q y n)

abbrev Rule := List (ℤ × ℤ)
def total (r : Rule) : ℤ := (r.map Prod.snd).sum
def moment (q : ℤ) (r : Rule) (k : ℕ) : ℤ :=
  (r.map (fun u => u.2*(pair q u.1 (2*k)).1)).sum

private abbrev Row := (ℤ × ℤ) × (ℤ × ℤ)

private def rows (q : ℤ) (r : Rule) (k : ℕ) : List Row :=
  r.map fun u => (u, pair q u.1 (2*k))

private def twice (q : ℤ) (k : ℕ) (r : Row) : Row :=
  (r.1, advance q r.1.1 (2*k+1) (advance q r.1.1 (2*k) r.2))

private def rowSum (r : List Row) : ℤ := (r.map (fun u => u.1.2 * u.2.1)).sum

private def checkRows (q : ℤ) (k : ℕ) (r : List Row) : ℕ → Bool
  | 0 => true
  | d+1 => (rowSum r == 0) && checkRows q (k+1) (r.map (twice q k)) d

def check (q : ℤ) (r : Rule) (count : ℕ) : Bool :=
  checkRows q 0 (rows q ((0, -total r) :: r) 0) count

private theorem rows_succ (q : ℤ) (r : Rule) (k : ℕ) :
    (rows q r k).map (twice q k) = rows q r (k+1) := by
  simp [rows, twice, List.map_map, Nat.mul_succ, pair, Function.comp_def]

private theorem rowSum_rows (q : ℤ) (r : Rule) (k : ℕ) :
    rowSum (rows q r k) = moment q r k := by
  simp [rows, rowSum, moment, List.map_map, Function.comp_def]

private theorem checks_sound (q : ℤ) (r : Rule) (d : ℕ) :
    ∀ k, checkRows q k (rows q r k) d = true →
      ∀ j < d, moment q r (k+j) = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    intro k h j hj
    simp only [checkRows, Bool.and_eq_true, beq_iff_eq, rowSum_rows, rows_succ] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih (k+1) h.2 j (by omega)

theorem check_sound {q : ℤ} {r : Rule} {n : ℕ} (h : check q r n = true) (k : ℕ)
    (hk : k < n) : moment q r k = total r * (pair q 0 (2*k)).1 := by
  have h' := checks_sound q ((0,-total r)::r) n 0 h k hk
  simp [moment, neg_mul] at h' ⊢
  linarith

end NextProof.Dual
