import NextProof.LowerTree
import NextProof.TailPacked

namespace NextProof.Compact
open NextProof.Tail Polynomial

def leftAux (d : ℤ) : List ℤ → List ℤ
  | [] => []
  | a::as => (a/d)::leftAux (2*d) as

theorem leftAux_le (w : List ℤ) (d : ℤ) (hd : 0 < d) (x : ℝ) (hx : 0 ≤ x) :
    (d : ℝ)*horner x (leftAux d w) ≤ horner (x/2) w := by
  induction w generalizing d with
  | nil => simp [leftAux,horner]
  | cons a as ih =>
    have h : d*(a/d) ≤ a := by
      have := Int.emod_nonneg a (ne_of_gt hd)
      linarith [Int.emod_add_mul_ediv a d]
    have h' : (d : ℝ)*(↑(a/d) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    have hu := ih (2*d) (by omega)
    push_cast at hu
    simp only [leftAux,horner]
    nlinarith only [h', mul_le_mul_of_nonneg_left hu hx]

theorem half_eval_real (p s : ℤ[X]) (w : List ℤ) (x : ℝ) :
    (halfForm p s w).eval₂ (Int.castRingHom ℝ) x =
    halfForm (p.eval₂ (Int.castRingHom ℝ) x) (s.eval₂ (Int.castRingHom ℝ) x) w := by
  induction w with
  | nil => simp [halfForm]
  | cons a as ih => simp only [halfForm,eval₂_add,eval₂_mul,eval₂_pow,← C_eq_intCast,eval₂_C,eval₂_ofNat,ih]; rfl

theorem half_eval_int (p s : ℤ[X]) (w : List ℤ) (x : ℤ) :
    (halfForm p s w).eval x = halfForm (p.eval x) (s.eval x) w := by
  induction w with
  | nil => simp [halfForm]
  | cons a as ih => simp [halfForm,ih]

def homBound (s : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::as => |a| * 2^(as.length+1)+(|s| + 1)*homBound s as

theorem hom_bound (s : ℤ) (w : List ℤ) :
    Bounded (halfForm X (C s) w) (homBound s w) := by
  induction w with
  | nil => intro i; simp [halfForm,homBound]
  | cons a as ih =>
    have h := bound_add (bound_const (a*2^(as.length+1)))
      (bound_add (bound_X ih) (bound_smul s ih))
    simp only [halfForm,homBound]
    convert h using 1
    · simp only [map_mul,map_pow,C_ofNat,add_mul, ← C_eq_intCast,Int.cast_id]
    · rw [abs_mul,abs_pow,abs_of_nonneg (by decide : (0:ℤ) ≤ 2)]
      ring

theorem half_append (s x : ℤ) (a b : List ℤ) :
    halfForm x s (a++b) =
      2^b.length*halfForm x s a+(x+s)^a.length*halfForm x s b := by
  induction a with
  | nil => simp [halfForm]
  | cons k a ih =>
    simp only [List.cons_append,List.length_append,List.length_cons,halfForm,ih,pow_succ,pow_add]
    ring

/-- Balanced evaluation of 2^n p((x+s)/2) over the integers. -/
def fastHom (s x : ℤ) : Blocks → ℤ
  | .empty => 0
  | .leaf a => 2*a
  | .join a b => 2^b.size*fastHom s x a+(x+s)^a.size*fastHom s x b

theorem fastHom_spec (s x : ℤ) (a : Blocks) : fastHom s x a = halfForm x s a.list := by
  induction a with
  | empty => rfl
  | leaf a => simp [fastHom,Blocks.list,halfForm];ring
  | join a b ha hb => simp [fastHom,Blocks.list,half_append,Blocks.size_eq,ha,hb]

/-- Compare the exact shifted polynomial with the decoded signed digits. -/
theorem hom_packed {w u : List ℤ} {s B : ℤ} (hB : 0 < B)
    (hm : homBound s w + major 1 u < B)
    (hv : halfForm B s w = horner B u) :
    halfForm (X : ℤ[X]) (C s) w = horner X u := by
  apply packed_eq (hom_bound s w) (by simpa using horner_bound 0 u) hB hm
  simpa only [half_eval_int,eval_X,eval_C,horner_eval] using hv

theorem rounded_right {w u : List ℤ}
    (h : halfForm (X : ℤ[X]) (C 1) w = horner X u)
    (x : ℝ) (hx : 0 ≤ x) :
    horner x (quotient (2^w.length) u) ≤ horner ((x+1)/2) w := by
  have he := congrArg (fun p : ℤ[X] => p.eval₂ (Int.castRingHom ℝ) x) h
  simp only [half_eval_real,eval₂_X,eval₂_C,
    horner_real,half_value] at he
  have hc := quotient_le (2^w.length) (by positivity) u x hx
  push_cast at hc
  rw [← he] at hc
  exact le_of_mul_le_mul_left hc (by positivity)

theorem hom_bound_one (w : List ℤ) : homBound 1 w = 2^w.length*absSum w := by
  induction w with
  | nil => simp [homBound,absSum]
  | cons a as ih => simp only [homBound,absSum,List.length_cons,ih,pow_succ,abs_one]; ring

theorem major_one (w : List ℤ) : major 1 w = absSum w := by
  induction w with
  | nil => rfl
  | cons a as ih => simp only [major,absSum,one_mul,ih]

end NextProof.Compact
