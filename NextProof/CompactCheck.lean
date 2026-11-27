import NextProof.CompactHalf
import NextProof.CompactPack

namespace NextProof.Compact
open NextProof.Tail

/-- Leaf and split parameters give a power-of-two rescaling and last retained degree. -/
inductive Plan
  | skip
  | leaf (shift degree : ℕ)
  | split (shift degree : ℕ) (lo hi : Plan)
  deriving Inhabited

def normalize (k d : ℕ) (v : List ℤ) : List ℤ :=
  truncate d (quotient (2^k) v)

private theorem normalize_pos {k d : ℕ} {w : List ℤ} {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1)
    (h : 0 ≤ horner x (normalize k d w)) : 0 ≤ horner x w := by
  have h' := h.trans (truncate_le d (quotient (2^k) w) x hx hx')
  exact (mul_nonneg (show 0 ≤ ((2^k:ℤ):ℝ) by positivity) h').trans
    (quotient_le (2^k) (by positivity) w x hx)

def exactRight (w : List ℤ) : Option (List ℤ) :=
  if w.isEmpty then some [] else
  let n := w.length
  let m : ℤ := 2^n*absSum w
  let stride := (m.natAbs.log2+n.log2+4)
  let radix : ℤ := 2^stride
  let a := Blocks.balanced (n.log2+2) w
  let z := fastHom 1 radix a
  let u := (a.decode stride z).list
  if m+absSum u < radix then some (quotient (2^n) u) else none

theorem exactRight_le {w u : List ℤ} (hh : exactRight w = some u)
    (x : ℝ) (hx : 0 ≤ x) : horner x u ≤ horner ((x+1)/2) w := by
  unfold exactRight at hh
  split at hh
  next e =>
    cases w with
    | nil => cases hh; rfl
    | cons _ _ => simp at e
  next e =>
    dsimp only at hh
    split at hh
    next hc =>
      cases hh
      apply rounded_right _ x hx
      apply hom_packed (B := (2 : ℤ)^((2^w.length*absSum w).natAbs.log2 + w.length.log2+4)) (by positivity)
      · simpa only [hom_bound_one,major_one] using hc
      · rw [← Blocks.subst_eq,Blocks.decode_subst]
        · simp only [fastHom_spec,Blocks.balanced_list]
        · rw [Blocks.size_eq, Blocks.balanced_list]
          cases w <;> simp_all
    next => contradiction

def check : Plan → ℚ → List ℤ → Bool
  | .skip,cut,_ => decide (1 < cut)
  | .leaf k d,_,w => decide (0 ≤ unitLower (normalize k d w))
  | .split k d lo hi,cut,w =>
    let v := normalize k d w
    match exactRight v with
    | none => false
    | some h => check lo (2*cut) (leftAux 1 v) && check hi (2*cut-1) h

theorem check_sound (p : Plan) (cut : ℚ) (w : List ℤ) (h : check p cut w = true)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hcut : (cut:ℝ) ≤ x) : 0 ≤ horner x w := by
  induction p generalizing cut w x with
  | skip =>
    have ht : 1 < cut := by simpa [check] using h
    have ht' : (1:ℝ) < cut := by exact_mod_cast ht
    linarith
  | leaf k d =>
    apply normalize_pos hx hx'
    have hl : 0 ≤ unitLower (normalize k d w) := by simpa [check] using h
    exact (show (0:ℝ) ≤ (unitLower (normalize k d w):ℝ) by exact_mod_cast hl).trans
      (unitLower_le _ hx hx')
  | split k d lo hi il ih =>
    let v := normalize k d w
    cases he : exactRight v with
    | none => simp [check, show exactRight (normalize k d w) = none from he] at h
    | some r =>
      change (match exactRight v with
        | none => false
        | some u => check lo (2*cut) (leftAux 1 v) && check hi (2*cut-1) u) = true at h
      rw [he] at h
      simp only [Bool.and_eq_true] at h
      have hs := h
      apply normalize_pos hx hx'
      by_cases hl : x ≤ 1/2
      · have h1 := il (2*cut) (leftAux 1 v) hs.1 (2*x) (by linarith) (by linarith) (by push_cast; linarith)
        have h2 := leftAux_le v 1 (by decide) (2*x) (by linarith)
        simpa using h1.trans (by simpa using h2 : horner (2*x) (leftAux 1 v) ≤ horner x v)
      · have h1 := ih (2*cut-1) r hs.2 (2*x-1) (by linarith) (by linarith) (by push_cast; linarith)
        have h2 := exactRight_le he (2*x-1) (by linarith)
        convert h1.trans h2 using 2; ring

end NextProof.Compact
