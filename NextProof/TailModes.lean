import NextProof.TailKernel

namespace NextProof.Tail
open Polynomial
open scoped FourierTransform

/-- All mode weights have one common positive denominator. -/
noncomputable def series (j : ℕ) : List ℤ → ℚ[X]
  | [] => 0
  | a::as => C (a : ℚ) * laguerreHalf (2*j) + series (j+1) as

theorem series_fourier (j : ℕ) (as : List ℤ) :
    𝓕 (radialGaussian (series j as)) = radialGaussian (series j as) := by
  induction as generalizing j with
  | nil =>
    simpa [series] using fourier_evenLaguerre_sum (∅ : Finset ℕ) (fun _ => (0 : ℚ)) id
  | cons a as ih =>
    rw [series, radialGaussian_add, fourier_add (integrable_radialGaussian _) (integrable_radialGaussian _),
      ih, radialGaussian_C_mul, fourier_const_mul, fourier_laguerreHalf, pow_mul]
    simp

def fac (n : ℕ) : ℕ := 2^n * n.factorial

private lemma fac_s (n : ℕ) : fac (n+1) = 2*(n+1)*fac n := by
  simp [fac, pow_succ, Nat.factorial_succ]
  ring

/-- One division-free step for H_n=2^n n! L_n. -/
def next {R : Type*} [CommRing R] (n : ℕ) (x u v : R) : R :=
  ((4*n+5 : ℕ) - 2*x)*v - ((2*(n+1)*(2*n+1) : ℕ) : R)*u

noncomputable def mode (n : ℕ) : ℚ[X] := (fac n : ℚ[X]) * laguerreHalf n

theorem mode_next (n : ℕ) :
    mode (n+2) = next n X (mode n) (mode (n+1)) := by
  have h := laguerreHalf_recurrence n
  simp only [map_add, map_mul, C_ofNat, map_natCast] at h
  simp only [mode, next, fac_s, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have h₁ : C (5 / 2 : ℚ) * 2 = 5 := by rw [← C_ofNat 2, ← map_mul, show (5/2 : ℚ)*2 = 5 by norm_num, C_ofNat]
  have h₂ : C (1 / 2 : ℚ) * 2 = 1 := by rw [← C_ofNat, ← map_mul]; norm_num
  linear_combination (4 * ((n : ℚ[X])+1) * (fac n : ℚ[X])) * h +
    (2*((n : ℚ[X])+1)*(fac n : ℚ[X])*laguerreHalf (n+1))*h₁ -
    (2*((n : ℚ[X])+1)*(fac n : ℚ[X])*laguerreHalf n)*h₂

/-- Carry the two current modes and the accumulated sum at the same integral scale. -/
def run {R : Type*} [CommRing R] (x : R) : List ℤ → ℕ → R → R → R → R
  | [], _, _, _, acc => acc
  | w::ws, n, u, v, acc =>
    let y := next n x u v
    run x ws (n+2) y (next (n+1) x v y)
      (((4*(n+1)*(n+2) : ℕ) : R)*(acc+w*u))

theorem run_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R)
    (ws : List ℤ) (n : ℕ) (u v a : R) :
    f (run x ws n u v a) = run (f x) ws n (f u) (f v) (f a) := by
  induction ws generalizing n u v a with
  | nil => rfl
  | cons w ws ih => simp only [run, ih, next, map_sub, map_mul, map_add, map_natCast, map_ofNat, map_intCast]

theorem run_modes (ws : List ℤ) (j : ℕ) (p : ℚ[X]) :
    run X ws (2*j) (mode (2*j)) (mode (2*j+1)) ((fac (2*j) : ℚ[X])*p) =
      (fac (2*(j+ws.length)) : ℚ[X]) * (p + series j ws) := by
  induction ws generalizing j p with
  | nil => simp [series, run]
  | cons w ws ih =>
    rw [run, ← mode_next, ← mode_next]
    have hs : 4*(2*j+1)*(2*j+2)*fac (2*j) = fac (2*j+2) := by
      rw [fac_s, fac_s]; ring
    have he : ((4 * (2*j+1)*(2*j+2) : ℕ) : ℚ[X]) *
        ((fac (2*j) : ℚ[X])*p+w*mode (2*j)) =
        (fac (2*j+2) : ℚ[X]) * (p+C (w : ℚ)*laguerreHalf (2*j)) := by
      rw [← hs, mode, C_eq_intCast]; push_cast; ring
    rw [he, show 2*j+2=2*(j+1) by omega, show 2*j+1+2 = 2*(j+1)+1 by omega, ih]
    simp only [series, List.length_cons]
    rw [show j+1+ws.length=j+(ws.length+1) by omega, add_assoc]

def weightBound (ws : List ℤ) (n : ℕ) (u v a : ℤ) : ℤ :=
  match ws with
  | [] => a
  | w::rest =>
    let y := ((4*n+7 : ℕ) : ℤ)*v + ((2*(n+1)*(2*n+1) : ℕ) : ℤ)*u
    let z := ((4*(n+1)+7 : ℕ) : ℤ)*y + ((2*(n+2)*(2*(n+1)+1) : ℕ) : ℤ)*v
    weightBound rest (n+2) y z (((4*(n+1)*(n+2) : ℕ) : ℤ)*(a + |w| * u))

private theorem bound_next (n : ℕ) {p q : ℤ[X]} {u v : ℤ}
    (hp : Bounded p u) (hq : Bounded q v) : Bounded (next n X p q)
      (((4*n+7 : ℕ) : ℤ)*v + ((2*(n+1)*(2*n+1) : ℕ) : ℤ)*u) := by
  let k : ℕ := 2*(n+1)*(2*n+1)
  have hb := bound_add (bound_add (bound_smul ((4*n+5 : ℕ) : ℤ) hq)
    (bound_smul (-2) (bound_X hq))) (bound_smul (-(k : ℤ)) hp)
  simp only [map_neg, map_natCast, C_ofNat, abs_neg, abs_of_nonneg (Int.natCast_nonneg _),
    abs_of_nonneg (by decide : (0:ℤ) ≤ 2)] at hb
  convert hb using 1
  · unfold next k; push_cast; ring
  · dsimp [k]; ring

theorem bound_run (ws : List ℤ) (n : ℕ) {p q r : ℤ[X]} {u v a : ℤ}
    (hp : Bounded p u) (hq : Bounded q v) (hr : Bounded r a) :
    Bounded (run X ws n p q r) (weightBound ws n u v a) := by
  induction ws generalizing n p q r u v a with
  | nil => exact hr
  | cons w ws ih =>
    apply ih _ (bound_next _ hp hq) (bound_next _ hq (bound_next _ hp hq))
    have hw : C w = (w : ℤ[X]) := by simpa only [Int.cast_id] using (C_eq_intCast (R := ℤ) w)
    simpa only [map_natCast, hw, abs_of_nonneg (Int.natCast_nonneg _)] using bound_smul (((4*(n+1)*(n+2) : ℕ) : ℤ)) (bound_add hr (bound_smul w hp))

noncomputable def intSeries (ws : List ℤ) : ℤ[X] := run X ws 0 1 (1-2*X) 0

theorem intSeries_map (ws : List ℤ) : (intSeries ws).map (Int.castRingHom ℚ) =
    (fac (2*ws.length) : ℚ[X]) * series 0 ws := by
  have h := run_map (mapRingHom (Int.castRingHom ℚ)) X ws 0 1 (1-2*X) 0
  have g := run_modes ws 0 0
  simp only [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_ofNat, map_X, Polynomial.map_zero] at h
  rw [intSeries, h]
  have hm0 : mode 0 = 1 := by simp [mode,fac]
  have hc : (2 : ℚ[X])*C (1/2 : ℚ) = 1 := by rw [← C_ofNat, ← map_mul]; norm_num
  have hm1 : mode 1 = 1-2*X := by
    rw [mode, laguerreHalf_one, show fac 1 = 2 by decide, Nat.cast_ofNat, mul_sub, hc]
  simpa only [Nat.mul_zero, zero_add, mul_zero, hm0, hm1] using g

theorem bind_packed (ws coeff : List ℤ) (B : ℤ)
    (hB : 0 < B) (hs : weightBound ws 0 1 3 0 + major 1 coeff < B)
    (hv : run B ws 0 1 (1-2*B) 0 = horner B coeff) :
    intSeries ws = horner (X : ℤ[X]) coeff := by
  apply packed_eq (m := weightBound ws 0 1 3 0) (n := major 1 coeff)
  · apply bound_run
    · simpa only [map_one, abs_one] using bound_const (1 : ℤ)
    · have h := bound_add (bound_const (1 : ℤ)) (bound_smul (-2) (bound_X (bound_const (1 : ℤ))))
      norm_num [sub_eq_add_neg] at h ⊢
      exact h
    · intro i; simp
  · simpa using horner_bound 0 coeff
  · exact hB
  · exact hs
  · rw [intSeries, horner_eval]
    have h := run_map (evalRingHom B) X ws 0 1 (1-2*X) 0
    simp only [map_one, map_zero, map_sub, map_mul, map_ofNat, coe_evalRingHom, eval_X] at h
    simpa only [eval_X] using h.trans hv

theorem eval_witness_binding (ws : List ℤ) (D : ℕ) (hD : 0 < D) (p : List ℤ)
    (h : intSeries ws = horner (X : ℤ[X]) p) (x : ℝ) :
    horner x p = ((fac (2*ws.length) : ℝ)*(D : ℝ))*
      (C (1/(D : ℚ))*series 0 ws).eval₂ (algebraMap ℚ ℝ) x := by
  have m := intSeries_map ws
  rw [h] at m
  have hm := congrArg (fun g : ℚ[X] => g.eval₂ (algebraMap ℚ ℝ) x) m
  simp only [eval₂_map, eval₂_mul, eval₂_natCast] at hm
  change (horner (X : ℤ[X]) p).eval₂ (Int.castRingHom ℝ) x = _ at hm
  rw [horner_real, eval₂_X] at hm
  rw [hm, eval₂_mul, eval₂_C]
  simp only [map_div₀, map_one, map_natCast]
  field_simp

end NextProof.Tail
