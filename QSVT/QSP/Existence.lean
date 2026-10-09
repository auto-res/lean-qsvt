/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import QSVT.QSP.Conversion
import QSVT.QSP.PolyW

/-!
# Existence of QSP phases (formal-spec QSP-7c, GSLW Theorem 3 "⇐")

Given polynomials `P, Q ∈ ℂ[X]` with (i) `deg P ≤ k`, `deg Q ≤ k - 1`, (ii) parity `P ≡ k`,
`Q ≡ k - 1 (mod 2)`, and (iii) the polynomial identity `P P^* + (1 - X²) Q Q^* = 1`
(equivalent to `|P(x)|² + (1 - x²)|Q(x)|² = 1` on `[-1, 1]`), there are phases `φ₀` and
`Φ = [φ₁, …, φ_k]` with `qspPolyW φ₀ Φ = (P, Q)`, i.e. by `seqW_eval`
`e^{iφ₀σ_z} ∏_j W(x) e^{iφ_jσ_z} = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]` (`exists_phases`).

The proof is GSLW's degree-lowering induction (eqs. (6)–(8)), by induction on `k`:

* `k = 0`: `P` is a unimodular constant `e^{iφ₀}` and `Q = 0`.
* `k = n + 1`: comparing the `X^{2n+2}` coefficient of (iii) gives
  `|p_{n+1}| = |q_n|` for the top coefficients `p_{n+1} = P.coeff (n+1)`, `q_n = Q.coeff n`
  (`coeff_top_mul_conj_eq`), so there is `φ` with `e^{-iφ} p_{n+1} = e^{iφ} q_n`
  (`exists_phase_coeff`; `φ = arg (p_{n+1}/q_n) / 2`, or `φ = 0` if both vanish).  The inverse
  step `unstepW φ (P, Q) = (e^{-iφ} X P + e^{iφ}(1 - X²) Q, e^{iφ} X Q - e^{-iφ} P)` satisfies
  `stepW φ (unstepW φ (P, Q)) = (P, Q)` for every `φ` (`stepW_unstepW`), preserves (iii)
  (`unstepW_unit`) and shifts the parities (`unstepW_fst_hasParity`, `unstepW_snd_hasParity`);
  the chosen `φ` kills the top coefficients and parity kills the next ones, so the new pair
  satisfies (i) for `n` (`natDegree_le_pred`).  The induction hypothesis gives `(φ₀, Φ̃)` and
  `Φ = Φ̃ ++ [φ]` works by `qspPolyW_concat`.

Note that no separate treatment of `deg P < k` is needed: if `p_{n+1} = 0` then `q_n = 0`
and `φ = 0` lowers `k` while keeping (i)–(iii), so the induction is on `k`, not on `deg P`.

`exists_phases_R` transports the result to the reflection convention through GSLW Cor 8
(`seqW_apply_zero_zero_eq`): for `k ≥ 1` there is `Φ` of length `k` with
`(seqR Φ x) 0 0 = P(x)` on `[-1, 1]`.

## Mathlib facts used

`Polynomial.coeff_mul_add_eq_of_natDegree_le`, `Polynomial.natDegree_le_pred`,
`Polynomial.eq_C_of_natDegree_le_zero`, `Complex.norm_eq_one_iff` (`‖z‖ = 1 ↔ ∃ θ, exp (θ I) = z`),
`Complex.mul_conj'`, `Complex.normSq_eq_zero`, `sq_eq_sq₀`.
-/

open Polynomial

namespace QSVT.QSP

open Complex QSVT.Poly

/-! ### The inverse step (GSLW eqs. (7)–(8)) -/

/-- QSP-7. The inverse of `stepW φ` (GSLW eqs. (7)–(8)):
`(P, Q) ↦ (e^{-iφ} X P + e^{iφ} (1 - X²) Q, e^{iφ} X Q - e^{-iφ} P)`.  For every `φ`,
`stepW φ (unstepW φ (P, Q)) = (P, Q)` (`stepW_unstepW`). -/
noncomputable def unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (-(Complex.I * φ))) * (X * PQ.1) +
      C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * PQ.2),
    C (Complex.exp (Complex.I * φ)) * (X * PQ.2) - C (Complex.exp (-(Complex.I * φ))) * PQ.1)

theorem unstepW_fst (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 =
      C (Complex.exp (-(Complex.I * φ))) * (X * P) +
        C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * Q) := rfl

theorem unstepW_snd (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).2 =
      C (Complex.exp (Complex.I * φ)) * (X * Q) - C (Complex.exp (-(Complex.I * φ))) * P := rfl

/-- QSP-7. `stepW φ ∘ unstepW φ = id` (uses only `e^{iφ} e^{-iφ} = 1`, i.e. `x² + (1 - x²) = 1`
after expanding). -/
theorem stepW_unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : stepW φ (unstepW φ PQ) = PQ := by
  have h := C_exp_mul_C_exp_neg φ
  obtain ⟨P, Q⟩ := PQ
  simp only [stepW, unstepW, Prod.mk.injEq]
  constructor
  · linear_combination P * h
  · linear_combination Q * h

/-- QSP-7. `unstepW φ` preserves `P P^* + (1 - X²) Q Q^*`. -/
theorem unstepW_unit (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 =
      P * conjP P + (1 - X ^ 2) * Q * conjP Q := by
  have h := C_exp_mul_C_exp_neg φ
  rw [unstepW_fst, unstepW_snd]
  simp only [conjP_mul, conjP_C, conjP_add, conjP_sub, conjP_X, conjP_pow, conjP_one,
    conj_exp_I_mul, conj_exp_neg_I_mul]
  linear_combination (P * conjP P + (1 - X ^ 2) * Q * conjP Q) * h

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the first component of `unstepW φ (P, Q)` has parity `n`. -/
theorem unstepW_fst_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).1 n := by
  rw [unstepW_fst]
  exact (hP.X_mul.of_add_two.C_mul _).add (hQ.one_sub_X_sq_mul.C_mul _)

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the second component of `unstepW φ (P, Q)` has parity
`n + 1`. -/
theorem unstepW_snd_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).2 (n + 1) := by
  rw [unstepW_snd]
  exact (hQ.X_mul.C_mul _).sub (hP.C_mul _)

/-- Crude degree bound for the first component of `unstepW`. -/
theorem natDegree_unstepW_fst_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 := by
  have h1X2 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by compute_degree
  rw [unstepW_fst]
  refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans ?_)
  · exact (natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega)
  · exact (natDegree_mul_le_of_le h1X2 hQ).trans (by omega)

/-- Crude degree bound for the second component of `unstepW`. -/
theorem natDegree_unstepW_snd_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 := by
  rw [unstepW_snd]
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans hP))
  exact (natDegree_mul_le_of_le natDegree_X_le hQ).trans (by omega)

/-- The top coefficient of the first component of `unstepW φ (P, Q)` for `deg Q ≤ n`:
`e^{-iφ} p_{n+1} - e^{iφ} q_n`. -/
theorem coeff_unstepW_fst {P Q : ℂ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (φ : ℝ) :
    (unstepW φ (P, Q)).1.coeff (n + 1 + 1) =
      Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) -
        Complex.exp (Complex.I * φ) * Q.coeff n := by
  rw [unstepW_fst, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, sub_mul, one_mul, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n + 1 + 1),
    show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul]
  ring

/-- The top coefficient of the second component of `unstepW φ (P, Q)`:
`e^{iφ} q_n - e^{-iφ} p_{n+1}`. -/
theorem coeff_unstepW_snd (P Q : ℂ[X]) (n : ℕ) (φ : ℝ) :
    (unstepW φ (P, Q)).2.coeff (n + 1) =
      Complex.exp (Complex.I * φ) * Q.coeff n -
        Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) := by
  rw [unstepW_snd, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-! ### The top coefficients -/

/-- QSP-7. The `X^{2n+2}` coefficient of `P P^* + (1 - X²) Q Q^* = 1` for `deg P ≤ n + 1`,
`deg Q ≤ n`: `p_{n+1} p̄_{n+1} = q_n q̄_n`. -/
theorem coeff_top_mul_conj_eq {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    P.coeff (n + 1) * (starRingEnd ℂ) (P.coeff (n + 1)) =
      Q.coeff n * (starRingEnd ℂ) (Q.coeff n) := by
  have h := congrArg (fun R : ℂ[X] => R.coeff (n + 1 + (n + 1))) hunit
  have hQQ : (Q * conjP Q).natDegree ≤ n + n :=
    natDegree_mul_le_of_le hQ ((natDegree_conjP_le Q).trans hQ)
  have h0 : (Q * conjP Q).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : (1 : ℂ[X]).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_one]; omega)
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hP ((natDegree_conjP_le P).trans hP),
    coeff_conjP, show (1 - X ^ 2) * Q * conjP Q = Q * conjP Q - X ^ 2 * (Q * conjP Q) by ring,
    coeff_sub, h0, h1, show n + 1 + (n + 1) = n + n + 2 by ring, coeff_X_pow_mul,
    coeff_mul_add_eq_of_natDegree_le hQ ((natDegree_conjP_le Q).trans hQ), coeff_conjP] at h
  linear_combination h

/-- QSP-7. Given `p p̄ = q q̄`, there is a phase `φ` with `e^{-iφ} p = e^{iφ} q`
(`φ = arg (p / q) / 2` if `q ≠ 0`, else `φ = 0`). -/
theorem exists_phase_coeff {p q : ℂ} (h : p * (starRingEnd ℂ) p = q * (starRingEnd ℂ) q) :
    ∃ φ : ℝ, Complex.exp (-(Complex.I * φ)) * p = Complex.exp (Complex.I * φ) * q := by
  by_cases hq : q = 0
  · refine ⟨0, ?_⟩
    have hp : p = 0 := by
      rw [hq, zero_mul, Complex.mul_conj] at h
      exact Complex.normSq_eq_zero.mp (by exact_mod_cast h)
    rw [hp, hq, mul_zero, mul_zero]
  · have hnorm : ‖p / q‖ = 1 := by
      rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hq)]
      rw [Complex.mul_conj', Complex.mul_conj'] at h
      exact (sq_eq_sq₀ (norm_nonneg p) (norm_nonneg q)).mp (by exact_mod_cast h)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (p / q)).mp hnorm
    refine ⟨θ / 2, ?_⟩
    have hp : p = p / q * q := (div_mul_cancel₀ p hq).symm
    have hee : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) = p / q := by
      rw [← Complex.exp_add, ← hθ]
      congr 1
      push_cast
      ring
    have h1 := exp_I_mul_mul_exp_neg (θ / 2)
    linear_combination Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * hp -
      (Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * q) * hee +
      (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) * q) * h1

/-! ### The existence theorem -/

/-- QSP-7c. Existence of QSP phases (GSLW Theorem 3, "⇐", rotation convention).  If
(i) `deg P ≤ k`, `deg Q ≤ k - 1` (with `Q = 0` for `k = 0`), (ii) `P` has parity `k` and `Q`
parity `k - 1`, and (iii) `P P^* + (1 - X²) Q Q^* = 1`, then there are `φ₀ : ℝ` and
`Φ : List ℝ` of length `k` with `qspPolyW φ₀ Φ = (P, Q)`; by `seqW_eval`,
`seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]` on `[-1, 1]`. -/
theorem exists_phases (k : ℕ) (P Q : ℂ[X]) (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ k - 1)
    (hQ0 : k = 0 → Q = 0) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧ qspPolyW φ₀ Φ = (P, Q) := by
  induction k generalizing P Q with
  | zero =>
    obtain rfl := hQ0 rfl
    rw [eq_C_of_natDegree_le_zero hP] at hunit ⊢
    have hc : P.coeff 0 * (starRingEnd ℂ) (P.coeff 0) = 1 := by
      rw [conjP_C, conjP_zero, mul_zero, add_zero, ← C_mul, ← C_1, C_inj] at hunit
      exact hunit
    have hnorm : ‖P.coeff 0‖ = 1 := by
      rw [Complex.mul_conj'] at hc
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [one_pow]; exact_mod_cast hc)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).mp hnorm
    exact ⟨θ, [], rfl, by rw [qspPolyW_nil, ← hθ, mul_comm]⟩
  | succ n ih =>
    rw [Nat.add_sub_cancel] at hQ hQpar
    obtain ⟨φ, hφ⟩ := exists_phase_coeff (coeff_top_mul_conj_eq hP hQ hunit)
    -- the lowered pair `(P̃, Q̃) = unstepW φ (P, Q)`
    have hPpar' : HasParity (unstepW φ (P, Q)).1 n := unstepW_fst_hasParity hPpar hQpar φ
    have hQpar' : HasParity (unstepW φ (P, Q)).2 (n + 1) := unstepW_snd_hasParity hPpar hQpar φ
    have hP' : (unstepW φ (P, Q)).1.natDegree ≤ n := by
      have h2 : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_fst_le hP hQ φ)
          (by rw [coeff_unstepW_fst hQ]; linear_combination hφ)
      rw [Nat.add_sub_cancel] at h2
      have h1 := natDegree_le_pred h2 (hPpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩)
      rwa [Nat.add_sub_cancel] at h1
    have hQn : (unstepW φ (P, Q)).2.coeff n = 0 :=
      hQpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩
    have hQ'' : (unstepW φ (P, Q)).2.natDegree ≤ n := by
      have h1 : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_snd_le hP hQ φ)
          (by rw [coeff_unstepW_snd]; linear_combination -hφ)
      rwa [Nat.add_sub_cancel] at h1
    have hQ' : (unstepW φ (P, Q)).2.natDegree ≤ n - 1 := natDegree_le_pred hQ'' hQn
    have hQ0' : n = 0 → (unstepW φ (P, Q)).2 = 0 := by
      rintro rfl
      rw [eq_C_of_natDegree_le_zero hQ'', hQn, C_0]
    have hQpar'' : HasParity (unstepW φ (P, Q)).2 (n - 1) := by
      rcases n with _ | m
      · rw [hQ0' rfl]
        exact hasParity_zero _
      · rw [Nat.add_sub_cancel]
        exact hQpar'.of_add_two
    have hunit' : (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 = 1 := by
      rw [unstepW_unit, hunit]
    obtain ⟨φ₀, Φ, hlen, hΦ⟩ := ih _ _ hP' hQ' hQ0' hPpar' hQpar'' hunit'
    refine ⟨φ₀, Φ ++ [φ], by rw [List.length_append, List.length_singleton, hlen], ?_⟩
    rw [qspPolyW_concat, hΦ]
    exact stepW_unstepW φ (P, Q)

/-! ### The reflection convention (GSLW Cor 8) -/

/-- QSP-7c, reflection convention (via GSLW Cor 8, `seqW_apply_zero_zero_eq`).  For `k ≥ 1` and
`(P, Q)` satisfying (i)–(iii) of `exists_phases`, there is a reflection-convention phase list
`Φ` of length `k` with `(seqR Φ x) 0 0 = P(x)` for all `x ∈ [-1, 1]`. -/
theorem exists_phases_R (k : ℕ) (hk : 1 ≤ k) (P Q : ℂ[X]) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k - 1) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ Φ : List ℝ, Φ.length = k ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, (seqR Φ x) 0 0 = P.eval (x : ℂ) := by
  obtain ⟨φ₀, Φ', hlen, hΦ'⟩ :=
    exists_phases k P Q hP hQ (fun h => absurd h (by omega)) hPpar hQpar hunit
  have hne : Φ' ≠ [] := by
    rintro rfl
    rw [List.length_nil] at hlen
    omega
  refine ⟨cor8Phases φ₀ Φ' hne, by rw [cor8Phases_length, hlen], fun x hx => ?_⟩
  rw [← seqW_apply_zero_zero_eq, seqW_apply_zero_zero hx, hΦ']

end QSVT.QSP
