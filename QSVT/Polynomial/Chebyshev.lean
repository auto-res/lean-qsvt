/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import QSVT.Polynomial.Parity
import QSVT.Polynomial.SupNorm

/-!
# Chebyshev polynomials and Chebyshev series (formal-spec POLY-5, POLY-6)

Mathlib's `Polynomial.Chebyshev.T : ℤ → R[X]` is indexed by `ℤ`; we only use `n : ℕ`
(coerced).  POLY-5 re-exports the facts the QSVT development relies on with `ℕ` indices:

* `T_eval_cos`, `T_eval_ofReal_cos`, `T_eval_real_cos` : `T_n(cos θ) = cos (n θ)`;
* `norm_eval_T_le_one`, `supNorm_T` : `|T_n(x)| ≤ 1` on `[-1, 1]` (and `‖T_n‖_∞ = 1`);
* `natDegree_T`, `T_parity`, `T_natCast_add_two`, `two_mul_X_mul_T`.

POLY-6: a Chebyshev series `ChebSeries` is a finitely supported coefficient sequence
`c : ℕ →₀ ℂ`; `c.toPoly = ∑ cₖ Tₖ`, `c.l1 = ∑ ‖cₖ‖`, and
`supNorm_toPoly_le_l1 : ‖∑ cₖ Tₖ‖_∞ ≤ ∑ ‖cₖ‖`.  This is the bound used by the exact
Chebyshev LCU route and the certificate checker (`‖∑ cₖ Tₖ − f‖ ≤ ∑ |cₖ − fₖ|`).

TODO (POLY-6, `chebCoeff`): the monomial → Chebyshev change of basis `ChebSeries.ofPoly`
with `(ofPoly P).toPoly = P` is not needed yet and is left for a later wave.
-/

namespace QSVT.Poly

open Polynomial Polynomial.Chebyshev

/-! ### POLY-5: Chebyshev polynomials of the first kind, `ℕ`-indexed -/

/-- POLY-5. `T_n(cos θ) = cos (n θ)` over `ℂ` (Mathlib `T_complex_cos`). -/
theorem T_eval_cos (θ : ℂ) (n : ℕ) : (T ℂ n).eval (Complex.cos θ) = Complex.cos (n * θ) := by
  rw [T_complex_cos, Int.cast_natCast]

/-- POLY-5. `T_n(cos θ) = cos (n θ)` over `ℝ` (Mathlib `T_real_cos`). -/
theorem T_eval_real_cos (θ : ℝ) (n : ℕ) : (T ℝ n).eval (Real.cos θ) = Real.cos (n * θ) := by
  rw [T_real_cos, Int.cast_natCast]

/-- POLY-5. `T_n(cos θ) = cos (n θ)` for the complex polynomial at a real point. -/
theorem T_eval_ofReal_cos (θ : ℝ) (n : ℕ) :
    (T ℂ n).eval ((Real.cos θ : ℝ) : ℂ) = ((Real.cos (n * θ) : ℝ) : ℂ) := by
  rw [← complex_ofReal_eval_T, T_eval_real_cos]

/-- POLY-5. `|T_n(x)| ≤ 1` for `x ∈ [-1, 1]` (Mathlib `abs_eval_T_real_le_one`). -/
theorem norm_eval_T_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(T ℂ n).eval (x : ℂ)‖ ≤ 1 := by
  rw [← complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs]
  exact abs_eval_T_real_le_one n (abs_le.mpr hx)

theorem supNorm_T_le_one (n : ℕ) : supNorm (T ℂ n) ≤ 1 :=
  supNorm_le_of_forall fun _ hx => norm_eval_T_le_one n hx

/-- POLY-5. `‖T_n‖_∞ = 1` (attained at `x = 1`). -/
@[simp]
theorem supNorm_T (n : ℕ) : supNorm (T ℂ n) = 1 := by
  refine le_antisymm (supNorm_T_le_one n) ?_
  simpa [T_eval_one] using norm_eval_le_supNorm (T ℂ n) (x := 1) ⟨by norm_num, by norm_num⟩

/-- POLY-5. `deg T_n = n`. -/
@[simp]
theorem natDegree_T (n : ℕ) : (T ℂ n).natDegree = n := by
  rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]

/-- POLY-5. The recurrence `T_{n+2} = 2 X T_{n+1} - T_n` with `ℕ` indices. -/
theorem T_natCast_add_two (n : ℕ) :
    T ℂ ((n + 2 : ℕ) : ℤ) = 2 * X * T ℂ ((n + 1 : ℕ) : ℤ) - T ℂ (n : ℤ) := by
  push_cast
  exact T_add_two ℂ n

/-- POLY-5. `2 x T_{n+1} = T_{n+2} + T_n`. -/
theorem two_mul_X_mul_T (n : ℕ) :
    2 * X * T ℂ ((n + 1 : ℕ) : ℤ) = T ℂ ((n + 2 : ℕ) : ℤ) + T ℂ (n : ℤ) := by
  rw [T_natCast_add_two]
  ring

/-- POLY-5. `T_n` has the parity of `n`. -/
theorem T_parity (n : ℕ) : HasParity (T ℂ n) n := by
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · rw [Nat.cast_zero, T_zero]
    exact hasParity_one
  · rw [Nat.cast_one, T_one]
    exact hasParity_X
  · intro m ih0 ih1
    have h2 : (2 : ℂ[X]) * X * T ℂ ((m + 1 : ℕ) : ℤ) = C 2 * (X * T ℂ ((m + 1 : ℕ) : ℤ)) := by
      rw [C_ofNat]
      ring
    rw [T_natCast_add_two, h2]
    exact (ih1.X_mul.C_mul 2).sub ih0.add_two

/-! ### POLY-6: Chebyshev series -/

/-- POLY-6. A finitely supported Chebyshev coefficient sequence `(cₖ)`, representing
`∑ₖ cₖ Tₖ`. -/
structure ChebSeries where
  /-- The coefficient of `Tₖ`. -/
  coeff : ℕ →₀ ℂ

namespace ChebSeries

/-- POLY-6. The polynomial `∑ₖ cₖ Tₖ`. -/
noncomputable def toPoly (c : ChebSeries) : ℂ[X] :=
  c.coeff.sum fun k a => C a * T ℂ k

/-- POLY-6. The `ℓ¹` norm `∑ₖ ‖cₖ‖` of the coefficients. -/
noncomputable def l1 (c : ChebSeries) : ℝ :=
  c.coeff.sum fun _ a => ‖a‖

/-- The series with the single term `a Tₖ`. -/
noncomputable def single (k : ℕ) (a : ℂ) : ChebSeries := ⟨Finsupp.single k a⟩

instance : Zero ChebSeries := ⟨⟨0⟩⟩

noncomputable instance : Add ChebSeries := ⟨fun c d => ⟨c.coeff + d.coeff⟩⟩

@[simp] theorem coeff_zero : (0 : ChebSeries).coeff = 0 := rfl

@[simp] theorem coeff_add (c d : ChebSeries) : (c + d).coeff = c.coeff + d.coeff := rfl

@[simp] theorem coeff_single (k : ℕ) (a : ℂ) : (single k a).coeff = Finsupp.single k a := rfl

theorem toPoly_eq_sum (c : ChebSeries) :
    c.toPoly = ∑ k ∈ c.coeff.support, C (c.coeff k) * T ℂ k := rfl

theorem l1_eq_sum (c : ChebSeries) : c.l1 = ∑ k ∈ c.coeff.support, ‖c.coeff k‖ := rfl

@[simp] theorem toPoly_zero : (0 : ChebSeries).toPoly = 0 := Finsupp.sum_zero_index

@[simp] theorem l1_zero : (0 : ChebSeries).l1 = 0 := Finsupp.sum_zero_index

@[simp]
theorem toPoly_single (k : ℕ) (a : ℂ) : (single k a).toPoly = C a * T ℂ k :=
  Finsupp.sum_single_index (by simp)

@[simp]
theorem l1_single (k : ℕ) (a : ℂ) : (single k a).l1 = ‖a‖ :=
  Finsupp.sum_single_index norm_zero

theorem toPoly_add (c d : ChebSeries) : (c + d).toPoly = c.toPoly + d.toPoly :=
  Finsupp.sum_add_index' (fun _ => by simp) fun _ _ _ => by rw [C_add, add_mul]

theorem l1_nonneg (c : ChebSeries) : 0 ≤ c.l1 :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- POLY-6. The `ℓ¹` norm is subadditive. -/
theorem l1_add_le (c d : ChebSeries) : (c + d).l1 ≤ c.l1 + d.l1 := by
  have hs : (c.coeff + d.coeff).support ⊆ c.coeff.support ∪ d.coeff.support :=
    Finsupp.support_add
  rw [l1, l1, l1, coeff_add, Finsupp.sum_of_support_subset _ hs _ fun _ _ => norm_zero,
    Finsupp.sum_of_support_subset _ Finset.subset_union_left _ fun _ _ => norm_zero,
    Finsupp.sum_of_support_subset _ Finset.subset_union_right _ fun _ _ => norm_zero,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by
    rw [Finsupp.add_apply]
    exact norm_add_le _ _

/-- POLY-6. `(∑ₖ cₖ Tₖ)(x) = ∑ₖ cₖ Tₖ(x)`. -/
theorem eval_toPoly (c : ChebSeries) (x : ℂ) :
    c.toPoly.eval x = c.coeff.sum fun k a => a * (T ℂ k).eval x := by
  simp only [toPoly, Finsupp.sum, eval_finsetSum, eval_mul, eval_C]

/-- POLY-6. `‖∑ₖ cₖ Tₖ(x)‖ ≤ ∑ₖ ‖cₖ‖` for `x ∈ [-1, 1]`. -/
theorem norm_eval_toPoly_le (c : ChebSeries) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖c.toPoly.eval (x : ℂ)‖ ≤ c.l1 := by
  rw [eval_toPoly, l1]
  simp only [Finsupp.sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_le_one k hx)

/-- POLY-6. `‖∑ₖ cₖ Tₖ‖_∞ ≤ ∑ₖ ‖cₖ‖`. -/
theorem supNorm_toPoly_le_l1 (c : ChebSeries) : supNorm c.toPoly ≤ c.l1 :=
  supNorm_le_of_forall fun _ hx => norm_eval_toPoly_le c hx

/-- POLY-6. `deg (∑ₖ cₖ Tₖ) ≤ max {k | cₖ ≠ 0}`. -/
theorem natDegree_toPoly_le (c : ChebSeries) : c.toPoly.natDegree ≤ c.coeff.support.sup id := by
  rw [toPoly_eq_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact (natDegree_C_mul_le _ _).trans ((natDegree_T k).le.trans (Finset.le_sup (f := id) hk))

end ChebSeries

end QSVT.Poly
