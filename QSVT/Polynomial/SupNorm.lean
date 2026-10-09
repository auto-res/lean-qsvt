/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Sup norm on `[-1, 1]` (formal-spec POLY-4)

`supNorm P = sSup {‖P(x)‖ | x ∈ [-1, 1]}` for `P : ℂ[X]`, evaluated at real points.

* Finiteness: the image is bounded (`bddAbove_image`) and the supremum is attained
  (`exists_eval_eq_supNorm`), by compactness of `[-1, 1]` and continuity of `P`.
* Characterisation: `norm_eval_le_supNorm`, `supNorm_le_of_forall`, `supNorm_le_iff`.
* Norm axioms: `supNorm_nonneg`, `supNorm_add_le`, `supNorm_C_mul`, `supNorm_neg`,
  `supNorm_mul_le`, `supNorm_zero`, `supNorm_one`, `supNorm_X`.
* Coefficient bound: `supNorm_le_sum_norm_coeff : supNorm P ≤ ∑ k ≤ deg P, ‖P.coeff k‖`.
  The sharper Chebyshev-basis bound is in `QSVT.Polynomial.Chebyshev`.
-/

namespace QSVT.Poly

open Polynomial

/-- POLY-4. The sup norm of `P` on the real interval `[-1, 1]`. -/
noncomputable def supNorm (P : ℂ[X]) : ℝ :=
  sSup ((fun x : ℝ => ‖P.eval (x : ℂ)‖) '' Set.Icc (-1) 1)

/-! ### Finiteness -/

theorem continuous_norm_eval (P : ℂ[X]) : Continuous fun x : ℝ => ‖P.eval (x : ℂ)‖ :=
  (P.continuous.comp Complex.continuous_ofReal).norm

theorem bddAbove_image (P : ℂ[X]) :
    BddAbove ((fun x : ℝ => ‖P.eval (x : ℂ)‖) '' Set.Icc (-1) 1) :=
  isCompact_Icc.bddAbove_image (continuous_norm_eval P).continuousOn

theorem nonempty_image (P : ℂ[X]) :
    ((fun x : ℝ => ‖P.eval (x : ℂ)‖) '' Set.Icc (-1) 1).Nonempty :=
  (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)).image _

/-- POLY-4. The sup norm is attained on `[-1, 1]`. -/
theorem exists_eval_eq_supNorm (P : ℂ[X]) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ = supNorm P := by
  have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  obtain ⟨x, hx, h⟩ :=
    isCompact_Icc.exists_sSup_image_eq hne (continuous_norm_eval P).continuousOn
  exact ⟨x, hx, h.symm⟩

/-! ### Characterisation -/

/-- POLY-4. `‖P(x)‖ ≤ supNorm P` for `x ∈ [-1, 1]`. -/
theorem norm_eval_le_supNorm (P : ℂ[X]) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖P.eval (x : ℂ)‖ ≤ supNorm P :=
  le_csSup (bddAbove_image P) ⟨x, hx, rfl⟩

/-- POLY-4. A pointwise bound on `[-1, 1]` bounds the sup norm. -/
theorem supNorm_le_of_forall {P : ℂ[X]} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ M) : supNorm P ≤ M :=
  csSup_le (nonempty_image P) (by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx)

theorem supNorm_le_iff {P : ℂ[X]} {M : ℝ} :
    supNorm P ≤ M ↔ ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ M :=
  ⟨fun h _ hx => (norm_eval_le_supNorm P hx).trans h, supNorm_le_of_forall⟩

theorem supNorm_nonneg (P : ℂ[X]) : 0 ≤ supNorm P :=
  (norm_nonneg _).trans (norm_eval_le_supNorm P (x := 0) ⟨by norm_num, by norm_num⟩)

/-! ### Norm axioms -/

@[simp]
theorem supNorm_zero : supNorm (0 : ℂ[X]) = 0 :=
  le_antisymm (supNorm_le_of_forall fun _ _ => by simp) (supNorm_nonneg 0)

@[simp]
theorem supNorm_one : supNorm (1 : ℂ[X]) = 1 :=
  le_antisymm (supNorm_le_of_forall fun _ _ => by simp)
    (by simpa using norm_eval_le_supNorm (1 : ℂ[X]) (x := 0) ⟨by norm_num, by norm_num⟩)

@[simp]
theorem supNorm_neg (P : ℂ[X]) : supNorm (-P) = supNorm P := by
  simp only [supNorm, eval_neg, norm_neg]

/-- POLY-4. Triangle inequality. -/
theorem supNorm_add_le (P Q : ℂ[X]) : supNorm (P + Q) ≤ supNorm P + supNorm Q :=
  supNorm_le_of_forall fun _ hx => by
    rw [eval_add]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_eval_le_supNorm P hx) (norm_eval_le_supNorm Q hx))

theorem supNorm_sub_le (P Q : ℂ[X]) : supNorm (P - Q) ≤ supNorm P + supNorm Q := by
  rw [sub_eq_add_neg, ← supNorm_neg Q]
  exact supNorm_add_le P (-Q)

theorem supNorm_mul_le (P Q : ℂ[X]) : supNorm (P * Q) ≤ supNorm P * supNorm Q :=
  supNorm_le_of_forall fun _ hx => by
    rw [eval_mul, norm_mul]
    exact mul_le_mul (norm_eval_le_supNorm P hx) (norm_eval_le_supNorm Q hx) (norm_nonneg _)
      (supNorm_nonneg P)

theorem supNorm_C_mul_le (c : ℂ) (P : ℂ[X]) : supNorm (C c * P) ≤ ‖c‖ * supNorm P :=
  supNorm_le_of_forall fun _ hx => by
    rw [eval_mul, eval_C, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_eval_le_supNorm P hx) (norm_nonneg c)

/-- POLY-4. Absolute homogeneity. -/
theorem supNorm_C_mul (c : ℂ) (P : ℂ[X]) : supNorm (C c * P) = ‖c‖ * supNorm P := by
  refine le_antisymm (supNorm_C_mul_le c P) ?_
  obtain ⟨x, hx, h⟩ := exists_eval_eq_supNorm P
  calc ‖c‖ * supNorm P = ‖(C c * P).eval (x : ℂ)‖ := by rw [← h, eval_mul, eval_C, norm_mul]
    _ ≤ supNorm (C c * P) := norm_eval_le_supNorm _ hx

theorem supNorm_smul (c : ℂ) (P : ℂ[X]) : supNorm (c • P) = ‖c‖ * supNorm P := by
  rw [smul_eq_C_mul, supNorm_C_mul]

@[simp]
theorem supNorm_C (c : ℂ) : supNorm (C c) = ‖c‖ := by
  simpa using supNorm_C_mul c 1

theorem supNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    supNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, supNorm (f i) :=
  supNorm_le_of_forall fun _ hx => by
    rw [eval_finsetSum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_eval_le_supNorm (f i) hx)

/-! ### Monomials and the coefficient bound -/

theorem norm_ofReal_le_one {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : ‖(x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr hx

theorem supNorm_X_pow_le_one (n : ℕ) : supNorm (X ^ n : ℂ[X]) ≤ 1 :=
  supNorm_le_of_forall fun _ hx => by
    rw [eval_pow, eval_X, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_ofReal_le_one hx)

@[simp]
theorem supNorm_X : supNorm (X : ℂ[X]) = 1 := by
  refine le_antisymm (by simpa using supNorm_X_pow_le_one 1) ?_
  simpa using norm_eval_le_supNorm (X : ℂ[X]) (x := 1) ⟨by norm_num, by norm_num⟩

/-- POLY-4. `‖P(x)‖ ≤ ∑ₖ ‖cₖ‖` on `[-1, 1]` (monomial basis). -/
theorem norm_eval_le_sum_norm_coeff (P : ℂ[X]) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖P.eval (x : ℂ)‖ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
  rw [eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_ofReal_le_one hx))

/-- POLY-4. `‖P‖_∞ ≤ ∑ₖ ‖cₖ‖` (monomial basis). -/
theorem supNorm_le_sum_norm_coeff (P : ℂ[X]) :
    supNorm P ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ :=
  supNorm_le_of_forall fun _ hx => norm_eval_le_sum_norm_coeff P hx

end QSVT.Poly
