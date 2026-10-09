/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Existence

/-!
# QSVTTest.Existence

Sanity checks for the rotation-convention QSP polynomials (QSP-3W, `qspPolyW`, `seqW_eval`) and
the existence theorem (QSP-7c, `exists_phases`, `exists_phases_R`) in degree `k ≤ 1`, plus axiom
audits of the main theorems.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open Polynomial QSVT.QSP QSVT.Poly

/-! ### The recursion in degree `k ≤ 1` -/

/-- `qspPolyW φ₀ [] = (e^{iφ₀}, 0)`. -/
example (φ₀ : ℝ) : qspPolyW φ₀ [] = (C (Complex.exp (Complex.I * φ₀)), 0) := qspPolyW_nil φ₀

/-- `qspPolyW φ₀ [φ] = (e^{iφ₀} e^{iφ} X, e^{iφ₀} e^{-iφ})`. -/
example (φ₀ φ : ℝ) :
    qspPolyW φ₀ [φ] =
      (C (Complex.exp (Complex.I * φ₀) * Complex.exp (Complex.I * φ)) * X,
        C (Complex.exp (Complex.I * φ₀) * Complex.exp (-(Complex.I * φ)))) := by
  rw [show [φ] = [] ++ [φ] from rfl, qspPolyW_concat', qspPolyW_nil]
  simp only [mul_zero, add_zero, zero_add, C_mul, Prod.mk.injEq]
  constructor <;> ring

/-- The evaluation theorem specialised to the empty list (statement-level check). -/
example (φ₀ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqW φ₀ [] x =
      !![(qspPolyW φ₀ []).1.eval (x : ℂ),
          Complex.I * (qspPolyW φ₀ []).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
        Complex.I * (conjP (qspPolyW φ₀ []).2).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (conjP (qspPolyW φ₀ []).1).eval (x : ℂ)] :=
  seqW_eval hx φ₀ []

/-- The inverse step undoes a step for any phase (`unstepW` is a right inverse of `stepW`). -/
example (φ : ℝ) (P Q : ℂ[X]) : stepW φ (unstepW φ (P, Q)) = (P, Q) := stepW_unstepW φ (P, Q)

/-! ### Existence, `k = 1` -/

/-- `k = 1`: `P = c X`, `Q = c̄` with `|c| = 1` satisfy (i)–(iii) and are realised by one phase. -/
example (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = 1 ∧ qspPolyW φ₀ Φ = (C c * X, C ((starRingEnd ℂ) c)) := by
  have hcc : (C c : ℂ[X]) * C ((starRingEnd ℂ) c) = 1 := by
    rw [← C_mul, Complex.mul_conj', hc, Complex.ofReal_one, one_pow, C_1]
  refine exists_phases 1 (C c * X) (C ((starRingEnd ℂ) c))
    ((natDegree_C_mul_le c X).trans natDegree_X_le) (natDegree_C _).le
    (fun h => absurd h one_ne_zero) (hasParity_X.C_mul c) (hasParity_C _) ?_
  simp only [conjP_mul, conjP_C, conjP_X, Complex.conj_conj]
  linear_combination hcc

/-- `k = 1`, reflection convention: a phase list of length one realises `P = c X`. -/
example (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ Φ : List ℝ, Φ.length = 1 ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, (seqR Φ x) 0 0 = (C c * X).eval (x : ℂ) := by
  have hcc : (C c : ℂ[X]) * C ((starRingEnd ℂ) c) = 1 := by
    rw [← C_mul, Complex.mul_conj', hc, Complex.ofReal_one, one_pow, C_1]
  refine exists_phases_R 1 le_rfl (C c * X) (C ((starRingEnd ℂ) c))
    ((natDegree_C_mul_le c X).trans natDegree_X_le) (natDegree_C _).le
    (hasParity_X.C_mul c) (hasParity_C _) ?_
  simp only [conjP_mul, conjP_C, conjP_X, Complex.conj_conj]
  linear_combination hcc

/-! ### Axiom audit -/

/-- info: 'QSVT.QSP.seqW_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqW_eval

/-- info: 'QSVT.QSP.qspPolyW_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.qspPolyW_unit

/-- info: 'QSVT.QSP.exists_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.exists_phases

/-- info: 'QSVT.QSP.exists_phases_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.exists_phases_R
