/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Polynomial.SqrtPart
import QSVT.Polynomial.SupNorm
import QSVT.Polynomial.Chebyshev

/-!
# QSVTTest.Polynomial

Regression tests for the polynomial layer (formal-spec POLY-3, POLY-4, POLY-5, POLY-6):
concrete `evenRoot`/`oddRoot` computations, sup-norm bounds, Chebyshev facts with `ℕ`
indices, and the axiom audit of the main theorems.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open Polynomial Polynomial.Chebyshev QSVT.Poly

/-! ### POLY-3: `evenRoot` / `oddRoot` -/

/-- `evenRoot (X⁴ + 2X² + 1) = X² + 2X + 1`. -/
example : evenRoot (X ^ 4 + 2 * X ^ 2 + 1 : ℂ[X]) = X ^ 2 + 2 * X + 1 := by
  rw [← evenRoot_comp_X_sq (X ^ 2 + 2 * X + 1)]
  congr 1
  simp only [add_comp, mul_comp, pow_comp, X_comp, one_comp, ofNat_comp]
  ring

/-- `oddRoot (X³ + X) = X + 1`. -/
example : oddRoot (X ^ 3 + X : ℂ[X]) = X + 1 := by
  rw [← oddRoot_X_mul_comp_X_sq (X + 1)]
  congr 1
  simp only [add_comp, X_comp, one_comp]
  ring

example : IsEven ((X ^ 2 + 2 * X + 1 : ℂ[X]).comp (X ^ 2)) := isEven_comp_X_sq _

example : IsOdd (X * (X + 1 : ℂ[X]).comp (X ^ 2)) := isOdd_X_mul_comp_X_sq _

/-- The representation theorem, evaluated. -/
example {P : ℂ[X]} (h : IsEven P) (x : ℂ) : P.eval x = (evenRoot P).eval (x ^ 2) :=
  h.eval_eq x

example (P : ℂ[X]) : (oddRoot P).natDegree ≤ P.natDegree / 2 := natDegree_oddRoot_le P

/-! ### POLY-4: sup norm -/

example : supNorm (X ^ 3 : ℂ[X]) ≤ 1 := supNorm_X_pow_le_one 3

example : supNorm (C 2 * X : ℂ[X]) = 2 := by
  rw [supNorm_C_mul, supNorm_X, mul_one]
  simp

example (P : ℂ[X]) :
    supNorm P ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ :=
  supNorm_le_sum_norm_coeff P

example (P Q : ℂ[X]) : supNorm (P - Q) ≤ supNorm P + supNorm Q := supNorm_sub_le P Q

/-! ### POLY-5 / POLY-6: Chebyshev -/

example : (T ℂ 2).natDegree = 2 := natDegree_T 2

example : HasParity (T ℂ 3) 3 := T_parity 3

example : IsOdd (T ℂ 3) := (T_parity 3).isOdd ⟨1, rfl⟩

example : IsEven (T ℂ 4) := (T_parity 4).isEven ⟨2, rfl⟩

example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : ‖(T ℂ 5).eval (x : ℂ)‖ ≤ 1 :=
  norm_eval_T_le_one 5 hx

example (θ : ℝ) : (T ℂ 3).eval ((Real.cos θ : ℝ) : ℂ) = ((Real.cos (3 * θ) : ℝ) : ℂ) := by
  exact_mod_cast T_eval_ofReal_cos θ 3

/-- `(a T₀ + b T₂)` as a polynomial. -/
example (a b : ℂ) :
    (ChebSeries.single 0 a + ChebSeries.single 2 b).toPoly = C a * T ℂ 0 + C b * T ℂ 2 := by
  rw [ChebSeries.toPoly_add, ChebSeries.toPoly_single, ChebSeries.toPoly_single]
  simp only [Nat.cast_zero, Nat.cast_ofNat]

/-- A two-term series `a T₀ + b T₂` has sup norm at most `‖a‖ + ‖b‖`. -/
example (a b : ℂ) :
    supNorm (ChebSeries.single 0 a + ChebSeries.single 2 b).toPoly ≤ ‖a‖ + ‖b‖ :=
  (ChebSeries.supNorm_toPoly_le_l1 _).trans
    (by simpa using ChebSeries.l1_add_le (ChebSeries.single 0 a) (ChebSeries.single 2 b))

/-! ### Axiom audit -/

/-- info: 'QSVT.Poly.IsEven.eq_evenRoot_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.IsEven.eq_evenRoot_comp

/-- info: 'QSVT.Poly.IsOdd.eq_X_mul_oddRoot_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.IsOdd.eq_X_mul_oddRoot_comp

/-- info: 'QSVT.Poly.supNorm_le_sum_norm_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.supNorm_le_sum_norm_coeff

/-- info: 'QSVT.Poly.norm_eval_T_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.norm_eval_T_le_one

/-- info: 'QSVT.Poly.T_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.T_parity

/-- info: 'QSVT.Poly.ChebSeries.supNorm_toPoly_le_l1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.ChebSeries.supNorm_toPoly_le_l1
