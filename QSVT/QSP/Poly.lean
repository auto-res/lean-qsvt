/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Complex.Exponential
import QSVT.Polynomial.Parity

/-!
# QSP polynomials (formal-spec QSP-3, definitions)

The polynomials attached to a reflection-convention QSP phase sequence
`Φ = [φ₁, …, φ_d]` (GSLW Cor 8, R-convention recursion verified in
`dev/qsp-convention-check.md`):

* `qspPoly Φ = (P, Q)`: the two-polynomial recursion; `P` is the top-left entry of
  `seqR Φ x` and `Q` the *bottom-left* entry divided by `√(1-x²)`.
* `qspPoly4 Φ = (P, Qt, Qb, Pb)`: the four-polynomial recursion following all four
  entries of `seqR Φ x = [[P, Qt·s], [Qb·s, Pb]]`.  Used as the induction-friendly
  form; `(P, Qb)` coincides with `qspPoly Φ`.
* `conjP P = P.map conj` (coefficientwise complex conjugate, written `P^*` in GSLW),
  `negX P = P.comp (-X)` (so `(negX P).eval x = P.eval (-x)`).
* Parity (`QSVT.Poly.HasParity P n`) is defined in `QSVT.Polynomial.Parity`.

This module contains only definitions and unfolding lemmas.  The evaluation theorem
`seqR_eval` and its corollaries are in `QSVT.QSP.Structure`.
-/

open Polynomial

namespace QSVT.QSP

/-- The coefficientwise complex conjugate `P^*` of a polynomial. -/
noncomputable def conjP (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

/-- The reflection `P(X) ↦ P(-X)`. -/
noncomputable def negX (P : ℂ[X]) : ℂ[X] := P.comp (-X)

/-- QSP-3. The four-polynomial recursion `(P, Qt, Qb, Pb)` with
`seqR Φ x = [[P(x), Qt(x)·s], [Qb(x)·s, Pb(x)]]`, `s = √(1-x²)`:
base `(1, 0, 0, 1)` and, for `φ :: Φ` with `e = e^{iφ}`,
`P' = e (X P + (1-X²) Qb)`, `Qt' = e (X Qt + Pb)`, `Qb' = e⁻¹ (P - X Qb)`,
`Pb' = e⁻¹ ((1-X²) Qt - X Pb)`. -/
noncomputable def qspPoly4 : List ℝ → ℂ[X] × ℂ[X] × ℂ[X] × ℂ[X]
  | [] => (1, 0, 0, 1)
  | φ :: Φ =>
    let P := (qspPoly4 Φ).1
    let Qt := (qspPoly4 Φ).2.1
    let Qb := (qspPoly4 Φ).2.2.1
    let Pb := (qspPoly4 Φ).2.2.2
    let e := Complex.exp (Complex.I * φ)
    let e' := Complex.exp (-(Complex.I * φ))
    (C e * (X * P + (1 - X ^ 2) * Qb), C e * (X * Qt + Pb),
      C e' * (P - X * Qb), C e' * ((1 - X ^ 2) * Qt - X * Pb))

/-- QSP-3. The QSP polynomials `(P, Q)` of a phase list in the reflection convention
(GSLW Cor 8): `seqR Φ x = [[P(x), Q^*(-x)·s], [Q(x)·s, P^*(-x)]]` with `s = √(1-x²)`.
Base `(1, 0)`; for `φ :: Φ` with `e = e^{iφ}`: `P' = e (X P + (1-X²) Q)`, `Q' = e⁻¹ (P - X Q)`. -/
noncomputable def qspPoly : List ℝ → ℂ[X] × ℂ[X]
  | [] => (1, 0)
  | φ :: Φ =>
    (C (Complex.exp (Complex.I * φ)) * (X * (qspPoly Φ).1 + (1 - X ^ 2) * (qspPoly Φ).2),
      C (Complex.exp (-(Complex.I * φ))) * ((qspPoly Φ).1 - X * (qspPoly Φ).2))

/-! ### Unfolding lemmas -/

@[simp]
theorem qspPoly4_nil : qspPoly4 [] = (1, 0, 0, 1) := rfl

theorem qspPoly4_cons (φ : ℝ) (Φ : List ℝ) :
    qspPoly4 (φ :: Φ) =
      (C (Complex.exp (Complex.I * φ)) *
          (X * (qspPoly4 Φ).1 + (1 - X ^ 2) * (qspPoly4 Φ).2.2.1),
        C (Complex.exp (Complex.I * φ)) * (X * (qspPoly4 Φ).2.1 + (qspPoly4 Φ).2.2.2),
        C (Complex.exp (-(Complex.I * φ))) * ((qspPoly4 Φ).1 - X * (qspPoly4 Φ).2.2.1),
        C (Complex.exp (-(Complex.I * φ))) *
          ((1 - X ^ 2) * (qspPoly4 Φ).2.1 - X * (qspPoly4 Φ).2.2.2)) := rfl

@[simp]
theorem qspPoly_nil : qspPoly [] = (1, 0) := rfl

theorem qspPoly_cons (φ : ℝ) (Φ : List ℝ) :
    qspPoly (φ :: Φ) =
      (C (Complex.exp (Complex.I * φ)) * (X * (qspPoly Φ).1 + (1 - X ^ 2) * (qspPoly Φ).2),
        C (Complex.exp (-(Complex.I * φ))) * ((qspPoly Φ).1 - X * (qspPoly Φ).2)) := rfl

/-! ### `conjP` and `negX` -/

@[simp] theorem conjP_add (P Q : ℂ[X]) : conjP (P + Q) = conjP P + conjP Q :=
  Polynomial.map_add _

@[simp] theorem conjP_sub (P Q : ℂ[X]) : conjP (P - Q) = conjP P - conjP Q :=
  Polynomial.map_sub _

@[simp] theorem conjP_mul (P Q : ℂ[X]) : conjP (P * Q) = conjP P * conjP Q :=
  Polynomial.map_mul _

@[simp] theorem conjP_pow (P : ℂ[X]) (n : ℕ) : conjP (P ^ n) = conjP P ^ n :=
  Polynomial.map_pow _ _

@[simp] theorem conjP_C (a : ℂ) : conjP (C a) = C ((starRingEnd ℂ) a) :=
  Polynomial.map_C _

@[simp] theorem conjP_X : conjP X = X :=
  Polynomial.map_X _

@[simp] theorem conjP_one : conjP 1 = 1 :=
  Polynomial.map_one _

@[simp] theorem conjP_zero : conjP 0 = 0 :=
  Polynomial.map_zero _

@[simp] theorem conjP_neg (P : ℂ[X]) : conjP (-P) = -conjP P :=
  Polynomial.map_neg _

/-- Conjugation is an involution. -/
@[simp] theorem conjP_conjP (P : ℂ[X]) : conjP (conjP P) = P := by
  unfold conjP
  rw [Polynomial.map_map]
  convert Polynomial.map_id using 2
  ext z
  exact Complex.conj_conj z

theorem eval_conjP (P : ℂ[X]) (z : ℂ) :
    (conjP P).eval z = (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
  rw [conjP, Polynomial.eval_map]
  conv_lhs => rw [← Complex.conj_conj z]
  exact Polynomial.eval₂_hom _ _

theorem eval_conjP_ofReal (P : ℂ[X]) (x : ℝ) :
    (conjP P).eval (x : ℂ) = (starRingEnd ℂ) (P.eval (x : ℂ)) := by
  rw [eval_conjP, Complex.conj_ofReal]

@[simp] theorem negX_add (P Q : ℂ[X]) : negX (P + Q) = negX P + negX Q :=
  Polynomial.add_comp

@[simp] theorem negX_sub (P Q : ℂ[X]) : negX (P - Q) = negX P - negX Q :=
  Polynomial.sub_comp

@[simp] theorem negX_mul (P Q : ℂ[X]) : negX (P * Q) = negX P * negX Q :=
  Polynomial.mul_comp _ _ _

@[simp] theorem negX_pow (P : ℂ[X]) (n : ℕ) : negX (P ^ n) = negX P ^ n :=
  Polynomial.pow_comp _ _ _

@[simp] theorem negX_C (a : ℂ) : negX (C a) = C a :=
  Polynomial.C_comp

@[simp] theorem negX_X : negX X = -X :=
  Polynomial.X_comp

@[simp] theorem negX_one : negX 1 = 1 :=
  Polynomial.one_comp

@[simp] theorem negX_zero : negX 0 = 0 :=
  Polynomial.zero_comp

@[simp] theorem eval_negX (P : ℂ[X]) (z : ℂ) : (negX P).eval z = P.eval (-z) := by
  rw [negX, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]

/-- `conjP` and `negX` commute. -/
theorem conjP_negX (P : ℂ[X]) : conjP (negX P) = negX (conjP P) := by
  unfold conjP negX
  rw [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]

/-! ### Conjugating the phase factors -/

theorem conj_exp_I_mul (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem conj_exp_neg_I_mul (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
    neg_neg]

end QSVT.QSP
