/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import QSVT.QSP.Conventions
import QSVT.QSP.Poly

/-!
# QSP structure theorem (formal-spec QSP-3)

The evaluation theorem for the reflection-convention QSP sequence (GSLW Cor 8):
for `x ∈ [-1, 1]`, `s = √(1-x²)` and `(P, Q) = qspPoly Φ`,

  `seqR Φ x = [[P(x), Q^*(-x)·s], [Q(x)·s, P^*(-x)]]`.

* `seqR_eval4` : the four-polynomial version (clean induction, no conjugation).
* `seqR_eval`  : the headline statement via `qspPoly`, `conjP`, `negX`.
* Corollaries: degree bounds (`natDegree_fst_le`, `natDegree_snd_le`), parity
  (`hasParity_fst`, `hasParity_snd`), the unit identity
  `|P(x)|² + (1-x²)|Q(x)|² = 1` (`norm_identity`), and the effect of negating all
  phases (`qspPoly_neg`).
-/

open Polynomial

namespace QSVT.QSP

open Matrix Complex

/-! ### One step of the sequence on a matrix of the shape `[[a, b s], [c s, d]]` -/

/-- The square root `s = √(1-x²)` satisfies `s² = 1 - x²` in `ℂ` for `x ∈ [-1, 1]`. -/
theorem ofReal_sqrt_mul_self {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) = 1 - (x : ℂ) ^ 2 := by
  have h : (0 : ℝ) ≤ 1 - x ^ 2 := by
    obtain ⟨h₁, h₂⟩ := hx
    nlinarith
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
  push_cast
  ring

/-- One QSP step `e^{iφσ_z} R(x)` applied to a matrix `[[a, b s], [c s, d]]`, `s = √(1-x²)`. -/
theorem phaseZ_mul_Rref_mul {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) (a b c d : ℂ) :
    phaseZ φ * Rref x *
        !![a, b * (Real.sqrt (1 - x ^ 2) : ℂ); c * (Real.sqrt (1 - x ^ 2) : ℂ), d] =
      !![Complex.exp (Complex.I * φ) * (x * a + (1 - (x : ℂ) ^ 2) * c),
          Complex.exp (Complex.I * φ) * (x * b + d) * (Real.sqrt (1 - x ^ 2) : ℂ);
        Complex.exp (-(Complex.I * φ)) * (a - x * c) * (Real.sqrt (1 - x ^ 2) : ℂ),
          Complex.exp (-(Complex.I * φ)) * ((1 - (x : ℂ) ^ 2) * b - x * d)] := by
  have hs := ofReal_sqrt_mul_self hx
  simp only [phaseZ, Rref, Matrix.mul_fin_two, zero_mul, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero]
    linear_combination (Complex.exp (Complex.I * φ) * c) * hs
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination (Complex.exp (-(Complex.I * φ)) * b) * hs

/-! ### The four-polynomial evaluation theorem -/

/-- QSP-3 (four-polynomial form). For `x ∈ [-1, 1]`, `s = √(1-x²)` and
`(P, Qt, Qb, Pb) = qspPoly4 Φ`, `seqR Φ x = [[P(x), Qt(x)·s], [Qb(x)·s, Pb(x)]]`. -/
theorem seqR_eval4 {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ Φ : List ℝ, seqR Φ x =
      !![(qspPoly4 Φ).1.eval (x : ℂ), (qspPoly4 Φ).2.1.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
        (qspPoly4 Φ).2.2.1.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (qspPoly4 Φ).2.2.2.eval (x : ℂ)]
  | [] => by
    rw [seqR_nil, qspPoly4_nil]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | φ :: Φ => by
    rw [seqR_cons, seqR_eval4 hx Φ, phaseZ_mul_Rref_mul hx, qspPoly4_cons]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_pow, eval_one]

/-! ### Relating the four- and two-polynomial recursions -/

/-- The first components of `qspPoly4` and `qspPoly` agree, and the bottom-left polynomial
of `qspPoly4` is the second component of `qspPoly`. -/
theorem qspPoly4_fst_and_Qb :
    ∀ Φ : List ℝ, (qspPoly4 Φ).1 = (qspPoly Φ).1 ∧ (qspPoly4 Φ).2.2.1 = (qspPoly Φ).2
  | [] => by simp
  | φ :: Φ => by
    obtain ⟨h₁, h₂⟩ := qspPoly4_fst_and_Qb Φ
    rw [qspPoly4_cons, qspPoly_cons]
    simp only [h₁, h₂, and_self]

theorem qspPoly4_fst (Φ : List ℝ) : (qspPoly4 Φ).1 = (qspPoly Φ).1 :=
  (qspPoly4_fst_and_Qb Φ).1

theorem qspPoly4_Qb (Φ : List ℝ) : (qspPoly4 Φ).2.2.1 = (qspPoly Φ).2 :=
  (qspPoly4_fst_and_Qb Φ).2

/-- The right column of `seqR` is determined by the left one: `Qt = Qb^*(-X)` and
`Pb = P^*(-X)`. -/
theorem qspPoly4_Qt_and_Pb :
    ∀ Φ : List ℝ, (qspPoly4 Φ).2.1 = negX (conjP (qspPoly4 Φ).2.2.1) ∧
      (qspPoly4 Φ).2.2.2 = negX (conjP (qspPoly4 Φ).1)
  | [] => by simp
  | φ :: Φ => by
    obtain ⟨h₁, h₂⟩ := qspPoly4_Qt_and_Pb Φ
    rw [qspPoly4_cons]
    simp only [conjP_mul, conjP_C, conjP_sub, conjP_add, conjP_X, conjP_one, conjP_pow,
      negX_mul, negX_C, negX_sub, negX_add, negX_X, negX_one, negX_pow,
      conj_exp_I_mul, conj_exp_neg_I_mul]
    rw [h₁, h₂]
    constructor <;> ring

theorem qspPoly4_Qt (Φ : List ℝ) : (qspPoly4 Φ).2.1 = negX (conjP (qspPoly Φ).2) := by
  rw [(qspPoly4_Qt_and_Pb Φ).1, qspPoly4_Qb]

theorem qspPoly4_Pb (Φ : List ℝ) : (qspPoly4 Φ).2.2.2 = negX (conjP (qspPoly Φ).1) := by
  rw [(qspPoly4_Qt_and_Pb Φ).2, qspPoly4_fst]

/-! ### The evaluation theorem -/

/-- QSP-3. Evaluation theorem (GSLW Cor 8, reflection convention). For `x ∈ [-1, 1]`,
`s = √(1-x²)` and `(P, Q) = qspPoly Φ`,
`seqR Φ x = [[P(x), Q^*(-x)·s], [Q(x)·s, P^*(-x)]]`, where `P^* = conjP P` is the
coefficientwise conjugate. -/
theorem seqR_eval {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    seqR Φ x =
      !![(qspPoly Φ).1.eval (x : ℂ),
          (conjP (qspPoly Φ).2).eval (-(x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ);
        (qspPoly Φ).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (conjP (qspPoly Φ).1).eval (-(x : ℂ))] := by
  rw [seqR_eval4 hx Φ, qspPoly4_fst, qspPoly4_Qb, qspPoly4_Qt, qspPoly4_Pb, eval_negX, eval_negX]

/-- The top-left entry of `seqR Φ x` is `P(x)`. -/
theorem seqR_apply_zero_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    seqR Φ x 0 0 = (qspPoly Φ).1.eval (x : ℂ) := by
  rw [seqR_eval hx Φ]
  simp

/-- The bottom-left entry of `seqR Φ x` is `Q(x) √(1-x²)`. -/
theorem seqR_apply_one_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    seqR Φ x 1 0 = (qspPoly Φ).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ) := by
  rw [seqR_eval hx Φ]
  simp

/-! ### Corollary (i): degree bounds -/

/-- Degree bounds in the induction-friendly form `deg P ≤ d`, `deg (X Q) ≤ d`. -/
theorem natDegree_aux :
    ∀ Φ : List ℝ, (qspPoly Φ).1.natDegree ≤ Φ.length ∧
      (X * (qspPoly Φ).2).natDegree ≤ Φ.length
  | [] => by simp
  | φ :: Φ => by
    obtain ⟨hP, hXQ⟩ := natDegree_aux Φ
    have h1X2 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by compute_degree
    have hX : (X : ℂ[X]).natDegree ≤ 1 := natDegree_X_le
    rw [qspPoly_cons, List.length_cons]
    dsimp only
    constructor
    · refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
      · exact natDegree_mul_le.trans (by omega)
      · rcases eq_or_ne (qspPoly Φ).2 0 with hQ | hQ
        · rw [hQ, mul_zero, natDegree_zero]
          exact Nat.zero_le _
        · rw [natDegree_X_mul hQ] at hXQ
          exact natDegree_mul_le.trans (by omega)
    · have h₁ : ((qspPoly Φ).1 - X * (qspPoly Φ).2).natDegree ≤ Φ.length :=
        (natDegree_sub_le _ _).trans (max_le hP hXQ)
      have h₂ := natDegree_C_mul_le (Complex.exp (-(Complex.I * φ)))
        ((qspPoly Φ).1 - X * (qspPoly Φ).2)
      exact natDegree_mul_le.trans (by omega)

/-- QSP-3 (i). `deg P ≤ d` for `(P, Q) = qspPoly Φ`, `d = Φ.length`. -/
theorem natDegree_fst_le (Φ : List ℝ) : (qspPoly Φ).1.natDegree ≤ Φ.length :=
  (natDegree_aux Φ).1

/-- QSP-3 (i). `deg Q ≤ d - 1` for `(P, Q) = qspPoly Φ`, `d = Φ.length` (and `Q = 0` if `d = 0`). -/
theorem natDegree_snd_le (Φ : List ℝ) : (qspPoly Φ).2.natDegree ≤ Φ.length - 1 := by
  rcases eq_or_ne (qspPoly Φ).2 0 with hQ | hQ
  · rw [hQ, natDegree_zero]
    exact Nat.zero_le _
  · have h := (natDegree_aux Φ).2
    rw [natDegree_X_mul hQ] at h
    omega

/-! ### Corollary (ii): parity -/

open QSVT.Poly in
/-- Parity in the induction-friendly form: `d` even gives `(P, Q)` (even, odd), `d` odd gives
(odd, even). -/
theorem parity_aux :
    ∀ Φ : List ℝ, (Even Φ.length → IsEven (qspPoly Φ).1 ∧ IsOdd (qspPoly Φ).2) ∧
      (Odd Φ.length → IsOdd (qspPoly Φ).1 ∧ IsEven (qspPoly Φ).2)
  | [] => ⟨fun _ => ⟨isEven_one, isOdd_zero⟩, fun h => absurd h (by decide)⟩
  | φ :: Φ => by
    obtain ⟨he, ho⟩ := parity_aux Φ
    rw [qspPoly_cons, List.length_cons]
    constructor
    · intro h
      obtain ⟨hP, hQ⟩ := ho (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h))
      exact ⟨(hP.X_mul.add hQ.one_sub_X_sq_mul).C_mul _, (hP.sub hQ.X_mul).C_mul _⟩
    · intro h
      obtain ⟨hP, hQ⟩ := he (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h))
      exact ⟨(hP.X_mul.add hQ.one_sub_X_sq_mul).C_mul _, (hP.sub hQ.X_mul).C_mul _⟩

/-- QSP-3 (ii). `P` has the parity of `d = Φ.length`. -/
theorem hasParity_fst (Φ : List ℝ) : QSVT.Poly.HasParity (qspPoly Φ).1 Φ.length :=
  ⟨fun h => ((parity_aux Φ).1 h).1, fun h => ((parity_aux Φ).2 h).1⟩

/-- QSP-3 (ii). `Q` has the parity of `d - 1`, `d = Φ.length` (for `d = 0`, `Q = 0`). -/
theorem hasParity_snd (Φ : List ℝ) : QSVT.Poly.HasParity (qspPoly Φ).2 (Φ.length - 1) := by
  rcases Φ with _ | ⟨φ, Φ⟩
  · exact ⟨fun _ => QSVT.Poly.isEven_zero, fun h => absurd h (by decide)⟩
  · rw [List.length_cons, Nat.add_sub_cancel]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact ((parity_aux (φ :: Φ)).2
        (by rw [List.length_cons]; exact Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr h))).2
    · exact ((parity_aux (φ :: Φ)).1
        (by rw [List.length_cons]; exact Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h))).2

/-! ### Corollary (iii): the unit identity -/

/-- QSP-3 (iii). `|P(x)|² + (1-x²)|Q(x)|² = 1` for `x ∈ [-1, 1]`, from unitarity of `seqR`
(`normSq` form). -/
theorem normSq_identity {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    Complex.normSq ((qspPoly Φ).1.eval (x : ℂ)) +
      (1 - x ^ 2) * Complex.normSq ((qspPoly Φ).2.eval (x : ℂ)) = 1 := by
  have hU := Matrix.mem_unitaryGroup_iff'.mp (seqR_mem_unitaryGroup hx Φ)
  have h00 := congrFun (congrFun hU 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, seqR_eval hx Φ] at h00
  simp only [Matrix.star_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.one_apply_eq, Complex.star_def, map_mul,
    Complex.conj_ofReal] at h00
  have hs := ofReal_sqrt_mul_self hx
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  linear_combination h00 -
    ((starRingEnd ℂ) ((qspPoly Φ).2.eval (x : ℂ)) * (qspPoly Φ).2.eval (x : ℂ)) * hs

/-- QSP-3 (iii). `‖P(x)‖² + (1-x²)‖Q(x)‖² = 1` for `x ∈ [-1, 1]`. -/
theorem norm_identity {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    ‖(qspPoly Φ).1.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖(qspPoly Φ).2.eval (x : ℂ)‖ ^ 2 = 1 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  exact normSq_identity hx Φ

/-! ### Corollary (iv): negated phases -/

/-- QSP-3 (iv). Negating all phases conjugates the polynomials:
`qspPoly (-Φ) = (P^*, Q^*)` (used for GSLW Cor 18 / SVT-8). -/
theorem qspPoly_neg :
    ∀ Φ : List ℝ, qspPoly (Φ.map Neg.neg) = (conjP (qspPoly Φ).1, conjP (qspPoly Φ).2)
  | [] => by simp
  | φ :: Φ => by
    rw [List.map_cons, qspPoly_cons, qspPoly_cons, qspPoly_neg Φ]
    simp only [conjP_mul, conjP_C, conjP_add, conjP_sub, conjP_X, conjP_one, conjP_pow,
      conj_exp_I_mul, conj_exp_neg_I_mul, Complex.ofReal_neg, mul_neg, neg_neg]

end QSVT.QSP
