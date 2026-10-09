/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import QSVT.QSP.Structure

/-!
# QSP polynomials in the rotation convention (formal-spec QSP-3W, QSP-7)

The polynomials attached to a rotation-convention QSP sequence (GSLW Thm 3)
`seqW φ₀ Φ x = e^{iφ₀σ_z} ∏_{j=1}^{k} W(x) e^{iφ_jσ_z}`, `Φ = [φ₁, …, φ_k]`:

* `stepW φ (P, Q)`: one rotation step on the polynomial pair (GSLW eq. (4)),
  `P' = e^{iφ} (X P + (X² - 1) Q)`, `Q' = e^{-iφ} (X Q + P)`;
* `qspPolyW φ₀ Φ`: the fold of `stepW` over `Φ` starting from `(e^{iφ₀}, 0)`.  The phases act
  on the right, matching `seqW φ₀ (Φ ++ [φ]) x = seqW φ₀ Φ x * (W(x) e^{iφσ_z})` (`seqW_concat`);
* `seqW_eval` (QSP-3W): for `x ∈ [-1, 1]` and `s = √(1-x²)`,
  `seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]` with `(P, Q) = qspPolyW φ₀ Φ`;
* the GSLW Thm 3 "⇒" properties of `(P, Q) = qspPolyW φ₀ Φ`, `k = Φ.length`:
  (i) `deg P ≤ k`, `deg Q ≤ k - 1` (`natDegree_qspPolyW_fst_le`, `natDegree_qspPolyW_snd_le`),
  (ii) parity `P ≡ k`, `Q ≡ k - 1` (`hasParity_qspPolyW_fst`, `hasParity_qspPolyW_snd`),
  (iii) the polynomial identity `P P^* + (1 - X²) Q Q^* = 1` (`qspPolyW_unit`), proved by
  induction on the recursion (`stepW_unit`) rather than from unitarity.

The converse (existence of phases, QSP-7c) is in `QSVT.QSP.Existence`.
-/

open Polynomial

namespace QSVT.Poly

/-! ### Parity helpers used by the rotation-convention recursion -/

/-- Multiplying by `X² - 1` preserves evenness. -/
theorem IsEven.X_sq_sub_one_mul {P : ℂ[X]} (hP : IsEven P) : IsEven ((X ^ 2 - 1) * P) := by
  rw [show (X ^ 2 - 1 : ℂ[X]) * P = -((1 - X ^ 2) * P) by ring]
  exact hP.one_sub_X_sq_mul.neg

/-- Multiplying by `X² - 1` preserves oddness. -/
theorem IsOdd.X_sq_sub_one_mul {P : ℂ[X]} (hP : IsOdd P) : IsOdd ((X ^ 2 - 1) * P) := by
  rw [show (X ^ 2 - 1 : ℂ[X]) * P = -((1 - X ^ 2) * P) by ring]
  exact hP.one_sub_X_sq_mul.neg

/-- Multiplying by `1 - X²` preserves the parity. -/
theorem HasParity.one_sub_X_sq_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) :
    HasParity ((1 - X ^ 2) * P) n :=
  ⟨fun hn => (hP.1 hn).one_sub_X_sq_mul, fun hn => (hP.2 hn).one_sub_X_sq_mul⟩

/-- A polynomial of parity `n` has no coefficient of the opposite parity:
`P.coeff m = 0` whenever `m + n` is odd. -/
theorem HasParity.coeff_eq_zero_of_odd_add {P : ℂ[X]} {n m : ℕ} (hP : HasParity P n)
    (hm : Odd (m + n)) : P.coeff m = 0 := by
  rcases Nat.even_or_odd n with hn | hn
  · exact hP.1 hn m (Nat.odd_add.mp hm |>.mpr hn)
  · refine hP.2 hn m ?_
    rw [Nat.odd_add] at hm
    exact Nat.not_odd_iff_even.mp (fun h => Nat.not_even_iff_odd.mpr hn (hm.mp h))

end QSVT.Poly

namespace QSVT.QSP

open Matrix Complex

/-! ### `conjP`: coefficients and degree -/

@[simp]
theorem coeff_conjP (P : ℂ[X]) (m : ℕ) : (conjP P).coeff m = (starRingEnd ℂ) (P.coeff m) :=
  Polynomial.coeff_map _ _

theorem natDegree_conjP_le (P : ℂ[X]) : (conjP P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_map_le

/-- `e^{iφ} e^{-iφ} = 1`. -/
theorem exp_I_mul_mul_exp_neg (φ : ℝ) :
    Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `C e^{iφ} * C e^{-iφ} = 1` in `ℂ[X]`. -/
theorem C_exp_mul_C_exp_neg (φ : ℝ) :
    (C (Complex.exp (Complex.I * φ)) : ℂ[X]) * C (Complex.exp (-(Complex.I * φ))) = 1 := by
  rw [← C_mul, exp_I_mul_mul_exp_neg, C_1]

/-! ### The rotation-convention recursion -/

/-- QSP-7. One rotation step `W(x) e^{iφσ_z}` acting on the right of a polynomial pair
(GSLW eq. (4)): `(P, Q) ↦ (e^{iφ} (X P + (X² - 1) Q), e^{-iφ} (X Q + P))`. -/
noncomputable def stepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (Complex.I * φ)) * (X * PQ.1 + (X ^ 2 - 1) * PQ.2),
    C (Complex.exp (-(Complex.I * φ))) * (X * PQ.2 + PQ.1))

/-- QSP-7. The QSP polynomials `(P, Q)` of a phase list `Φ = [φ₁, …, φ_k]` with leading phase
`φ₀` in the rotation convention (GSLW Thm 3):
`seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]`, `s = √(1-x²)`.
Base `(e^{iφ₀}, 0)`; the phases are applied from the left to the right of the list by `stepW`. -/
noncomputable def qspPolyW (φ₀ : ℝ) (Φ : List ℝ) : ℂ[X] × ℂ[X] :=
  Φ.foldl (fun PQ φ => stepW φ PQ) (C (Complex.exp (Complex.I * φ₀)), 0)

/-! ### Unfolding lemmas -/

theorem stepW_fst (φ : ℝ) (P Q : ℂ[X]) :
    (stepW φ (P, Q)).1 = C (Complex.exp (Complex.I * φ)) * (X * P + (X ^ 2 - 1) * Q) := rfl

theorem stepW_snd (φ : ℝ) (P Q : ℂ[X]) :
    (stepW φ (P, Q)).2 = C (Complex.exp (-(Complex.I * φ))) * (X * Q + P) := rfl

@[simp]
theorem qspPolyW_nil (φ₀ : ℝ) : qspPolyW φ₀ [] = (C (Complex.exp (Complex.I * φ₀)), 0) := rfl

/-- QSP-7. Appending a phase on the right applies one `stepW`. -/
theorem qspPolyW_concat (φ₀ φ : ℝ) (Φ : List ℝ) :
    qspPolyW φ₀ (Φ ++ [φ]) = stepW φ (qspPolyW φ₀ Φ) := by
  simp only [qspPolyW, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- QSP-7. `qspPolyW_concat` with the components written out:
`P' = e^{iφ} (X P + (X² - 1) Q)`, `Q' = e^{-iφ} (X Q + P)`. -/
theorem qspPolyW_concat' (φ₀ φ : ℝ) (Φ : List ℝ) :
    qspPolyW φ₀ (Φ ++ [φ]) =
      (C (Complex.exp (Complex.I * φ)) *
          (X * (qspPolyW φ₀ Φ).1 + (X ^ 2 - 1) * (qspPolyW φ₀ Φ).2),
        C (Complex.exp (-(Complex.I * φ))) * (X * (qspPolyW φ₀ Φ).2 + (qspPolyW φ₀ Φ).1)) :=
  qspPolyW_concat φ₀ φ Φ

/-- Appending a phase on the right of `seqW` multiplies by `W(x) e^{iφσ_z}` on the right. -/
theorem seqW_concat (φ₀ φ x : ℝ) (Φ : List ℝ) :
    seqW φ₀ (Φ ++ [φ]) x = seqW φ₀ Φ x * (Wrot x * phaseZ φ) := by
  simp only [seqW, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

/-! ### One step on a matrix of the shape `[[a, i b s], [i c s, d]]` -/

/-- One rotation step `W(x) e^{iφσ_z}` applied on the right of `[[a, i b s], [i c s, d]]`,
`s = √(1-x²)`, `x ∈ [-1, 1]`. -/
theorem mul_Wrot_mul_phaseZ {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) (a b c d : ℂ) :
    !![a, I * b * (Real.sqrt (1 - x ^ 2) : ℂ); I * c * (Real.sqrt (1 - x ^ 2) : ℂ), d] *
        (Wrot x * phaseZ φ) =
      !![Complex.exp (I * φ) * (x * a + ((x : ℂ) ^ 2 - 1) * b),
          I * (Complex.exp (-(I * φ)) * (x * b + a)) * (Real.sqrt (1 - x ^ 2) : ℂ);
        I * (Complex.exp (I * φ) * (x * c + d)) * (Real.sqrt (1 - x ^ 2) : ℂ),
          Complex.exp (-(I * φ)) * (x * d + ((x : ℂ) ^ 2 - 1) * c)] := by
  have hs := ofReal_sqrt_mul_self hx
  simp only [Wrot, phaseZ, Matrix.mul_fin_two, mul_zero, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero]
    linear_combination (b * Complex.exp (I * φ) * (Real.sqrt (1 - x ^ 2) : ℂ) *
      (Real.sqrt (1 - x ^ 2) : ℂ)) * I_sq - (b * Complex.exp (I * φ)) * hs
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination (c * Complex.exp (-(I * φ)) * (Real.sqrt (1 - x ^ 2) : ℂ) *
      (Real.sqrt (1 - x ^ 2) : ℂ)) * I_sq - (c * Complex.exp (-(I * φ))) * hs

/-! ### The evaluation theorem -/

/-- QSP-3W. Evaluation theorem in the rotation convention (GSLW Thm 3, "⇒"). For `x ∈ [-1, 1]`,
`s = √(1-x²)` and `(P, Q) = qspPolyW φ₀ Φ`,
`seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]`, where `P^* = conjP P` is the
coefficientwise conjugate. -/
theorem seqW_eval {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (φ₀ : ℝ) (Φ : List ℝ) :
    seqW φ₀ Φ x =
      !![(qspPolyW φ₀ Φ).1.eval (x : ℂ),
          I * (qspPolyW φ₀ Φ).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
        I * (conjP (qspPolyW φ₀ Φ).2).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (conjP (qspPolyW φ₀ Φ).1).eval (x : ℂ)] := by
  induction Φ using List.reverseRecOn with
  | nil =>
    rw [qspPolyW_nil, seqW, List.map_nil, List.prod_nil, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phaseZ, conj_exp_I_mul]
  | append_singleton Φ φ ih =>
    rw [seqW_concat, ih, mul_Wrot_mul_phaseZ hx, qspPolyW_concat', conjP_mul, conjP_mul]
    simp only [conjP_C, conjP_add, conjP_mul, conjP_X, conjP_pow, conjP_sub, conjP_one,
      conj_exp_I_mul, conj_exp_neg_I_mul, eval_mul, eval_C, eval_add, eval_X, eval_pow,
      eval_sub, eval_one]

/-- The top-left entry of `seqW φ₀ Φ x` is `P(x)`. -/
theorem seqW_apply_zero_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (φ₀ : ℝ) (Φ : List ℝ) :
    seqW φ₀ Φ x 0 0 = (qspPolyW φ₀ Φ).1.eval (x : ℂ) := by
  rw [seqW_eval hx φ₀ Φ]
  simp

/-! ### (iii) The unit identity, by induction on the recursion -/

/-- QSP-7. One `stepW` preserves `P P^* + (1 - X²) Q Q^*`. -/
theorem stepW_unit (φ : ℝ) (P Q : ℂ[X]) :
    (stepW φ (P, Q)).1 * conjP (stepW φ (P, Q)).1 +
        (1 - X ^ 2) * (stepW φ (P, Q)).2 * conjP (stepW φ (P, Q)).2 =
      P * conjP P + (1 - X ^ 2) * Q * conjP Q := by
  have h := C_exp_mul_C_exp_neg φ
  rw [stepW_fst, stepW_snd]
  simp only [conjP_mul, conjP_C, conjP_add, conjP_X, conjP_pow, conjP_sub, conjP_one,
    conj_exp_I_mul, conj_exp_neg_I_mul]
  linear_combination (P * conjP P + (1 - X ^ 2) * Q * conjP Q) * h

/-- QSP-3W (iii), polynomial form. `P P^* + (1 - X²) Q Q^* = 1` for `(P, Q) = qspPolyW φ₀ Φ`;
on `[-1, 1]` this is `|P(x)|² + (1 - x²) |Q(x)|² = 1`. -/
theorem qspPolyW_unit (φ₀ : ℝ) (Φ : List ℝ) :
    (qspPolyW φ₀ Φ).1 * conjP (qspPolyW φ₀ Φ).1 +
      (1 - X ^ 2) * (qspPolyW φ₀ Φ).2 * conjP (qspPolyW φ₀ Φ).2 = 1 := by
  induction Φ using List.reverseRecOn with
  | nil =>
    rw [qspPolyW_nil]
    simp only [conjP_C, conjP_zero, mul_zero, add_zero, conj_exp_I_mul]
    exact C_exp_mul_C_exp_neg φ₀
  | append_singleton Φ φ ih =>
    rw [qspPolyW_concat, stepW_unit, ih]

/-! ### (i) Degree bounds -/

/-- From `deg (X Q) ≤ n` deduce `deg Q ≤ n`. -/
theorem natDegree_le_of_natDegree_X_mul_le {Q : ℂ[X]} {n : ℕ} (h : (X * Q).natDegree ≤ n) :
    Q.natDegree ≤ n := by
  rcases eq_or_ne Q 0 with hQ | hQ
  · rw [hQ, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_X_mul hQ] at h
    omega

/-- Degree bounds in the induction-friendly form `deg P ≤ k`, `deg (X Q) ≤ k`. -/
theorem natDegree_qspPolyW_aux (φ₀ : ℝ) (Φ : List ℝ) :
    (qspPolyW φ₀ Φ).1.natDegree ≤ Φ.length ∧ (X * (qspPolyW φ₀ Φ).2).natDegree ≤ Φ.length := by
  induction Φ using List.reverseRecOn with
  | nil => simp
  | append_singleton Φ φ ih =>
    obtain ⟨hP, hXQ⟩ := ih
    have hQ : (qspPolyW φ₀ Φ).2.natDegree ≤ Φ.length := natDegree_le_of_natDegree_X_mul_le hXQ
    rw [qspPolyW_concat', List.length_append, List.length_singleton]
    dsimp only
    constructor
    · refine (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le ?_ ?_)
      · exact (natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega)
      · rw [show (X ^ 2 - 1 : ℂ[X]) * (qspPolyW φ₀ Φ).2 =
          X * (X * (qspPolyW φ₀ Φ).2) - (qspPolyW φ₀ Φ).2 by ring]
        refine (natDegree_sub_le _ _).trans (max_le ?_ (by omega))
        exact (natDegree_mul_le_of_le natDegree_X_le hXQ).trans (by omega)
    · refine (natDegree_mul_le_of_le natDegree_X_le ((natDegree_C_mul_le _ _).trans
        (natDegree_add_le_of_degree_le hXQ hP))).trans (by omega)

/-- QSP-3W (i). `deg P ≤ k` for `(P, Q) = qspPolyW φ₀ Φ`, `k = Φ.length`. -/
theorem natDegree_qspPolyW_fst_le (φ₀ : ℝ) (Φ : List ℝ) :
    (qspPolyW φ₀ Φ).1.natDegree ≤ Φ.length :=
  (natDegree_qspPolyW_aux φ₀ Φ).1

/-- QSP-3W (i). `deg Q ≤ k - 1` for `(P, Q) = qspPolyW φ₀ Φ`, `k = Φ.length`
(and `Q = 0` for `k = 0`, by `qspPolyW_nil`). -/
theorem natDegree_qspPolyW_snd_le (φ₀ : ℝ) (Φ : List ℝ) :
    (qspPolyW φ₀ Φ).2.natDegree ≤ Φ.length - 1 := by
  rcases eq_or_ne (qspPolyW φ₀ Φ).2 0 with hQ | hQ
  · rw [hQ, natDegree_zero]
    exact Nat.zero_le _
  · have h := (natDegree_qspPolyW_aux φ₀ Φ).2
    rw [natDegree_X_mul hQ] at h
    omega

/-! ### (ii) Parity -/

open QSVT.Poly in
/-- Parity in the induction-friendly form: `k` even gives `(P, Q)` (even, odd), `k` odd gives
(odd, even). -/
theorem parity_qspPolyW_aux (φ₀ : ℝ) (Φ : List ℝ) :
    (Even Φ.length → IsEven (qspPolyW φ₀ Φ).1 ∧ IsOdd (qspPolyW φ₀ Φ).2) ∧
      (Odd Φ.length → IsOdd (qspPolyW φ₀ Φ).1 ∧ IsEven (qspPolyW φ₀ Φ).2) := by
  induction Φ using List.reverseRecOn with
  | nil => exact ⟨fun _ => ⟨isEven_C _, isOdd_zero⟩, fun h => absurd h (by decide)⟩
  | append_singleton Φ φ ih =>
    obtain ⟨he, ho⟩ := ih
    rw [qspPolyW_concat', List.length_append, List.length_singleton]
    dsimp only
    constructor
    · intro h
      obtain ⟨hP, hQ⟩ := ho (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h))
      exact ⟨(hP.X_mul.add hQ.X_sq_sub_one_mul).C_mul _, (hQ.X_mul.add hP).C_mul _⟩
    · intro h
      obtain ⟨hP, hQ⟩ := he (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h))
      exact ⟨(hP.X_mul.add hQ.X_sq_sub_one_mul).C_mul _, (hQ.X_mul.add hP).C_mul _⟩

/-- QSP-3W (ii). `P` has the parity of `k = Φ.length`. -/
theorem hasParity_qspPolyW_fst (φ₀ : ℝ) (Φ : List ℝ) :
    QSVT.Poly.HasParity (qspPolyW φ₀ Φ).1 Φ.length :=
  ⟨fun h => ((parity_qspPolyW_aux φ₀ Φ).1 h).1, fun h => ((parity_qspPolyW_aux φ₀ Φ).2 h).1⟩

/-- QSP-3W (ii). `Q` has the parity of `k - 1`, `k = Φ.length` (for `k = 0`, `Q = 0`). -/
theorem hasParity_qspPolyW_snd (φ₀ : ℝ) (Φ : List ℝ) :
    QSVT.Poly.HasParity (qspPolyW φ₀ Φ).2 (Φ.length - 1) := by
  rcases Φ.eq_nil_or_concat with hΦ | ⟨L, ψ, hΦ⟩
  · rw [hΦ, qspPolyW_nil]
    exact QSVT.Poly.hasParity_zero _
  · have hlen : Φ.length - 1 + 1 = Φ.length := by
      rw [hΦ]
      simp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact ((parity_qspPolyW_aux φ₀ Φ).2
        (by rw [← hlen]; exact Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr h))).2
    · exact ((parity_qspPolyW_aux φ₀ Φ).1
        (by rw [← hlen]; exact Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h))).2

end QSVT.QSP
