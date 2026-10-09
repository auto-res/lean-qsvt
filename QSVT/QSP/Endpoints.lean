/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Conventions

/-!
# Endpoint formulas (formal-spec QSP-5, GSLW Cor 8 "moreover")

At `x = ±1` the reflection `R(x)` is diagonal, so `seqR Φ (±1)` is diagonal with top-left entry
`P_Φ(±1) = (±1)^d ∏_j e^{iφ_j}` (`d = Φ.length`). At `x = 0`, `R(0) = σ_x` swaps the two rows,
so `seqR Φ 0` is diagonal for even `d` and anti-diagonal for odd `d`; the surviving entry of the
first row is `e^{i alt Φ}`, where `alt Φ = φ₁ - φ₂ + φ₃ - ⋯` is the alternating sum of the phases
(GSLW write this as `e^{-i Σ_j (-1)^j φ_j}`).

Everything is stated on the matrix entries of `seqR`; the polynomial `P_Φ` is defined elsewhere.
-/

namespace QSVT.QSP

open Matrix Complex

/-! ### `Rref` at the endpoints -/

/-- QSP-5. `R(1) = diag(1, -1)`. -/
theorem Rref_one : Rref 1 = !![1, 0; 0, -1] := by
  simp [Rref]

/-- QSP-5. `R(-1) = diag(-1, 1)`. -/
theorem Rref_neg_one : Rref (-1) = !![-1, 0; 0, 1] := by
  simp [Rref]

/-- QSP-5. `R(0) = σ_x = [[0, 1], [1, 0]]`. -/
theorem Rref_zero : Rref 0 = !![0, 1; 1, 0] := by
  simp [Rref]

/-! ### `x = 1` and `x = -1` -/

/-- QSP-5 (GSLW Cor 8). At `x = 1` the QSP sequence is diagonal:
`seqR Φ 1 = diag(∏_j e^{iφ_j}, (-1)^d ∏_j e^{-iφ_j})` with `d = Φ.length`. -/
theorem seqR_one (Φ : List ℝ) :
    seqR Φ 1 = !![(Φ.map (fun φ => Complex.exp (Complex.I * φ))).prod, 0;
      0, (-1) ^ Φ.length * (Φ.map (fun φ => Complex.exp (-(Complex.I * φ)))).prod] := by
  induction Φ with
  | nil => simp [Matrix.one_fin_two]
  | cons φ Φ ih =>
    rw [seqR_cons, Rref_one, ih, phaseZ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- QSP-5 (GSLW Cor 8 "moreover"). `P_Φ(1) = ∏_j e^{iφ_j}`. -/
theorem seqR_one_apply (Φ : List ℝ) :
    (seqR Φ 1) 0 0 = (Φ.map (fun φ => Complex.exp (Complex.I * φ))).prod := by
  rw [seqR_one]
  simp

/-- QSP-5 (GSLW Cor 8). At `x = -1` the QSP sequence is diagonal:
`seqR Φ (-1) = diag((-1)^d ∏_j e^{iφ_j}, ∏_j e^{-iφ_j})` with `d = Φ.length`. -/
theorem seqR_neg_one (Φ : List ℝ) :
    seqR Φ (-1) = !![(-1) ^ Φ.length * (Φ.map (fun φ => Complex.exp (Complex.I * φ))).prod, 0;
      0, (Φ.map (fun φ => Complex.exp (-(Complex.I * φ)))).prod] := by
  induction Φ with
  | nil => simp [Matrix.one_fin_two]
  | cons φ Φ ih =>
    rw [seqR_cons, Rref_neg_one, ih, phaseZ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- QSP-5 (GSLW Cor 8 "moreover"). `P_Φ(-1) = (-1)^d ∏_j e^{iφ_j}` with `d = Φ.length`. -/
theorem seqR_neg_one_apply (Φ : List ℝ) :
    (seqR Φ (-1)) 0 0 = (-1) ^ Φ.length * (Φ.map (fun φ => Complex.exp (Complex.I * φ))).prod := by
  rw [seqR_neg_one]
  simp

/-! ### `x = 0` -/

/-- QSP-5. The alternating sum `alt [φ₁, …, φ_d] = φ₁ - φ₂ + φ₃ - ⋯ = Σ_j (-1)^(j+1) φ_j`
(indices from `1`), defined by `alt [] = 0`, `alt (φ :: Φ) = φ - alt Φ`. -/
def alt : List ℝ → ℝ
  | [] => 0
  | φ :: Φ => φ - alt Φ

@[simp]
theorem alt_nil : alt [] = 0 := rfl

@[simp]
theorem alt_cons (φ : ℝ) (Φ : List ℝ) : alt (φ :: Φ) = φ - alt Φ := rfl

/-- `alt Φ = Σ_{j < d} (-1)^j Φ[j]` (`0`-based indices). -/
theorem alt_eq_sum (Φ : List ℝ) :
    alt Φ = ∑ j : Fin Φ.length, (-1 : ℝ) ^ (j : ℕ) * Φ.get j := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    rw [alt_cons, ih]
    change _ = ∑ j : Fin (Φ.length + 1), (-1 : ℝ) ^ (j : ℕ) * (φ :: Φ).get j
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, List.get_cons_zero, Fin.val_succ,
      List.get_cons_succ', pow_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

theorem exp_I_mul_sub (φ a : ℝ) :
    Complex.exp (Complex.I * ((φ - a : ℝ) : ℂ))
      = Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * a)) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem exp_neg_I_mul_sub (φ a : ℝ) :
    Complex.exp (-(Complex.I * ((φ - a : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * φ)) * Complex.exp (Complex.I * a) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- QSP-5, auxiliary (both parities at once, for the induction). At `x = 0`,
`seqR Φ 0 = diag(e^{i alt Φ}, e^{-i alt Φ})` for even `Φ.length` and
`seqR Φ 0 = [[0, e^{i alt Φ}], [e^{-i alt Φ}, 0]]` for odd `Φ.length`. -/
theorem seqR_zero_even_odd (Φ : List ℝ) :
    (Even Φ.length →
        seqR Φ 0 =
          !![Complex.exp (Complex.I * alt Φ), 0; 0, Complex.exp (-(Complex.I * alt Φ))]) ∧
      (Odd Φ.length →
        seqR Φ 0 =
          !![0, Complex.exp (Complex.I * alt Φ); Complex.exp (-(Complex.I * alt Φ)), 0]) := by
  induction Φ with
  | nil =>
    refine ⟨fun _ => ?_, fun h => absurd h Nat.not_odd_zero⟩
    simp [Matrix.one_fin_two]
  | cons φ Φ ih =>
    obtain ⟨ihe, iho⟩ := ih
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ho : Odd Φ.length := by simpa [Nat.even_add_one] using h
      rw [seqR_cons, Rref_zero, iho ho, phaseZ, alt_cons, exp_I_mul_sub, exp_neg_I_mul_sub]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · have he : Even Φ.length := by simpa [Nat.odd_add_one] using h
      rw [seqR_cons, Rref_zero, ihe he, phaseZ, alt_cons, exp_I_mul_sub, exp_neg_I_mul_sub]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- QSP-5 (GSLW Cor 8 "moreover"). For even `d = Φ.length`,
`seqR Φ 0 = diag(e^{i alt Φ}, e^{-i alt Φ})`. -/
theorem seqR_zero_of_even {Φ : List ℝ} (h : Even Φ.length) :
    seqR Φ 0 = !![Complex.exp (Complex.I * alt Φ), 0; 0, Complex.exp (-(Complex.I * alt Φ))] :=
  (seqR_zero_even_odd Φ).1 h

/-- QSP-5. For odd `d = Φ.length`, `seqR Φ 0 = [[0, e^{i alt Φ}], [e^{-i alt Φ}, 0]]`. -/
theorem seqR_zero_of_odd {Φ : List ℝ} (h : Odd Φ.length) :
    seqR Φ 0 = !![0, Complex.exp (Complex.I * alt Φ); Complex.exp (-(Complex.I * alt Φ)), 0] :=
  (seqR_zero_even_odd Φ).2 h

/-- QSP-5 (GSLW Cor 8 "moreover"). For even `d`, `P_Φ(0) = e^{i alt Φ} = e^{-i Σ_j (-1)^j φ_j}`. -/
theorem seqR_zero_apply_of_even {Φ : List ℝ} (h : Even Φ.length) :
    (seqR Φ 0) 0 0 = Complex.exp (Complex.I * alt Φ) := by
  rw [seqR_zero_of_even h]
  simp

/-- QSP-5. For even `d`, the top-right entry of `seqR Φ 0` vanishes. -/
theorem seqR_zero_apply_zero_one_of_even {Φ : List ℝ} (h : Even Φ.length) :
    (seqR Φ 0) 0 1 = 0 := by
  rw [seqR_zero_of_even h]
  simp

/-- QSP-5. For odd `d`, `P_Φ(0) = 0`. -/
theorem seqR_zero_apply_of_odd {Φ : List ℝ} (h : Odd Φ.length) :
    (seqR Φ 0) 0 0 = 0 := by
  rw [seqR_zero_of_odd h]
  simp

/-- QSP-5. For odd `d`, the top-right entry of `seqR Φ 0` is `e^{i alt Φ}`. -/
theorem seqR_zero_apply_zero_one_of_odd {Φ : List ℝ} (h : Odd Φ.length) :
    (seqR Φ 0) 0 1 = Complex.exp (Complex.I * alt Φ) := by
  rw [seqR_zero_of_odd h]
  simp

end QSVT.QSP
