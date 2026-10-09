/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QSVT.QSP.Conventions

/-!
# Conversion between the QSP conventions (formal-spec QSP-2, GSLW Cor 8)

The rotation convention `seqW φ₀ Φ' x = e^{iφ₀σ_z} ∏_j W(x) e^{iφ'_j σ_z}` (GSLW Thm 3) and the
reflection convention `seqR Φ x = ∏_j e^{iφ_j σ_z} R(x)` (GSLW Cor 8) are related by

  `W(x) = i e^{-iπσ_z/4} R(x) e^{-iπσ_z/4}`                         (`Wrot_eq_Rref`)

(GSLW's printed eq. (16) has `+π/4` on the right; both exponents are `-π/4`, see
`dev/qsp-convention-check.md`). Merging adjacent phase gates gives the full-matrix identity,
for `Φ' = (φ'_0, …, φ'_d)` with `d ≥ 1`, `θ := φ'_d - π/4` and
`Φ̃ := (φ'_0 - π/4, φ'_1 - π/2, …, φ'_{d-1} - π/2)` (`shift φ₀ Φ'`):

  `seqW φ'_0 (φ'_1, …, φ'_d) x = i^d • seqR Φ̃ x * e^{iθσ_z}`         (`seqW_eq_seqR`).

Since `e^{iθσ_z}` only rescales the first column and `i^d = e^{idπ/2}`, the top-left entries agree
after absorbing all scalars into the first phase (GSLW Cor 8's mapping
`φ_1 = φ'_0 + φ'_d + (d-1)π/2`, `φ_j = φ'_{j-1} - π/2` for `j ≥ 2`, `cor8Phases`):

  `(seqW φ'_0 Φ' x) 0 0 = (seqR (cor8Phases φ'_0 Φ') x) 0 0`         (`seqW_apply_zero_zero_eq`).

This is what maps the output of the usual QSP phase solvers (rotation convention) to the primary
reflection convention of this project.
-/

namespace QSVT.QSP

open Matrix Complex
open scoped Real

/-! ### One rotation step -/

/-- QSP-2 (GSLW eq. (16), corrected). `W(x) = i e^{-iπσ_z/4} R(x) e^{-iπσ_z/4}` for every real
`x`; note that both exponents are `-π/4`. -/
theorem Wrot_eq_Rref (x : ℝ) :
    Wrot x = I • (phaseZ (-(π / 4)) * Rref x * phaseZ (-(π / 4))) := by
  set e : ℂ := Complex.exp (I * ((-(π / 4) : ℝ) : ℂ)) with he_def
  set f : ℂ := Complex.exp (-(I * ((-(π / 4) : ℝ) : ℂ))) with hf_def
  have he : e * e = -I := by
    rw [he_def, ← Complex.exp_add]
    refine Eq.trans ?_ Complex.exp_neg_pi_div_two_mul_I
    congr 1; push_cast; ring
  have hf : f * f = I := by
    rw [hf_def, ← Complex.exp_add]
    refine Eq.trans ?_ Complex.exp_pi_div_two_mul_I
    congr 1; push_cast; ring
  have hef : e * f = 1 := by
    rw [he_def, hf_def, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hP : phaseZ (-(π / 4)) = !![e, 0; 0, f] := rfl
  rw [hP]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wrot, Rref]
  · linear_combination (-I * (x : ℂ)) * he + (x : ℂ) * I_sq
  · linear_combination (-(Real.sqrt (1 - x ^ 2) : ℂ)) * hef
  · linear_combination (-(Real.sqrt (1 - x ^ 2) : ℂ)) * hef
  · linear_combination (I * (x : ℂ)) * hf + (x : ℂ) * I_sq

/-- QSP-2. One rotation step with its neighbouring phases:
`e^{iφσ_z} W(x) e^{iψσ_z} = i e^{i(φ-π/4)σ_z} R(x) e^{i(ψ-π/4)σ_z}`. -/
theorem phaseZ_mul_Wrot_mul_phaseZ (φ ψ x : ℝ) :
    phaseZ φ * Wrot x * phaseZ ψ = I • (phaseZ (φ - π / 4) * Rref x * phaseZ (ψ - π / 4)) := by
  rw [Wrot_eq_Rref, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc phaseZ φ * (phaseZ (-(π / 4)) * Rref x * phaseZ (-(π / 4))) * phaseZ ψ
      = (phaseZ φ * phaseZ (-(π / 4))) * Rref x * (phaseZ (-(π / 4)) * phaseZ ψ) := by
        simp only [mul_assoc]
    _ = _ := by rw [phaseZ_mul_phaseZ, phaseZ_mul_phaseZ, ← sub_eq_add_neg, neg_add_eq_sub]

/-- QSP-2. Peeling off the first rotation of a `seqW`:
`seqW φ₀ (φ :: Φ) x = i • e^{i(φ₀-π/4)σ_z} R(x) seqW (φ - π/4) Φ x`. -/
theorem seqW_cons (φ₀ φ x : ℝ) (Φ : List ℝ) :
    seqW φ₀ (φ :: Φ) x = I • (phaseZ (φ₀ - π / 4) * Rref x * seqW (φ - π / 4) Φ x) := by
  simp only [seqW, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← mul_assoc, phaseZ_mul_Wrot_mul_phaseZ, Matrix.smul_mul]
  simp only [mul_assoc]

/-! ### The full-matrix conversion -/

/-- QSP-2. The shifted phases `Φ̃ = (φ₀ - π/4, φ'_1 - π/2, …, φ'_{d-1} - π/2)` (length `d`)
attached to a rotation sequence `seqW φ₀ (φ'_1, …, φ'_d)`; the last phase `φ'_d` is dropped and
reappears as the right factor `e^{i(φ'_d - π/4)σ_z}` in `seqW_eq_seqR`. -/
noncomputable def shift (φ₀ : ℝ) (Φ' : List ℝ) : List ℝ :=
  (φ₀ - π / 4) :: Φ'.dropLast.map (· - π / 2)

@[simp]
theorem shift_length (φ₀ : ℝ) (Φ' : List ℝ) : (shift φ₀ Φ').length = Φ'.dropLast.length + 1 := by
  simp [shift]

/-- QSP-2, concat form. For `Φ' = L ++ [ψ]`,
`seqW φ₀ (L ++ [ψ]) x = i^{|L|+1} • seqR ((φ₀ - π/4) :: L.map (· - π/2)) x * e^{i(ψ-π/4)σ_z}`. -/
theorem seqW_append_singleton (φ₀ ψ x : ℝ) (L : List ℝ) :
    seqW φ₀ (L ++ [ψ]) x =
      (I ^ (L.length + 1)) •
        (seqR ((φ₀ - π / 4) :: L.map (· - π / 2)) x * phaseZ (ψ - π / 4)) := by
  induction L generalizing φ₀ with
  | nil =>
    rw [List.nil_append, seqW_cons, seqW, List.map_nil, List.prod_nil, mul_one]
    simp [mul_assoc]
  | cons φ L ih =>
    rw [List.cons_append, seqW_cons, ih, Matrix.mul_smul, smul_smul, ← pow_succ',
      List.length_cons, List.map_cons]
    congr 1
    rw [show φ - π / 4 - π / 4 = φ - π / 2 by ring]
    simp only [seqR_cons, mul_assoc]

/-- QSP-2 (full matrix). For a nonempty rotation phase list `Φ' = (φ'_1, …, φ'_d)` with leading
phase `φ₀ = φ'_0`, `seqW φ₀ Φ' x = i^d • seqR (shift φ₀ Φ') x * e^{i(φ'_d - π/4)σ_z}`, where
`shift φ₀ Φ' = (φ₀ - π/4, φ'_1 - π/2, …, φ'_{d-1} - π/2)` (GSLW Cor 8, exact matrix form). -/
theorem seqW_eq_seqR (φ₀ x : ℝ) {Φ' : List ℝ} (hΦ : Φ' ≠ []) :
    seqW φ₀ Φ' x =
      (I ^ Φ'.length) • (seqR (shift φ₀ Φ') x * phaseZ (Φ'.getLast hΦ - π / 4)) := by
  obtain ⟨L, ψ, rfl⟩ : ∃ L ψ, Φ' = L ++ [ψ] := by
    rcases List.eq_nil_or_concat Φ' with h | ⟨L, ψ, h⟩
    · exact absurd h hΦ
    · exact ⟨L, ψ, by simpa using h⟩
  rw [seqW_append_singleton, shift, List.dropLast_concat, List.getLast_concat,
    List.length_append, List.length_singleton]

/-! ### The top-left entry (GSLW Cor 8) -/

/-- The top-left entry of `e^{iaσ_z} M` is `e^{ia} M₀₀`. -/
theorem phaseZ_mul_apply_zero_zero (a : ℝ) (M : M₂) :
    (phaseZ a * M) 0 0 = Complex.exp (I * a) * M 0 0 := by
  simp [phaseZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The top-left entry of `M e^{iaσ_z}` is `M₀₀ e^{ia}`. -/
theorem mul_phaseZ_apply_zero_zero (a : ℝ) (M : M₂) :
    (M * phaseZ a) 0 0 = M 0 0 * Complex.exp (I * a) := by
  simp [phaseZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `i^d = e^{i d π/2}`. -/
theorem I_pow_eq_exp (d : ℕ) : I ^ d = Complex.exp (I * (((d : ℝ) * (π / 2) : ℝ) : ℂ)) := by
  have h : Complex.exp (I * (((d : ℝ) * (π / 2) : ℝ) : ℂ)) = Complex.exp (π / 2 * I) ^ d := by
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [h, Complex.exp_pi_div_two_mul_I]

/-- QSP-2. The GSLW Cor 8 phase mapping from the rotation phases `(φ₀; φ'_1, …, φ'_d)` to
reflection phases: `φ_1 = φ₀ + φ'_d + (d-1)π/2` and `φ_j = φ'_{j-1} - π/2` for `2 ≤ j ≤ d`. -/
noncomputable def cor8Phases (φ₀ : ℝ) (Φ' : List ℝ) (hΦ : Φ' ≠ []) : List ℝ :=
  (φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2)) :: Φ'.dropLast.map (· - π / 2)

@[simp]
theorem cor8Phases_length (φ₀ : ℝ) (Φ' : List ℝ) (hΦ : Φ' ≠ []) :
    (cor8Phases φ₀ Φ' hΦ).length = Φ'.length := by
  simp only [cor8Phases, List.length_cons, List.length_map, List.length_dropLast]
  have := List.length_pos_of_ne_nil hΦ
  omega

/-- QSP-2 (GSLW Cor 8, top-left entry). The rotation-convention sequence with phases
`(φ₀; φ'_1, …, φ'_d)` and the reflection-convention sequence with phases `cor8Phases φ₀ Φ'`
have the same top-left entry, hence realize the same polynomial `P`. -/
theorem seqW_apply_zero_zero_eq (φ₀ x : ℝ) {Φ' : List ℝ} (hΦ : Φ' ≠ []) :
    (seqW φ₀ Φ' x) 0 0 = (seqR (cor8Phases φ₀ Φ' hΦ) x) 0 0 := by
  rw [seqW_eq_seqR φ₀ x hΦ, shift, cor8Phases, seqR_cons, seqR_cons, Matrix.smul_apply,
    smul_eq_mul, mul_phaseZ_apply_zero_zero, mul_assoc (phaseZ (φ₀ - π / 4)),
    mul_assoc (phaseZ (φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2))),
    phaseZ_mul_apply_zero_zero, phaseZ_mul_apply_zero_zero, I_pow_eq_exp]
  have key : Complex.exp (I * (((Φ'.length : ℝ) * (π / 2) : ℝ) : ℂ)) *
      Complex.exp (I * ((φ₀ - π / 4 : ℝ) : ℂ)) *
      Complex.exp (I * ((Φ'.getLast hΦ - π / 4 : ℝ) : ℂ)) =
      Complex.exp (I * ((φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  linear_combination (Rref x * seqR (Φ'.dropLast.map (· - π / 2)) x) 0 0 * key

end QSVT.QSP
