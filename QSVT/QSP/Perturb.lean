/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QSVT.QSP.Conventions

/-!
# Phase perturbation bound (formal-spec QSP-6)

Perturbing the phases of a reflection-convention QSP sequence perturbs the sequence by at most
the sum of the phase errors, in the L2 operator norm (`Matrix.Norms.L2Operator`):

* `norm_phaseZ_sub_phaseZ`: `‖e^{iφσ_z} - e^{iψσ_z}‖ ≤ |φ - ψ|` (the phase gate is diagonal
  with entries `e^{±iφ}`, and `‖e^{iφ} - e^{iψ}‖ = 2|sin((φ-ψ)/2)| ≤ |φ - ψ|`);
* `norm_seqR_sub_seqR_le`: `‖seqR Φ x - seqR Φ' x‖ ≤ ∑_j |φ_j - φ'_j|` for `x ∈ [-1, 1]` and
  phase lists of equal length, by telescoping `AB - A'B' = (A - A')B + A'(B - B')` over unitary
  factors (which have norm `1`);
* `norm_seqR_sub_seqR`: the same with the constant `2` of the specification;
* `norm_seqR_sub_seqR_apply`: the entrywise consequence, via `‖A i j‖ ≤ ‖A‖`
  (`norm_apply_le_l2_opNorm`).

This is used to compare rational (certificate) phases with the theoretical ones (Route B).

## Mathlib facts used

`Matrix.instL2OpNormedRing`, `Matrix.instCStarRing` (scoped instances in
`Matrix.Norms.L2Operator`), `CStarRing.norm_of_mem_unitary`, `Matrix.l2_opNorm_diagonal`,
`pi_norm_le_iff_of_nonneg`, `Real.norm_exp_I_mul_ofReal_sub_one_le`, `Matrix.toEuclideanCLM_toLp`,
`Matrix.l2_opNorm_toEuclideanCLM`, `PiLp.norm_apply_le`, `PiLp.norm_single`.
-/

namespace QSVT.QSP

open Matrix Complex
open scoped Real Matrix.Norms.L2Operator

/-! ### Unitaries have operator norm one -/

/-- QSP-6. `‖e^{iφσ_z}‖ = 1`. -/
theorem norm_phaseZ (φ : ℝ) : ‖phaseZ φ‖ = 1 :=
  CStarRing.norm_of_mem_unitary (phaseZ_mem_unitaryGroup φ)

/-- QSP-6. `‖R(x)‖ = 1` for `x ∈ [-1, 1]`. -/
theorem norm_Rref {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : ‖Rref x‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Rref_mem_unitaryGroup hx)

/-- QSP-6. `‖seqR Φ x‖ = 1` for `x ∈ [-1, 1]`. -/
theorem norm_seqR {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) : ‖seqR Φ x‖ = 1 :=
  CStarRing.norm_of_mem_unitary (seqR_mem_unitaryGroup hx Φ)

/-! ### The phase gate is `1`-Lipschitz -/

/-- `‖e^{iφ} - e^{iψ}‖ ≤ |φ - ψ|`. -/
theorem norm_exp_I_mul_sub_exp_I_mul (φ ψ : ℝ) :
    ‖Complex.exp (I * φ) - Complex.exp (I * ψ)‖ ≤ |φ - ψ| := by
  have h : Complex.exp (I * φ) - Complex.exp (I * ψ)
      = Complex.exp (I * ψ) * (Complex.exp (I * ((φ - ψ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `phaseZ φ` as a diagonal matrix. -/
theorem phaseZ_eq_diagonal (φ : ℝ) :
    phaseZ φ = diagonal ![Complex.exp (I * φ), Complex.exp (-(I * φ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseZ]

/-- QSP-6. `‖e^{iφσ_z} - e^{iψσ_z}‖ ≤ |φ - ψ|` in the L2 operator norm. -/
theorem norm_phaseZ_sub_phaseZ (φ ψ : ℝ) : ‖phaseZ φ - phaseZ ψ‖ ≤ |φ - ψ| := by
  rw [phaseZ_eq_diagonal, phaseZ_eq_diagonal, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro i
  fin_cases i
  · simpa using norm_exp_I_mul_sub_exp_I_mul φ ψ
  · have h := norm_exp_I_mul_sub_exp_I_mul (-φ) (-ψ)
    rw [neg_sub_neg, abs_sub_comm] at h
    simpa [mul_neg] using h

/-! ### Entries are bounded by the operator norm -/

/-- `‖A i j‖ ≤ ‖A‖` for the L2 operator norm: evaluate `A` on the `j`-th basis vector. -/
theorem norm_apply_le_l2_opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  set v : EuclideanSpace ℂ n := WithLp.toLp 2 (Pi.single j (1 : ℂ)) with hv
  calc ‖A i j‖ = ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v) i‖ := by
        rw [hv, Matrix.toEuclideanCLM_toLp, PiLp.toLp_apply, Matrix.mulVec_single_one,
          Matrix.col_apply]
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ := by
        rw [Matrix.l2_opNorm_toEuclideanCLM, hv, PiLp.toLp_single, PiLp.norm_single, norm_one,
          mul_one]

/-! ### Telescoping over the phase list -/

/-- QSP-6 (sharp form). For `x ∈ [-1, 1]` and phase lists of equal length,
`‖seqR Φ x - seqR Φ' x‖ ≤ ∑_j |φ_j - φ'_j|` (L2 operator norm), by telescoping
`AB - A'B' = (A - A')B + A'(B - B')` over the unitary factors. -/
theorem norm_seqR_sub_seqR_le {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ (Φ Φ' : List ℝ), Φ.length = Φ'.length →
      ‖seqR Φ x - seqR Φ' x‖ ≤ ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | φ :: Φ, ψ :: Φ', h => by
    have ih := norm_seqR_sub_seqR_le hx Φ Φ' (by simpa using h)
    rw [seqR_cons, seqR_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
    have key : phaseZ φ * Rref x * seqR Φ x - phaseZ ψ * Rref x * seqR Φ' x
        = (phaseZ φ - phaseZ ψ) * Rref x * seqR Φ x
          + phaseZ ψ * Rref x * (seqR Φ x - seqR Φ' x) := by
      noncomm_ring
    have h1 : ‖(phaseZ φ - phaseZ ψ) * Rref x * seqR Φ x‖ ≤ |φ - ψ| :=
      calc ‖(phaseZ φ - phaseZ ψ) * Rref x * seqR Φ x‖
          ≤ ‖(phaseZ φ - phaseZ ψ) * Rref x‖ * ‖seqR Φ x‖ := norm_mul_le _ _
        _ ≤ ‖phaseZ φ - phaseZ ψ‖ * ‖Rref x‖ * ‖seqR Φ x‖ := by
            gcongr
            exact norm_mul_le _ _
        _ = ‖phaseZ φ - phaseZ ψ‖ := by rw [norm_Rref hx, norm_seqR hx, mul_one, mul_one]
        _ ≤ |φ - ψ| := norm_phaseZ_sub_phaseZ φ ψ
    have h2 : ‖phaseZ ψ * Rref x * (seqR Φ x - seqR Φ' x)‖ ≤ ‖seqR Φ x - seqR Φ' x‖ :=
      calc ‖phaseZ ψ * Rref x * (seqR Φ x - seqR Φ' x)‖
          ≤ ‖phaseZ ψ * Rref x‖ * ‖seqR Φ x - seqR Φ' x‖ := norm_mul_le _ _
        _ ≤ ‖phaseZ ψ‖ * ‖Rref x‖ * ‖seqR Φ x - seqR Φ' x‖ := by
            gcongr
            exact norm_mul_le _ _
        _ = ‖seqR Φ x - seqR Φ' x‖ := by rw [norm_phaseZ, norm_Rref hx, one_mul, one_mul]
    calc ‖phaseZ φ * Rref x * seqR Φ x - phaseZ ψ * Rref x * seqR Φ' x‖
        = ‖(phaseZ φ - phaseZ ψ) * Rref x * seqR Φ x
            + phaseZ ψ * Rref x * (seqR Φ x - seqR Φ' x)‖ := by rw [key]
      _ ≤ ‖(phaseZ φ - phaseZ ψ) * Rref x * seqR Φ x‖
            + ‖phaseZ ψ * Rref x * (seqR Φ x - seqR Φ' x)‖ := norm_add_le _ _
      _ ≤ |φ - ψ| + ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum := add_le_add h1 (h2.trans ih)

/-- The sum of phase errors is nonnegative. -/
theorem phaseErr_sum_nonneg (Φ Φ' : List ℝ) :
    0 ≤ ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum := by
  refine List.sum_nonneg fun a ha => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  exact abs_nonneg _

/-- QSP-6. Perturbation bound in the form of the specification: for `x ∈ [-1, 1]` and phase
lists of equal length, `‖seqR Φ x - seqR Φ' x‖ ≤ 2 ∑_j |φ_j - φ'_j|` (L2 operator norm). -/
theorem norm_seqR_sub_seqR {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ Φ' : List ℝ)
    (hl : Φ.length = Φ'.length) :
    ‖seqR Φ x - seqR Φ' x‖ ≤ 2 * ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum := by
  have h := norm_seqR_sub_seqR_le hx Φ Φ' hl
  have hs := phaseErr_sum_nonneg Φ Φ'
  linarith

/-- QSP-6 (entrywise). Every entry of `seqR Φ x - seqR Φ' x` is bounded by
`∑_j |φ_j - φ'_j|`; in particular the realized polynomials `P_Φ(x)` (top-left entries) differ by at
most the total phase error. -/
theorem norm_seqR_sub_seqR_apply_le {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ Φ' : List ℝ)
    (hl : Φ.length = Φ'.length) (i j : Fin 2) :
    ‖(seqR Φ x) i j - (seqR Φ' x) i j‖ ≤ ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum :=
  calc ‖(seqR Φ x) i j - (seqR Φ' x) i j‖ = ‖(seqR Φ x - seqR Φ' x) i j‖ := by
        rw [Matrix.sub_apply]
    _ ≤ ‖seqR Φ x - seqR Φ' x‖ := norm_apply_le_l2_opNorm _ i j
    _ ≤ _ := norm_seqR_sub_seqR_le hx Φ Φ' hl

/-- QSP-6 (entrywise, specification constant). -/
theorem norm_seqR_sub_seqR_apply {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (Φ Φ' : List ℝ)
    (hl : Φ.length = Φ'.length) (i j : Fin 2) :
    ‖(seqR Φ x) i j - (seqR Φ' x) i j‖ ≤ 2 * ((Φ.zip Φ').map (fun p => |p.1 - p.2|)).sum := by
  have h := norm_seqR_sub_seqR_apply_le hx Φ Φ' hl i j
  have hs := phaseErr_sum_nonneg Φ Φ'
  linarith

end QSVT.QSP
