/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# QSP conventions (formal-spec QSP-1)

Single-qubit matrices used in Quantum Signal Processing (QSP), following
Gilyén–Su–Low–Wiebe (GSLW, arXiv:1806.01838).

* `Rref x`  : the reflection `R(x) = [[x, √(1-x²)], [√(1-x²), -x]]` (GSLW Def 7).
* `phaseZ φ`: the phase `e^{iφσ_z} = diag(e^{iφ}, e^{-iφ})`.
* `seqR Φ x`: the reflection-convention QSP sequence `∏_j e^{iφ_j σ_z} R(x)` (GSLW Cor 8).
* `Wrot x`  : the rotation `W(x) = [[x, i√(1-x²)], [i√(1-x²), x]]` (GSLW Thm 3).
* `seqW φ₀ Φ x`: the rotation-convention sequence `e^{iφ₀σ_z} ∏_j W(x) e^{iφ_j σ_z}`.

The reflection convention is the primary one in this project; the rotation
convention is connected to it by a conversion lemma (QSP-2, elsewhere).

This file contains only definitions and elementary lemmas (unitarity, group laws
for `phaseZ`, involutivity of `Rref`).
-/

namespace QSVT.QSP

open Matrix Complex

/-- 2×2 complex matrices: the single-qubit operators of QSP. -/
abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ

/-- The GSLW reflection `R(x) = [[x, √(1-x²)], [√(1-x²), -x]]` (GSLW Def 7).
For `x ∈ [-1, 1]` this is a Hermitian unitary (a reflection). -/
noncomputable def Rref (x : ℝ) : M₂ :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ); (Real.sqrt (1 - x ^ 2) : ℂ), -(x : ℂ)]

/-- The phase `e^{iφσ_z} = diag(e^{iφ}, e^{-iφ})`. -/
noncomputable def phaseZ (φ : ℝ) : M₂ :=
  !![Complex.exp (Complex.I * φ), 0; 0, Complex.exp (-(Complex.I * φ))]

/-- The reflection-convention QSP sequence: `seqR [φ₁, …, φ_d] x = ∏_{j=1}^{d} e^{iφ_j σ_z} R(x)`
(GSLW Cor 8), defined by recursion on the phase list. -/
noncomputable def seqR : List ℝ → ℝ → M₂
  | [], _ => 1
  | φ :: Φ, x => phaseZ φ * Rref x * seqR Φ x

/-- The GSLW rotation `W(x) = [[x, i√(1-x²)], [i√(1-x²), x]]` (GSLW Thm 3). -/
noncomputable def Wrot (x : ℝ) : M₂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x ^ 2); Complex.I * Real.sqrt (1 - x ^ 2), (x : ℂ)]

/-- The rotation-convention QSP sequence
`seqW φ₀ [φ₁, …, φ_k] x = e^{iφ₀σ_z} ∏_{j=1}^{k} W(x) e^{iφ_j σ_z}` (GSLW Thm 3). -/
noncomputable def seqW (φ₀ : ℝ) (Φ : List ℝ) (x : ℝ) : M₂ :=
  phaseZ φ₀ * (Φ.map (fun φ => Wrot x * phaseZ φ)).prod

/-! ### `seqR` unfolding lemmas -/

@[simp]
theorem seqR_nil (x : ℝ) : seqR [] x = 1 := rfl

@[simp]
theorem seqR_cons (φ : ℝ) (Φ : List ℝ) (x : ℝ) :
    seqR (φ :: Φ) x = phaseZ φ * Rref x * seqR Φ x := rfl

/-! ### `phaseZ` -/

theorem phaseZ_mul_phaseZ (φ ψ : ℝ) : phaseZ φ * phaseZ ψ = phaseZ (φ + ψ) := by
  simp only [phaseZ, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul, zero_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring_nf

@[simp]
theorem phaseZ_zero : phaseZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseZ]

/-- The conjugate transpose of `phaseZ φ` is `phaseZ (-φ)`. -/
theorem phaseZ_conjTranspose (φ : ℝ) : (phaseZ φ)ᴴ = phaseZ (-φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseZ, Matrix.conjTranspose_apply, ← Complex.exp_conj, Complex.conj_ofReal]

theorem phaseZ_neg_mul_phaseZ (φ : ℝ) : phaseZ (-φ) * phaseZ φ = 1 := by
  rw [phaseZ_mul_phaseZ, neg_add_cancel, phaseZ_zero]

theorem phaseZ_mul_phaseZ_neg (φ : ℝ) : phaseZ φ * phaseZ (-φ) = 1 := by
  rw [phaseZ_mul_phaseZ, add_neg_cancel, phaseZ_zero]

theorem phaseZ_mem_unitaryGroup (φ : ℝ) : phaseZ φ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, phaseZ_conjTranspose,
    phaseZ_mul_phaseZ_neg]

/-! ### `Rref` -/

theorem Rref_conjTranspose (x : ℝ) : (Rref x)ᴴ = Rref x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rref, Matrix.conjTranspose_apply, Complex.conj_ofReal]

theorem Rref_mul_Rref {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : Rref x * Rref x = 1 := by
  have h : (0 : ℝ) ≤ 1 - x ^ 2 := by
    obtain ⟨h₁, h₂⟩ := hx
    nlinarith
  have hs : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)
      = 1 - (x : ℂ) ^ 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rref, hs] <;> ring

theorem Rref_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Rref x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Rref_conjTranspose,
    Rref_mul_Rref hx]

/-! ### `seqR` -/

theorem seqR_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ Φ : List ℝ, seqR Φ x ∈ Matrix.unitaryGroup (Fin 2) ℂ
  | [] => by
    rw [seqR_nil]
    exact one_mem _
  | φ :: Φ => by
    rw [seqR_cons]
    exact mul_mem (mul_mem (phaseZ_mem_unitaryGroup φ) (Rref_mem_unitaryGroup hx))
      (seqR_mem_unitaryGroup hx Φ)

end QSVT.QSP
