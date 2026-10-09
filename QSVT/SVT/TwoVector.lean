/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import QSVT.Encoding.Projected
import QSVT.SVT.PhaseOp
import QSVT.SVT.AltSeq
import QSVT.QSP.Conventions
import QSVT.QSP.Structure

/-!
# The two-vector lemma for the eigenvalue transformation (formal-spec SVT-3, core)

Let `E` be a Hermitian projected unitary encoding (`U`, `Π`, `A = Π U Π = A†`) and let
`ψ ∈ ran Π` be an eigenvector of `A` with real eigenvalue `ς`. For `|ς| < 1` put
`s = √(1 - ς²)` and define the two normalised "perpendicular" vectors (GSLW, proof of Thm 17)
```
ψ̃⊥ = (1 - Π) U ψ / s     (`ψt`: the frame after `U`)
ψ⊥  = (1 - Π) U† ψ / s    (`ψp`: the frame after `U†`)
```
Then `U`, `U†` and the phase operators act on `{ψ, ψ⊥}` and `{ψ, ψ̃⊥}` exactly as the
single-qubit matrices `R(ς)` and `e^{iφσ_z}` act on the standard basis:
```
U  ψ  = ς ψ + s ψ̃⊥      U  ψ⊥  = s ψ - ς ψ̃⊥      e^{iφ(2Π-I)} ψ   = e^{iφ} ψ
U† ψ  = ς ψ + s ψ⊥      U† ψ̃⊥ = s ψ - ς ψ⊥      e^{iφ(2Π-I)} ψ⊥  = e^{-iφ} ψ⊥  (same for ψ̃⊥)
```
(`U_ψ`, `U_ψp`, `U_adjoint_ψ`, `U_adjoint_ψt`, `phaseOp_ψ`, `phaseOp_ψp`, `phaseOp_ψt`).
Consequently the alternating sequence acts on `ψ` as the QSP sequence `seqR Φ ς` acts on the
first basis vector (`altSeq_apply_eigen`):
```
U_Φ ψ = (seqR Φ ς)₀₀ ψ + (seqR Φ ς)₁₀ ψ⊥   (Φ.length even)
U_Φ ψ = (seqR Φ ς)₀₀ ψ + (seqR Φ ς)₁₀ ψ̃⊥   (Φ.length odd)
```
For `|ς| = 1` one has `U ψ = U† ψ = ς ψ` instead (`altSeq_apply_eigen_of_sq_eq_one`), and in
both cases `Π U_Φ ψ = (seqR Φ ς)₀₀ ψ` (`proj_altSeq_apply_eigen`), i.e. `Π U_Φ ψ = P_Φ(ς) ψ`
by QSP-3 (`proj_altSeq_apply_eigen_eval`): the vector form of SVT-3.

Everything here is purely algebraic in `U`, `Π`, `ψ`, `ς`; no eigenbasis is involved.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Orthogonal projections: pointwise lemmas -/

section Proj

variable {P : L ℋ}

/-- `Π ((1 - Π) v) = 0`. -/
theorem _root_.QuantumState.IsProjective.apply_one_sub_apply (hP : IsProjective P) (v : ℋ) :
    P ((1 - P) v) = 0 := by
  rw [← Module.End.mul_apply, hP.mul_one_sub, LinearMap.zero_apply]

/-- `⟪Π v, (1 - Π) v⟫ = 0`. -/
theorem _root_.QuantumState.IsProjective.inner_apply_one_sub_apply (hP : IsProjective P) (v : ℋ) :
    inner ℂ (P v) ((1 - P) v) = 0 := by
  have h := LinearMap.adjoint_inner_left P ((1 - P) v) v
  rwa [hP.adjoint_eq, hP.apply_one_sub_apply, inner_zero_right] at h

/-- `⟪(1 - Π) v, Π v⟫ = 0`. -/
theorem _root_.QuantumState.IsProjective.inner_one_sub_apply_apply (hP : IsProjective P) (v : ℋ) :
    inner ℂ ((1 - P) v) (P v) = 0 := by
  rw [← inner_conj_symm, hP.inner_apply_one_sub_apply, map_zero]

/-- Pythagoras for an orthogonal projection: `⟪v, v⟫ = ⟪Π v, Π v⟫ + ⟪(1 - Π) v, (1 - Π) v⟫`. -/
theorem _root_.QuantumState.IsProjective.inner_self_eq_add (hP : IsProjective P) (v : ℋ) :
    inner ℂ v v = inner ℂ (P v) (P v) + inner ℂ ((1 - P) v) ((1 - P) v) := by
  have hv : P v + (1 - P) v = v := by
    rw [LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
  conv_lhs => rw [← hv]
  rw [inner_add_add_self, hP.inner_apply_one_sub_apply, hP.inner_one_sub_apply_apply, add_zero,
    add_zero]

/-- SVT-2 pointwise: `e^{iφ(2Π-I)} v = e^{iφ} v` for `v ∈ ran Π`. -/
theorem phaseOp_apply_of_proj_eq (φ : ℝ) {v : ℋ} (hv : P v = v) :
    phaseOp P φ v = Complex.exp (Complex.I * φ) • v := by
  simp only [phaseOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hv, sub_self, smul_zero, add_zero]

/-- SVT-2 pointwise: `e^{iφ(2Π-I)} v = e^{-iφ} v` for `v ∈ ker Π`. -/
theorem phaseOp_apply_of_proj_eq_zero (φ : ℝ) {v : ℋ} (hv : P v = 0) :
    phaseOp P φ v = Complex.exp (-(Complex.I * φ)) • v := by
  simp only [phaseOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hv, sub_zero, smul_zero, zero_add]

/-- A unitary `V` with `Π V ψ = ς ψ`, `ς² = 1`, satisfies `V ψ = ς ψ`
(`‖V ψ‖ = ‖ψ‖ = ‖Π V ψ‖` forces `(1 - Π) V ψ = 0` by Pythagoras). -/
theorem unitary_apply_eq_smul_of_proj_apply (hP : IsProjective P) {V : L ℋ}
    (hV : V ∈ unitary (L ℋ)) {ψ : ℋ} {ς : ℝ} (hς : ς ^ 2 = 1) (hPV : P (V ψ) = (ς : ℂ) • ψ) :
    V ψ = (ς : ℂ) • ψ := by
  have hV1 : V† * V = 1 := Unitary.star_mul_self_of_mem hV
  have hVV : inner ℂ (V ψ) (V ψ) = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_left V ψ (V ψ), ← Module.End.mul_apply, hV1,
      Module.End.one_apply]
  have hpy := hP.inner_self_eq_add (V ψ)
  rw [hVV, hPV, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← sq, hς, Complex.ofReal_one, one_mul] at hpy
  have hw : inner ℂ ((1 - P) (V ψ)) ((1 - P) (V ψ)) = 0 := by linear_combination -hpy
  rw [inner_self_eq_zero, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  rw [hw, hPV]

end Proj

/-! ### Matrix entries of one QSP step -/

/-- The `(0,0)` entry of `e^{iφσ_z} R(x) M`: `e^{iφ} (x M₀₀ + √(1-x²) M₁₀)`. -/
theorem phaseZ_mul_Rref_mul_apply_zero_zero (φ x : ℝ) (M : M₂) :
    (phaseZ φ * Rref x * M) 0 0 =
      Complex.exp (Complex.I * φ) * ((x : ℂ) * M 0 0 + (Real.sqrt (1 - x ^ 2) : ℂ) * M 1 0) := by
  simp [phaseZ, Rref, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The `(1,0)` entry of `e^{iφσ_z} R(x) M`: `e^{-iφ} (√(1-x²) M₀₀ - x M₁₀)`. -/
theorem phaseZ_mul_Rref_mul_apply_one_zero (φ x : ℝ) (M : M₂) :
    (phaseZ φ * Rref x * M) 1 0 =
      Complex.exp (-(Complex.I * φ)) *
        ((Real.sqrt (1 - x ^ 2) : ℂ) * M 0 0 - (x : ℂ) * M 1 0) := by
  simp [phaseZ, Rref, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ### The two perpendicular vectors -/

section TwoVector

variable (E : HermitianEncoding ℋ) {ψ : ℋ} {ς : ℝ}

/-- SVT-3. GSLW's `ψ̃⊥ = (1 - Π) U ψ / √(1 - ς²)`: the normalised component of `U ψ`
orthogonal to `ran Π` (the frame after `U`). -/
noncomputable def ψt (ς : ℝ) (ψ : ℋ) : ℋ :=
  ((Real.sqrt (1 - ς ^ 2) : ℂ)⁻¹) • ((1 - E.P) (E.U ψ))

/-- SVT-3. GSLW's `ψ⊥ = (1 - Π) U† ψ / √(1 - ς²)`: the normalised component of `U† ψ`
orthogonal to `ran Π` (the frame after `U†`). -/
noncomputable def ψp (ς : ℝ) (ψ : ℋ) : ℋ :=
  ((Real.sqrt (1 - ς ^ 2) : ℂ)⁻¹) • ((1 - E.P) ((E.U†) ψ))

/-- SVT-3 (R0). `Π ψ̃⊥ = 0`. -/
theorem P_ψt : E.P (ψt E ς ψ) = 0 := by
  rw [ψt, map_smul, E.hP.apply_one_sub_apply, smul_zero]

/-- SVT-3 (R0). `Π ψ⊥ = 0`. -/
theorem P_ψp : E.P (ψp E ς ψ) = 0 := by
  rw [ψp, map_smul, E.hP.apply_one_sub_apply, smul_zero]

/-- SVT-3. `Π U ψ = A ψ = ς ψ` for an eigenvector `ψ ∈ ran Π`. -/
theorem P_U_apply (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) :
    E.P (E.U ψ) = (ς : ℂ) • ψ := by
  calc E.P (E.U ψ) = E.P (E.U (E.P ψ)) := by rw [hψ]
    _ = E.encoded ψ := by rw [E.encoded_eq]; rfl
    _ = (ς : ℂ) • ψ := hA

/-- SVT-3. `Π U† ψ = A† ψ = A ψ = ς ψ` for an eigenvector `ψ ∈ ran Π` (`A` self-adjoint). -/
theorem P_U_adjoint_apply (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) :
    E.P ((E.U†) ψ) = (ς : ℂ) • ψ := by
  calc E.P ((E.U†) ψ) = E.P ((E.U†) (E.P ψ)) := by rw [hψ]
    _ = ((E.encoded)†) ψ := by rw [E.encoded_adjoint, E.P'_eq]; rfl
    _ = E.encoded ψ := by rw [E.encoded_adjoint_eq]
    _ = (ς : ℂ) • ψ := hA

/-- `√(1 - ς²) ≠ 0` (as a complex number) when `ς² < 1`. -/
theorem ofReal_sqrt_ne_zero (hς : ς ^ 2 < 1) : (Real.sqrt (1 - ς ^ 2) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'

/-- `√(1 - ς²) · √(1 - ς²) = 1 - ς²` (in `ℂ`) when `ς² ≤ 1`. -/
theorem ofReal_sqrt_mul_self' (hς : ς ^ 2 ≤ 1) :
    (Real.sqrt (1 - ς ^ 2) : ℂ) * (Real.sqrt (1 - ς ^ 2) : ℂ) = 1 - (ς : ℂ) ^ 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  push_cast
  ring

/-- SVT-3 (R1). `U ψ = ς ψ + √(1 - ς²) ψ̃⊥`. -/
theorem U_ψ (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1) :
    E.U ψ = (ς : ℂ) • ψ + (Real.sqrt (1 - ς ^ 2) : ℂ) • ψt E ς ψ := by
  rw [ψt, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hς), one_smul, LinearMap.sub_apply,
    Module.End.one_apply, P_U_apply E hψ hA, add_sub_cancel]

/-- SVT-3 (R2). `U† ψ = ς ψ + √(1 - ς²) ψ⊥`. -/
theorem U_adjoint_ψ (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1) :
    (E.U†) ψ = (ς : ℂ) • ψ + (Real.sqrt (1 - ς ^ 2) : ℂ) • ψp E ς ψ := by
  rw [ψp, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hς), one_smul, LinearMap.sub_apply,
    Module.End.one_apply, P_U_adjoint_apply E hψ hA, add_sub_cancel]

/-- SVT-3 (R3). `U ψ⊥ = √(1 - ς²) ψ - ς ψ̃⊥` (from `ψ = U U† ψ`). -/
theorem U_ψp (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1) :
    E.U (ψp E ς ψ) = (Real.sqrt (1 - ς ^ 2) : ℂ) • ψ - (ς : ℂ) • ψt E ς ψ := by
  have h1 : E.U ((E.U†) ψ) = ψ := by
    rw [← Module.End.mul_apply, E.U_mul_U_adjoint, Module.End.one_apply]
  rw [U_adjoint_ψ E hψ hA hς, map_add, map_smul, map_smul, U_ψ E hψ hA hς] at h1
  refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hς) ?_
  have h2 : (Real.sqrt (1 - ς ^ 2) : ℂ) • E.U (ψp E ς ψ) =
      ψ - (ς : ℂ) • ((ς : ℂ) • ψ + (Real.sqrt (1 - ς ^ 2) : ℂ) • ψt E ς ψ) :=
    eq_sub_of_add_eq' h1
  change (Real.sqrt (1 - ς ^ 2) : ℂ) • E.U (ψp E ς ψ) =
    (Real.sqrt (1 - ς ^ 2) : ℂ) • ((Real.sqrt (1 - ς ^ 2) : ℂ) • ψ - (ς : ℂ) • ψt E ς ψ)
  rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hς.le]
  module

/-- SVT-3 (R4). `U† ψ̃⊥ = √(1 - ς²) ψ - ς ψ⊥` (from `ψ = U† U ψ`). -/
theorem U_adjoint_ψt (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1) :
    (E.U†) (ψt E ς ψ) = (Real.sqrt (1 - ς ^ 2) : ℂ) • ψ - (ς : ℂ) • ψp E ς ψ := by
  have h1 : (E.U†) (E.U ψ) = ψ := by
    rw [← Module.End.mul_apply, E.U_adjoint_mul_U, Module.End.one_apply]
  rw [U_ψ E hψ hA hς, map_add, map_smul, map_smul, U_adjoint_ψ E hψ hA hς] at h1
  refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hς) ?_
  have h2 : (Real.sqrt (1 - ς ^ 2) : ℂ) • (E.U†) (ψt E ς ψ) =
      ψ - (ς : ℂ) • ((ς : ℂ) • ψ + (Real.sqrt (1 - ς ^ 2) : ℂ) • ψp E ς ψ) :=
    eq_sub_of_add_eq' h1
  change (Real.sqrt (1 - ς ^ 2) : ℂ) • (E.U†) (ψt E ς ψ) =
    (Real.sqrt (1 - ς ^ 2) : ℂ) • ((Real.sqrt (1 - ς ^ 2) : ℂ) • ψ - (ς : ℂ) • ψp E ς ψ)
  rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hς.le]
  module

/-- SVT-3 (R5). `e^{iφ(2Π-I)} ψ = e^{iφ} ψ`. -/
theorem phaseOp_ψ (hψ : E.P ψ = ψ) (φ : ℝ) :
    phaseOp E.P φ ψ = Complex.exp (Complex.I * φ) • ψ :=
  phaseOp_apply_of_proj_eq φ hψ

/-- SVT-3 (R5). `e^{iφ(2Π-I)} ψ̃⊥ = e^{-iφ} ψ̃⊥`. -/
theorem phaseOp_ψt (φ : ℝ) :
    phaseOp E.P φ (ψt E ς ψ) = Complex.exp (-(Complex.I * φ)) • ψt E ς ψ :=
  phaseOp_apply_of_proj_eq_zero φ (P_ψt E)

/-- SVT-3 (R5). `e^{iφ(2Π-I)} ψ⊥ = e^{-iφ} ψ⊥`. -/
theorem phaseOp_ψp (φ : ℝ) :
    phaseOp E.P φ (ψp E ς ψ) = Complex.exp (-(Complex.I * φ)) • ψp E ς ψ :=
  phaseOp_apply_of_proj_eq_zero φ (P_ψp E)

/-! ### The induction lemma -/

/-- SVT-3 (induction lemma, `|ς| < 1`). The alternating sequence acts on the eigenvector `ψ`
as the QSP sequence `seqR Φ ς` acts on the first standard basis vector:
`U_Φ ψ = (seqR Φ ς)₀₀ ψ + (seqR Φ ς)₁₀ ψ⊥` for even `Φ.length`, and with `ψ̃⊥` in place of
`ψ⊥` for odd `Φ.length`. -/
theorem altSeq_apply_eigen (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1)
    (Φ : List ℝ) :
    altSeq E.toProjUnitaryEncoding Φ ψ =
      (seqR Φ ς) 0 0 • ψ + (seqR Φ ς) 1 0 • (if Even Φ.length then ψp E ς ψ else ψt E ς ψ) := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    have hlen : Even (φ :: Φ).length ↔ ¬ Even Φ.length := by
      rw [List.length_cons]
      exact Nat.even_add_one
    rw [altSeq_cons, Module.End.mul_apply, ih, seqR_cons, phaseZ_mul_Rref_mul_apply_zero_zero,
      phaseZ_mul_Rref_mul_apply_one_zero]
    by_cases h : Even Φ.length
    · have h' : ¬ Even (φ :: Φ).length := fun h2 => hlen.mp h2 h
      rw [ite_eq_left h, ite_eq_left h, ite_eq_right h', E.P'_eq, Module.End.mul_apply, map_add,
        map_smul, map_smul, U_ψ E hψ hA hς, U_ψp E hψ hA hς]
      simp only [map_add, map_sub, map_smul, phaseOp_ψ E hψ, phaseOp_ψt E]
      module
    · have h' : Even (φ :: Φ).length := hlen.mpr h
      rw [ite_eq_right h, ite_eq_right h, ite_eq_left h', Module.End.mul_apply, map_add,
        map_smul, map_smul, U_adjoint_ψ E hψ hA hς, U_adjoint_ψt E hψ hA hς]
      simp only [map_add, map_sub, map_smul, phaseOp_ψ E hψ, phaseOp_ψp E]
      module

/-! ### The endpoints `ς = ±1` -/

/-- SVT-3 (endpoint). For `ς² = 1`, `U ψ = ς ψ`. -/
theorem U_apply_eq_smul_of_sq_eq_one (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ)
    (hς : ς ^ 2 = 1) : E.U ψ = (ς : ℂ) • ψ :=
  unitary_apply_eq_smul_of_proj_apply E.hP E.hU hς (P_U_apply E hψ hA)

/-- SVT-3 (endpoint). For `ς² = 1`, `U† ψ = ς ψ`. -/
theorem U_adjoint_apply_eq_smul_of_sq_eq_one (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ)
    (hς : ς ^ 2 = 1) : (E.U†) ψ = (ς : ℂ) • ψ :=
  unitary_apply_eq_smul_of_proj_apply E.hP E.U_adjoint_mem_unitary hς (P_U_adjoint_apply E hψ hA)

/-- SVT-3 (induction lemma, `|ς| = 1`). `U_Φ ψ = (seqR Φ ς)₀₀ ψ`. -/
theorem altSeq_apply_eigen_of_sq_eq_one (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ)
    (hς : ς ^ 2 = 1) (Φ : List ℝ) :
    altSeq E.toProjUnitaryEncoding Φ ψ = (seqR Φ ς) 0 0 • ψ := by
  have hs : (Real.sqrt (1 - ς ^ 2) : ℂ) = 0 := by
    rw [hς, sub_self, Real.sqrt_zero, Complex.ofReal_zero]
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    rw [altSeq_cons, Module.End.mul_apply, ih, seqR_cons, phaseZ_mul_Rref_mul_apply_zero_zero, hs,
      zero_mul, add_zero]
    split_ifs
    · rw [E.P'_eq, Module.End.mul_apply, map_smul, U_apply_eq_smul_of_sq_eq_one E hψ hA hς,
        map_smul, map_smul, phaseOp_ψ E hψ, smul_smul, smul_smul]
      congr 1
      ring
    · rw [Module.End.mul_apply, map_smul, U_adjoint_apply_eq_smul_of_sq_eq_one E hψ hA hς,
        map_smul, map_smul, phaseOp_ψ E hψ, smul_smul, smul_smul]
      congr 1
      ring

/-! ### The headline: `Π U_Φ ψ = (seqR Φ ς)₀₀ ψ` -/

/-- SVT-3 (vector form). For a Hermitian encoding `E`, an eigenvector `ψ ∈ ran Π` of
`A = E.encoded` with eigenvalue `ς ∈ [-1, 1]`, and any phase list `Φ`,
`Π U_Φ ψ = (seqR Φ ς)₀₀ ψ`; by QSP-3 the scalar is `P_Φ(ς)`. -/
theorem proj_altSeq_apply_eigen (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ)
    (hς : ς ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    E.P (altSeq E.toProjUnitaryEncoding Φ ψ) = (seqR Φ ς) 0 0 • ψ := by
  have hsq : ς ^ 2 ≤ 1 := by nlinarith [hς.1, hς.2]
  rcases hsq.lt_or_eq with h | h
  · rw [altSeq_apply_eigen E hψ hA h Φ, map_add, map_smul, map_smul, hψ]
    split_ifs
    · rw [P_ψp, smul_zero, add_zero]
    · rw [P_ψt, smul_zero, add_zero]
  · rw [altSeq_apply_eigen_of_sq_eq_one E hψ hA h Φ, map_smul, hψ]

/-- SVT-3 (vector form, polynomial). `Π U_Φ ψ = P_Φ(ς) ψ` with `(P_Φ, Q_Φ) = qspPoly Φ`
(GSLW Thm 17 on one eigenvector). -/
theorem proj_altSeq_apply_eigen_eval (hψ : E.P ψ = ψ) (hA : E.encoded ψ = (ς : ℂ) • ψ)
    (hς : ς ∈ Set.Icc (-1 : ℝ) 1) (Φ : List ℝ) :
    E.P (altSeq E.toProjUnitaryEncoding Φ ψ) = ((qspPoly Φ).1.eval (ς : ℂ)) • ψ := by
  rw [proj_altSeq_apply_eigen E hψ hA hς Φ, seqR_apply_zero_zero hς Φ]

end TwoVector

end QSVT.SVT
