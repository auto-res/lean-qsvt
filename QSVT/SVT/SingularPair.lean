/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.TwoFrame

/-!
# The two-frame lemma for an arbitrary singular pair (formal-spec SVT-7, general vector form)

`QSVT.SVT.TwoFrame` proves the frame relations and the vector form of GSLW Thm 17 for the
specific orthonormal basis `rv E i` of right singular vectors produced by the spectral theorem.
Its proofs only use three facts about the pair `(ψ, σ)`: `Π ψ = ψ`, `0 ≤ σ ≤ 1`, and the Gram
equation `A†A ψ = σ² ψ`. This module abstracts them into the predicate `IsSingularPair E ψ σ`
and re-proves everything for an *arbitrary* right singular vector `ψ` (not necessarily a member
of the basis, not necessarily normalised): with
```
ψ̃  = lvOf E ψ σ  = A ψ / σ                 (`0` when `σ = 0`)
ψ̃⊥ = lvtOf E ψ σ = (1 - Π̃) U ψ / √(1 - σ²)
ψ⊥  = rvpOf E ψ σ = (1 - Π) U† ψ̃ / √(1 - σ²)
```
one has `A ψ = σ ψ̃`, `A† ψ̃ = σ ψ`, the relations (R0)–(R5) of `QSVT.SVT.TwoFrame`, the induction
lemma `altSeq_apply_singular`, and the headline
```
Π̃ U_Φ ψ = P_Φ(σ) ψ̃    (Φ.length odd,  `proj_altSeq_apply_singular_odd`)
Π  U_Φ ψ = P_Φ(σ) ψ    (Φ.length even, `proj_altSeq_apply_singular_even`)
```
valid for every singular pair including the endpoints `σ = 0` and `σ = 1`. The basis vectors of
SVT-6 are singular pairs (`isSingularPair_rv`, with `lvOf E (rv E i) (σ E i) = lv E i`
definitionally), so nothing is lost.

The point of the generalisation is applications such as fixed-point amplitude amplification
(`QSVT.Examples.FixedPointAA`), where the right singular vector `ψ₀` is given by the problem and
one wants `Π̃ U_Φ ψ₀` without identifying `ψ₀` inside the abstract basis `rv E i`.

`IsSingularPair.mk'` builds a singular pair from `Π ψ = ψ`, `0 ≤ σ`, `A†A ψ = σ² ψ` and `ψ ≠ 0`
(then `σ ≤ 1` follows from `‖A ψ‖ ≤ ‖ψ‖`).
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Singular pairs -/

/-- SVT-7. `(ψ, σ)` is a *singular pair* of the encoding `E` (encoded operator `A = Π̃ U Π`):
`ψ ∈ ran Π` is a right singular vector with singular value `σ ∈ [0, 1]`, in the SVD-free form
`A†A ψ = σ² ψ`. No normalisation of `ψ` is assumed (`ψ = 0` is allowed). -/
structure IsSingularPair (E : ProjUnitaryEncoding ℋ) (ψ : ℋ) (σ : ℝ) : Prop where
  /-- `Π ψ = ψ`. -/
  P_eq : E.P ψ = ψ
  /-- `0 ≤ σ`. -/
  nonneg : 0 ≤ σ
  /-- `σ ≤ 1`. -/
  le_one : σ ≤ 1
  /-- `A†A ψ = σ² ψ`. -/
  gram : (E.encoded†) (E.encoded ψ) = ((σ : ℂ) ^ 2) • ψ

section Defs

variable (E : ProjUnitaryEncoding ℋ)

/-- SVT-7. The left singular vector `ψ̃ = A ψ / σ` attached to a right singular vector `ψ` with
singular value `σ` (`0` when `σ = 0`); generalises `lv`. -/
noncomputable def lvOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  if σ = 0 then 0 else ((σ : ℂ)⁻¹) • E.encoded ψ

/-- SVT-7. GSLW's `ψ̃⊥ = (1 - Π̃) U ψ / √(1 - σ²)` for an arbitrary singular pair; generalises
`lvt`. -/
noncomputable def lvtOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  ((Real.sqrt (1 - σ ^ 2) : ℂ)⁻¹) • ((1 - E.P') (E.U ψ))

/-- SVT-7. GSLW's `ψ⊥ = (1 - Π) U† ψ̃ / √(1 - σ²)` for an arbitrary singular pair; generalises
`rvp`. -/
noncomputable def rvpOf (ψ : ℋ) (σ : ℝ) : ℋ :=
  ((Real.sqrt (1 - σ ^ 2) : ℂ)⁻¹) • ((1 - E.P) ((E.U†) (lvOf E ψ σ)))

/-- SVT-7. `ψ̃ = 0` when `σ = 0`. -/
theorem lvOf_of_eq_zero {ψ : ℋ} {σ : ℝ} (h0 : σ = 0) : lvOf E ψ σ = 0 := by
  rw [lvOf, ite_eq_left h0]

/-- SVT-7. `ψ̃ = σ⁻¹ A ψ` when `σ ≠ 0`. -/
theorem lvOf_of_ne_zero {ψ : ℋ} {σ : ℝ} (h0 : σ ≠ 0) :
    lvOf E ψ σ = ((σ : ℂ)⁻¹) • E.encoded ψ := by
  rw [lvOf, ite_eq_right h0]

/-- SVT-7. `Π̃ ψ̃ = ψ̃` (`ψ̃ ∈ ran Π̃`), for every `ψ`, `σ`. -/
theorem P'_lvOf (ψ : ℋ) (σ : ℝ) : E.P' (lvOf E ψ σ) = lvOf E ψ σ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, map_zero]
  · rw [lvOf_of_ne_zero E h0, map_smul, ← Module.End.mul_apply, E.P'_mul_encoded]

/-- SVT-7 (R0). `Π̃ ψ̃⊥ = 0`. -/
theorem P'_lvtOf (ψ : ℋ) (σ : ℝ) : E.P' (lvtOf E ψ σ) = 0 := by
  rw [lvtOf, map_smul, E.hP'.apply_one_sub_apply, smul_zero]

/-- SVT-7 (R0). `Π ψ⊥ = 0`. -/
theorem P_rvpOf (ψ : ℋ) (σ : ℝ) : E.P (rvpOf E ψ σ) = 0 := by
  rw [rvpOf, map_smul, E.hP.apply_one_sub_apply, smul_zero]

/-- SVT-7 (R5). `e^{iφ(2Π̃-I)} ψ̃ = e^{iφ} ψ̃`. -/
theorem phaseOp_P'_lvOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P' φ (lvOf E ψ σ) = Complex.exp (Complex.I * φ) • lvOf E ψ σ :=
  phaseOp_apply_of_proj_eq φ (P'_lvOf E ψ σ)

/-- SVT-7 (R5). `e^{iφ(2Π̃-I)} ψ̃⊥ = e^{-iφ} ψ̃⊥`. -/
theorem phaseOp_P'_lvtOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P' φ (lvtOf E ψ σ) = Complex.exp (-(Complex.I * φ)) • lvtOf E ψ σ :=
  phaseOp_apply_of_proj_eq_zero φ (P'_lvtOf E ψ σ)

/-- SVT-7 (R5). `e^{iφ(2Π-I)} ψ⊥ = e^{-iφ} ψ⊥`. -/
theorem phaseOp_P_rvpOf (ψ : ℋ) (σ : ℝ) (φ : ℝ) :
    phaseOp E.P φ (rvpOf E ψ σ) = Complex.exp (-(Complex.I * φ)) • rvpOf E ψ σ :=
  phaseOp_apply_of_proj_eq_zero φ (P_rvpOf E ψ σ)

/-- SVT-7 (endpoint). `√(1 - σ²) = 0` (in `ℂ`) when `σ = 1`. -/
theorem ofReal_sqrt_one_sub_sq_eq_zero {σ : ℝ} (h1 : σ = 1) :
    (Real.sqrt (1 - σ ^ 2) : ℂ) = 0 := by
  rw [h1, one_pow, sub_self, Real.sqrt_zero, Complex.ofReal_zero]

/-- SVT-7 (endpoint). `ψ̃⊥ = 0` when `σ = 1`. -/
theorem lvtOf_of_eq_one {ψ : ℋ} {σ : ℝ} (h1 : σ = 1) : lvtOf E ψ σ = 0 := by
  rw [lvtOf, ofReal_sqrt_one_sub_sq_eq_zero h1, inv_zero, zero_smul]

/-- SVT-7 (endpoint). `ψ⊥ = 0` when `σ = 1`. -/
theorem rvpOf_of_eq_one {ψ : ℋ} {σ : ℝ} (h1 : σ = 1) : rvpOf E ψ σ = 0 := by
  rw [rvpOf, ofReal_sqrt_one_sub_sq_eq_zero h1, inv_zero, zero_smul]

/-! ### The basis vectors of SVT-6 are singular pairs -/

/-- SVT-7. The right singular vectors `rv E i` of SVT-6 with their singular values `σ E i` are
singular pairs. -/
theorem isSingularPair_rv (i : svIndex E) : IsSingularPair E (rv E i) (σ E i) where
  P_eq := P_rv E i
  nonneg := σ_nonneg E i
  le_one := σ_le_one E i
  gram := by rw [← Module.End.mul_apply, gram_rv, ofReal_σ_sq]

/-- SVT-7. On the basis vectors, `lvOf` is the left singular vector `lv` of SVT-6. -/
theorem lvOf_rv (i : svIndex E) : lvOf E (rv E i) (σ E i) = lv E i := rfl

end Defs

namespace IsSingularPair

variable {E : ProjUnitaryEncoding ℋ} {ψ : ℋ} {σ : ℝ}

/-! ### Elementary consequences of the Gram equation -/

/-- SVT-7. `σ² ≤ 1`. -/
theorem sq_le_one (h : IsSingularPair E ψ σ) : σ ^ 2 ≤ 1 := pow_le_one₀ h.nonneg h.le_one

/-- SVT-7. `σ ∈ [-1, 1]` (the form needed by the QSP evaluation theorem QSP-3). -/
theorem mem_Icc_neg_one_one (h : IsSingularPair E ψ σ) : σ ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith [h.nonneg], h.le_one⟩

/-- SVT-7. `σ² = 1 → σ = 1` (as `σ ≥ 0`). -/
theorem eq_one_of_sq_eq_one (h : IsSingularPair E ψ σ) (h1 : σ ^ 2 = 1) : σ = 1 :=
  (pow_eq_one_iff_of_nonneg h.nonneg two_ne_zero).mp h1

/-- SVT-7. `‖A ψ‖² = σ² ‖ψ‖²`, from `⟪A†A ψ, ψ⟫ = ⟪A ψ, A ψ⟫`. -/
theorem norm_encoded_sq (h : IsSingularPair E ψ σ) : ‖E.encoded ψ‖ ^ 2 = σ ^ 2 * ‖ψ‖ ^ 2 := by
  have h1 : inner ℂ ((E.encoded†) (E.encoded ψ)) ψ = inner ℂ (E.encoded ψ) (E.encoded ψ) :=
    LinearMap.adjoint_inner_left _ _ _
  rw [h.gram, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, map_pow,
    Complex.conj_ofReal] at h1
  have h2 := congrArg Complex.re h1
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_mul] using h2.symm

/-- SVT-7. `‖A ψ‖ = σ ‖ψ‖`. -/
theorem norm_encoded (h : IsSingularPair E ψ σ) : ‖E.encoded ψ‖ = σ * ‖ψ‖ := by
  have h1 := h.norm_encoded_sq
  rw [← mul_pow] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg h.nonneg (norm_nonneg _)) two_ne_zero).mp h1

/-- SVT-7. `A ψ = 0` when `σ = 0`. -/
theorem encoded_eq_zero_of_eq_zero (h : IsSingularPair E ψ σ) (h0 : σ = 0) :
    E.encoded ψ = 0 := by
  rw [← norm_eq_zero, h.norm_encoded, h0, zero_mul]

/-- SVT-7 (defining relation). `A ψ = σ ψ̃`. -/
theorem A_apply (h : IsSingularPair E ψ σ) : E.encoded ψ = (σ : ℂ) • lvOf E ψ σ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, h.encoded_eq_zero_of_eq_zero h0, smul_zero]
  · rw [lvOf_of_ne_zero E h0, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h0), one_smul]

/-- SVT-7 (defining relation). `A† ψ̃ = σ ψ` (from `A†A ψ = σ² ψ`). -/
theorem A_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    (E.encoded†) (lvOf E ψ σ) = (σ : ℂ) • ψ := by
  by_cases h0 : σ = 0
  · rw [lvOf_of_eq_zero E h0, map_zero, h0, Complex.ofReal_zero, zero_smul]
  · have hc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
    rw [lvOf_of_ne_zero E h0, map_smul, h.gram, smul_smul, sq, ← mul_assoc, inv_mul_cancel₀ hc,
      one_mul]

/-- SVT-7. `‖ψ̃‖ = ‖ψ‖` when `σ ≠ 0`. -/
theorem norm_lvOf (h : IsSingularPair E ψ σ) (h0 : σ ≠ 0) : ‖lvOf E ψ σ‖ = ‖ψ‖ := by
  rw [lvOf_of_ne_zero E h0, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h.nonneg, h.norm_encoded, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-- SVT-7. `‖ψ̃‖ = 1` when `σ ≠ 0` and `‖ψ‖ = 1`. -/
theorem norm_lvOf_of_norm_one (h : IsSingularPair E ψ σ) (h0 : σ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ‖lvOf E ψ σ‖ = 1 := by
  rw [h.norm_lvOf h0, hψ]

/-- SVT-7. `Π̃ U ψ = Π̃ U Π ψ = A ψ = σ ψ̃`. -/
theorem P'_U_apply (h : IsSingularPair E ψ σ) : E.P' (E.U ψ) = (σ : ℂ) • lvOf E ψ σ := by
  calc E.P' (E.U ψ) = E.P' (E.U (E.P ψ)) := by rw [h.P_eq]
    _ = E.encoded ψ := rfl
    _ = (σ : ℂ) • lvOf E ψ σ := h.A_apply

/-- SVT-7. `Π U† ψ̃ = Π U† Π̃ ψ̃ = A† ψ̃ = σ ψ`. -/
theorem P_U_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    E.P ((E.U†) (lvOf E ψ σ)) = (σ : ℂ) • ψ := by
  calc E.P ((E.U†) (lvOf E ψ σ)) = E.P ((E.U†) (E.P' (lvOf E ψ σ))) := by rw [P'_lvOf]
    _ = ((E.encoded)†) (lvOf E ψ σ) := by rw [E.encoded_adjoint]; rfl
    _ = (σ : ℂ) • ψ := h.A_adjoint_lvOf

/-! ### The endpoint `σ = 1` -/

/-- SVT-7 (endpoint). For `σ = 1`, `U ψ = ψ̃` (`‖U ψ‖ = ‖ψ‖ = ‖Π̃ U ψ‖`). -/
theorem U_apply_of_eq_one (h : IsSingularPair E ψ σ) (h1 : σ = 1) : E.U ψ = lvOf E ψ σ := by
  have h0 : σ ≠ 0 := by rw [h1]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP' E.hU (h.norm_lvOf h0) ?_
  rw [h.P'_U_apply, h1, Complex.ofReal_one, one_smul]

/-- SVT-7 (endpoint). For `σ = 1`, `U† ψ̃ = ψ` (`‖U† ψ̃‖ = ‖ψ‖ = ‖Π U† ψ̃‖`). -/
theorem U_adjoint_lvOf_of_eq_one (h : IsSingularPair E ψ σ) (h1 : σ = 1) :
    (E.U†) (lvOf E ψ σ) = ψ := by
  have h0 : σ ≠ 0 := by rw [h1]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP E.U_adjoint_mem_unitary (h.norm_lvOf h0).symm ?_
  rw [h.P_U_adjoint_lvOf, h1, Complex.ofReal_one, one_smul]

/-! ### The frame relations (R1)–(R5) -/

/-- SVT-7 (R1). `U ψ = σ ψ̃ + √(1 - σ²) ψ̃⊥`. -/
theorem U_apply (h : IsSingularPair E ψ σ) :
    E.U ψ = (σ : ℂ) • lvOf E ψ σ + (Real.sqrt (1 - σ ^ 2) : ℂ) • lvtOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · rw [lvtOf, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hlt), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, h.P'_U_apply, add_sub_cancel]
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [ofReal_sqrt_one_sub_sq_eq_zero h1, zero_smul, add_zero, h.U_apply_of_eq_one h1, h1,
      Complex.ofReal_one, one_smul]

/-- SVT-7 (R2). `U† ψ̃ = σ ψ + √(1 - σ²) ψ⊥`. -/
theorem U_adjoint_lvOf (h : IsSingularPair E ψ σ) :
    (E.U†) (lvOf E ψ σ) = (σ : ℂ) • ψ + (Real.sqrt (1 - σ ^ 2) : ℂ) • rvpOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · rw [rvpOf, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero hlt), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, h.P_U_adjoint_lvOf, add_sub_cancel]
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [ofReal_sqrt_one_sub_sq_eq_zero h1, zero_smul, add_zero, h.U_adjoint_lvOf_of_eq_one h1, h1,
      Complex.ofReal_one, one_smul]

/-- SVT-7 (R3). `U ψ⊥ = √(1 - σ²) ψ̃ - σ ψ̃⊥` (from `ψ̃ = U U† ψ̃`). -/
theorem U_rvpOf (h : IsSingularPair E ψ σ) :
    E.U (rvpOf E ψ σ) = (Real.sqrt (1 - σ ^ 2) : ℂ) • lvOf E ψ σ - (σ : ℂ) • lvtOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · have h1 : E.U ((E.U†) (lvOf E ψ σ)) = lvOf E ψ σ := by
      rw [← Module.End.mul_apply, E.U_mul_U_adjoint, Module.End.one_apply]
    rw [h.U_adjoint_lvOf, map_add, map_smul, map_smul, h.U_apply] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hlt) ?_
    have h2 : (Real.sqrt (1 - σ ^ 2) : ℂ) • E.U (rvpOf E ψ σ) =
        lvOf E ψ σ - (σ : ℂ) • ((σ : ℂ) • lvOf E ψ σ +
          (Real.sqrt (1 - σ ^ 2) : ℂ) • lvtOf E ψ σ) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ ^ 2) : ℂ) • E.U (rvpOf E ψ σ) =
      (Real.sqrt (1 - σ ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ ^ 2) : ℂ) • lvOf E ψ σ - (σ : ℂ) • lvtOf E ψ σ)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hlt.le]
    module
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [rvpOf_of_eq_one E h1, lvtOf_of_eq_one E h1, ofReal_sqrt_one_sub_sq_eq_zero h1, map_zero,
      zero_smul, smul_zero, sub_zero]

/-- SVT-7 (R4). `U† ψ̃⊥ = √(1 - σ²) ψ - σ ψ⊥` (from `ψ = U† U ψ`). -/
theorem U_adjoint_lvtOf (h : IsSingularPair E ψ σ) :
    (E.U†) (lvtOf E ψ σ) = (Real.sqrt (1 - σ ^ 2) : ℂ) • ψ - (σ : ℂ) • rvpOf E ψ σ := by
  rcases h.sq_le_one.lt_or_eq with hlt | heq
  · have h1 : (E.U†) (E.U ψ) = ψ := by
      rw [← Module.End.mul_apply, E.U_adjoint_mul_U, Module.End.one_apply]
    rw [h.U_apply, map_add, map_smul, map_smul, h.U_adjoint_lvOf] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero hlt) ?_
    have h2 : (Real.sqrt (1 - σ ^ 2) : ℂ) • (E.U†) (lvtOf E ψ σ) =
        ψ - (σ : ℂ) • ((σ : ℂ) • ψ + (Real.sqrt (1 - σ ^ 2) : ℂ) • rvpOf E ψ σ) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ ^ 2) : ℂ) • (E.U†) (lvtOf E ψ σ) =
      (Real.sqrt (1 - σ ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ ^ 2) : ℂ) • ψ - (σ : ℂ) • rvpOf E ψ σ)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' hlt.le]
    module
  · have h1 := h.eq_one_of_sq_eq_one heq
    rw [lvtOf_of_eq_one E h1, rvpOf_of_eq_one E h1, ofReal_sqrt_one_sub_sq_eq_zero h1, map_zero,
      zero_smul, smul_zero, sub_zero]

/-- SVT-7 (R5). `e^{iφ(2Π-I)} ψ = e^{iφ} ψ`. -/
theorem phaseOp_P_apply (h : IsSingularPair E ψ σ) (φ : ℝ) :
    phaseOp E.P φ ψ = Complex.exp (Complex.I * φ) • ψ :=
  phaseOp_apply_of_proj_eq φ h.P_eq

/-! ### Building a singular pair from an unnormalised eigenvector of `A†A` -/

/-- SVT-7. A nonzero `ψ ∈ ran Π` with `A†A ψ = σ² ψ`, `0 ≤ σ`, is a singular pair: `σ ≤ 1`
follows from `‖A ψ‖ ≤ ‖ψ‖`. -/
theorem mk' (hψ : E.P ψ = ψ) (hσ : 0 ≤ σ) (hG : (E.encoded†) (E.encoded ψ) = ((σ : ℂ) ^ 2) • ψ)
    (hne : ψ ≠ 0) : IsSingularPair E ψ σ := by
  have hsq : ‖E.encoded ψ‖ ^ 2 = σ ^ 2 * ‖ψ‖ ^ 2 := by
    have h1 : inner ℂ ((E.encoded†) (E.encoded ψ)) ψ = inner ℂ (E.encoded ψ) (E.encoded ψ) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [hG, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, map_pow,
      Complex.conj_ofReal] at h1
    have h2 := congrArg Complex.re h1
    simpa [← Complex.ofReal_pow, ← Complex.ofReal_mul] using h2.symm
  have hle : ‖E.encoded ψ‖ ^ 2 ≤ 1 * ‖ψ‖ ^ 2 := by
    rw [one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (E.norm_encoded_apply_le ψ) 2
  have hpos : 0 < ‖ψ‖ ^ 2 := by positivity
  have hσ2 : σ ^ 2 ≤ 1 := le_of_mul_le_mul_right (hsq ▸ hle) hpos
  exact ⟨hψ, hσ, (pow_le_one_iff_of_nonneg hσ two_ne_zero).mp hσ2, hG⟩

end IsSingularPair

/-! ### The induction lemma and the headline -/

section Headline

variable {E : ProjUnitaryEncoding ℋ} {ψ : ℋ} {σ : ℝ}

/-- SVT-7 (induction lemma, GSLW Thm 17 proof, arbitrary singular pair). The alternating
sequence acts on the right singular vector `ψ` as the QSP sequence `seqR Φ σ` acts on the first
standard basis vector, in the `Π`-frame `{ψ, ψ⊥}` for even `Φ.length` and in the `Π̃`-frame
`{ψ̃, ψ̃⊥}` for odd `Φ.length`:
```
U_Φ ψ = (seqR Φ σ)₀₀ ψ + (seqR Φ σ)₁₀ ψ⊥    (Φ.length even)
U_Φ ψ = (seqR Φ σ)₀₀ ψ̃ + (seqR Φ σ)₁₀ ψ̃⊥   (Φ.length odd)
```
-/
theorem altSeq_apply_singular (h : IsSingularPair E ψ σ) (Φ : List ℝ) :
    altSeq E Φ ψ =
      (seqR Φ σ) 0 0 • (if Even Φ.length then ψ else lvOf E ψ σ) +
        (seqR Φ σ) 1 0 • (if Even Φ.length then rvpOf E ψ σ else lvtOf E ψ σ) := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    have hlen : Even (φ :: Φ).length ↔ ¬ Even Φ.length := by
      rw [List.length_cons]
      exact Nat.even_add_one
    rw [altSeq_cons, Module.End.mul_apply, ih, seqR_cons, phaseZ_mul_Rref_mul_apply_zero_zero,
      phaseZ_mul_Rref_mul_apply_one_zero]
    by_cases he : Even Φ.length
    · have he' : ¬ Even (φ :: Φ).length := fun h2 => hlen.mp h2 he
      rw [ite_eq_left he, ite_eq_left he, ite_eq_left he, ite_eq_right he', ite_eq_right he',
        Module.End.mul_apply, map_add, map_smul, map_smul, h.U_apply, h.U_rvpOf]
      simp only [map_add, map_sub, map_smul, phaseOp_P'_lvOf E ψ σ, phaseOp_P'_lvtOf E ψ σ]
      module
    · have he' : Even (φ :: Φ).length := hlen.mpr he
      rw [ite_eq_right he, ite_eq_right he, ite_eq_right he, ite_eq_left he', ite_eq_left he',
        Module.End.mul_apply, map_add, map_smul, map_smul, h.U_adjoint_lvOf, h.U_adjoint_lvtOf]
      simp only [map_add, map_sub, map_smul, h.phaseOp_P_apply, phaseOp_P_rvpOf E ψ σ]
      module

/-- SVT-7 (vector form, odd length, arbitrary singular pair). `Π̃ U_Φ ψ = P_Φ(σ) ψ̃` with
`(P_Φ, Q_Φ) = qspPoly Φ` (GSLW Thm 17 on one singular vector, odd case; for `σ = 0` both sides
vanish). -/
theorem proj_altSeq_apply_singular_odd (h : IsSingularPair E ψ σ) {Φ : List ℝ}
    (hodd : Odd Φ.length) :
    E.P' (altSeq E Φ ψ) = ((qspPoly Φ).1.eval (σ : ℂ)) • lvOf E ψ σ := by
  have hne : ¬ Even Φ.length := Nat.not_even_iff_odd.mpr hodd
  rw [altSeq_apply_singular h, ite_eq_right hne, ite_eq_right hne, map_add, map_smul, map_smul,
    P'_lvOf, P'_lvtOf, smul_zero, add_zero, seqR_apply_zero_zero h.mem_Icc_neg_one_one Φ]

/-- SVT-7 (vector form, even length, arbitrary singular pair). `Π U_Φ ψ = P_Φ(σ) ψ` with
`(P_Φ, Q_Φ) = qspPoly Φ` (GSLW Thm 17 on one singular vector, even case). -/
theorem proj_altSeq_apply_singular_even (h : IsSingularPair E ψ σ) {Φ : List ℝ}
    (heven : Even Φ.length) :
    E.P (altSeq E Φ ψ) = ((qspPoly Φ).1.eval (σ : ℂ)) • ψ := by
  rw [altSeq_apply_singular h, ite_eq_left heven, ite_eq_left heven, map_add, map_smul, map_smul,
    h.P_eq, P_rvpOf, smul_zero, add_zero, seqR_apply_zero_zero h.mem_Icc_neg_one_one Φ]

end Headline

end QSVT.SVT
