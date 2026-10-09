/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.SVTransform

/-!
# Minimal singular value decomposition of a projected unitary encoding (formal-spec SVT-6)

Let `E : ProjUnitaryEncoding ℋ` with encoded operator `A = Π̃ U Π` (`E.encoded`). Mathlib has
no SVD, so we build the little that QSVT needs from the spectral theorem for the Gram operator
`G = A†A` (GSLW Def 11, "SVD-free" formulation of the specification):

* `G` is symmetric and maps `ran Π` into itself (`gram_isSymmetric`, `gram_range_invariant`),
  so the spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`) applied to the restriction
  `gramRestricted E : ran Π → ran Π` gives an orthonormal basis `rv E i` of `ran Π` (the *right
  singular vectors*) with `G (rv i) = σsq i • rv i`;
* `σsq i = ‖A (rv i)‖² ∈ [0, 1]` (`σsq_eq_norm_sq`), and the *singular values* are
  `σ i = √(σsq i) = ‖A (rv i)‖ ∈ [0, 1]` (`σ_eq_norm`, `σ_mem_Icc`);
* the *left singular vectors* `lv i = A (rv i) / σ i` (and `lv i = 0` when `σ i = 0`) lie in
  `ran Π̃`, are unit vectors when `σ i ≠ 0`, and satisfy the two defining relations
  `A (rv i) = σ i • lv i` (`A_rv`) and `A† (lv i) = σ i • rv i` (`A_adjoint_lv`) for *every* `i`;
* the singular value transformation of SVT-5 acts on the singular vectors as GSLW Def 16 says:
  `svTransform p E (rv i) = p(σ i) • rv i` for even `p` and `= p(σ i) • lv i` for odd `p`
  (`svTransform_apply_rv_of_isEven`, `svTransform_apply_rv_of_isOdd`);
* extensionality through the basis: two operators agreeing on every `rv i` and on `ker Π` are
  equal (`ext_of_rv`, `ext_mul_P_of_rv`).

This is the general-encoding counterpart of `QSVT.SVT.EigenBasis` (which treats `A` itself for a
Hermitian encoding); the proofs are the same with `A†A` in place of `A`.

## Mathlib facts used

`LinearMap.IsSymmetric.eigenvectorBasis` / `eigenvalues` / `apply_eigenvectorBasis`,
`LinearMap.IsSymmetric.restrict_invariant`, `IsSelfAdjoint.star_mul_self`,
`Module.End.aeval_apply_of_hasEigenvector`, `OrthonormalBasis.sum_repr'`,
`orthonormal_iff_ite`, `inner_self_eq_norm_sq_to_K`, `Real.sq_sqrt`, `Real.sqrt_sq`.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- SVT-6. `‖A x‖ ≤ ‖x‖` for every projected unitary encoding (`A = Π̃ U Π` is a product of
two contractions and a unitary). -/
theorem _root_.QSVT.Encoding.ProjUnitaryEncoding.norm_encoded_apply_le
    (E : ProjUnitaryEncoding ℋ) (x : ℋ) : ‖E.encoded x‖ ≤ ‖x‖ :=
  calc ‖E.encoded x‖ = ‖E.P' (E.U (E.P x))‖ := rfl
    _ ≤ ‖E.U (E.P x)‖ := norm_proj_apply_le E.hP' _
    _ = ‖E.P x‖ := norm_unitary_apply E.hU _
    _ ≤ ‖x‖ := norm_proj_apply_le E.hP x

section Gram

variable (E : ProjUnitaryEncoding ℋ)

/-! ### The Gram operator `A†A` on `ran Π` -/

/-- SVT-6. The Gram operator `A†A` is symmetric. -/
theorem gram_isSymmetric : LinearMap.IsSymmetric (E.encoded† * E.encoded) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (IsSelfAdjoint.star_mul_self E.encoded)

/-- SVT-6. `Π A†A = A†A`. -/
theorem P_mul_gram : E.P * (E.encoded† * E.encoded) = E.encoded† * E.encoded := by
  rw [← mul_assoc, P_mul_encoded_adjoint]

/-- SVT-6. `A†A x ∈ ran Π`. -/
theorem gram_mem_range (x : ℋ) : (E.encoded† * E.encoded) x ∈ LinearMap.range E.P :=
  ⟨(E.encoded† * E.encoded) x, by rw [← Module.End.mul_apply, P_mul_gram]⟩

/-- SVT-6. `ran Π` is invariant under `A†A`. -/
theorem gram_range_invariant :
    ∀ x ∈ LinearMap.range E.P, (E.encoded† * E.encoded) x ∈ LinearMap.range E.P :=
  fun x _ => gram_mem_range E x

/-- SVT-6. The input subspace `ran Π` of the encoding (a finite-dimensional inner product space
via `Submodule.innerProductSpace`). -/
abbrev inputSpace : Submodule ℂ ℋ := LinearMap.range E.P

/-- SVT-6. The index type of the singular vectors: `Fin (dim ran Π)`. -/
abbrev svIndex : Type := Fin (Module.finrank ℂ (inputSpace E))

/-- SVT-6. The restriction `A†A|_{ran Π} : ran Π → ran Π`. -/
noncomputable def gramRestricted : inputSpace E →ₗ[ℂ] inputSpace E :=
  (E.encoded† * E.encoded).restrict (gram_range_invariant E)

@[simp] theorem coe_gramRestricted_apply (v : inputSpace E) :
    (gramRestricted E v : ℋ) = (E.encoded† * E.encoded) v := rfl

/-- SVT-6. `A†A|_{ran Π}` is symmetric. -/
theorem gramRestricted_isSymmetric : LinearMap.IsSymmetric (gramRestricted E) :=
  (gram_isSymmetric E).restrict_invariant (gram_range_invariant E)

/-! ### Right singular vectors and singular values -/

/-- SVT-6. An orthonormal eigenbasis of `A†A|_{ran Π}`: the right singular vectors of `A`
(`LinearMap.IsSymmetric.eigenvectorBasis`). -/
noncomputable def rvBasis : OrthonormalBasis (svIndex E) ℂ (inputSpace E) :=
  (gramRestricted_isSymmetric E).eigenvectorBasis rfl

/-- SVT-6. The eigenvalue `σᵢ²` of `A†A` on the `i`-th right singular vector. -/
noncomputable def σsq (i : svIndex E) : ℝ :=
  (gramRestricted_isSymmetric E).eigenvalues rfl i

/-- SVT-6. The `i`-th right singular vector `ψᵢ ∈ ran Π`, viewed in `ℋ`. -/
noncomputable def rv (i : svIndex E) : ℋ :=
  (rvBasis E i : ℋ)

/-- SVT-6. `ψᵢ ∈ ran Π`. -/
theorem rv_mem (i : svIndex E) : rv E i ∈ LinearMap.range E.P :=
  (rvBasis E i).2

/-- SVT-6. `Π ψᵢ = ψᵢ`. -/
theorem P_rv (i : svIndex E) : E.P (rv E i) = rv E i :=
  (mem_range_proj_iff E.hP _).mp (rv_mem E i)

/-- SVT-6. `A†A ψᵢ = σᵢ² ψᵢ`. -/
theorem gram_rv (i : svIndex E) :
    (E.encoded† * E.encoded) (rv E i) = (σsq E i : ℂ) • rv E i := by
  have h : gramRestricted E (rvBasis E i) = (σsq E i : ℂ) • rvBasis E i :=
    (gramRestricted_isSymmetric E).apply_eigenvectorBasis rfl i
  have h' := congrArg Subtype.val h
  rw [Submodule.coe_smul, coe_gramRestricted_apply] at h'
  exact h'

/-- SVT-6. `‖ψᵢ‖ = 1`. -/
theorem norm_rv (i : svIndex E) : ‖rv E i‖ = 1 := by
  rw [rv, Submodule.norm_coe]
  exact (rvBasis E).orthonormal.1 i

/-- SVT-6. `ψᵢ ≠ 0`. -/
theorem rv_ne_zero (i : svIndex E) : rv E i ≠ 0 := by
  intro h
  have h1 := norm_rv E i
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- SVT-6. Orthonormality of the right singular vectors: `⟪ψᵢ, ψⱼ⟫ = δᵢⱼ`. -/
theorem inner_rv_rv (i j : svIndex E) :
    inner ℂ (rv E i) (rv E j) = if i = j then (1 : ℂ) else 0 := by
  have h := orthonormal_iff_ite.mp (rvBasis E).orthonormal i j
  rwa [Submodule.coe_inner] at h

/-- SVT-6. `ψᵢ` is an eigenvector of `A†A` with eigenvalue `σᵢ²`. -/
theorem hasEigenvector_rv (i : svIndex E) :
    Module.End.HasEigenvector (E.encoded† * E.encoded) (σsq E i : ℂ) (rv E i) :=
  ⟨Module.End.mem_eigenspace_iff.mpr (gram_rv E i), rv_ne_zero E i⟩

/-- SVT-6 (positivity). `σᵢ² = ‖A ψᵢ‖²`, from `⟪A†A ψᵢ, ψᵢ⟫ = ⟪A ψᵢ, A ψᵢ⟫`. -/
theorem σsq_eq_norm_sq (i : svIndex E) : σsq E i = ‖E.encoded (rv E i)‖ ^ 2 := by
  have h1 : inner ℂ ((E.encoded† * E.encoded) (rv E i)) (rv E i) =
      inner ℂ (E.encoded (rv E i)) (E.encoded (rv E i)) := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  rw [gram_rv, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_rv,
    Complex.conj_ofReal] at h1
  norm_num at h1
  exact_mod_cast h1

/-- SVT-6. `0 ≤ σᵢ²`. -/
theorem σsq_nonneg (i : svIndex E) : 0 ≤ σsq E i := by
  rw [σsq_eq_norm_sq]
  positivity

/-- SVT-6. `σᵢ² ≤ 1`, from `‖A ψᵢ‖ ≤ ‖ψᵢ‖ = 1`. -/
theorem σsq_le_one (i : svIndex E) : σsq E i ≤ 1 := by
  rw [σsq_eq_norm_sq]
  have h := E.norm_encoded_apply_le (rv E i)
  rw [norm_rv] at h
  exact pow_le_one₀ (norm_nonneg _) h

/-- SVT-6. The `i`-th singular value `σᵢ = √(σᵢ²)`. -/
noncomputable def σ (i : svIndex E) : ℝ :=
  Real.sqrt (σsq E i)

/-- SVT-6. `0 ≤ σᵢ`. -/
theorem σ_nonneg (i : svIndex E) : 0 ≤ σ E i :=
  Real.sqrt_nonneg _

/-- SVT-6. `σᵢ ^ 2 = σᵢ²` (the eigenvalue of `A†A`). -/
theorem σ_sq (i : svIndex E) : σ E i ^ 2 = σsq E i :=
  Real.sq_sqrt (σsq_nonneg E i)

/-- SVT-6. `(σᵢ : ℂ) ^ 2 = (σᵢ² : ℂ)`. -/
theorem ofReal_σ_sq (i : svIndex E) : (σ E i : ℂ) ^ 2 = (σsq E i : ℂ) := by
  rw [← Complex.ofReal_pow, σ_sq]

/-- SVT-6. `σᵢ = ‖A ψᵢ‖`. -/
theorem σ_eq_norm (i : svIndex E) : σ E i = ‖E.encoded (rv E i)‖ := by
  rw [σ, σsq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- SVT-6. `σᵢ ≤ 1`. -/
theorem σ_le_one (i : svIndex E) : σ E i ≤ 1 := by
  rw [σ_eq_norm]
  have h := E.norm_encoded_apply_le (rv E i)
  rwa [norm_rv] at h

/-- SVT-6. `σᵢ ∈ [0, 1]`. -/
theorem σ_mem_Icc (i : svIndex E) : σ E i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨σ_nonneg E i, σ_le_one E i⟩

/-- SVT-6. `σᵢ ∈ [-1, 1]` (the form needed by the QSP evaluation theorem QSP-3). -/
theorem σ_mem_Icc_neg_one_one (i : svIndex E) : σ E i ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith [σ_nonneg E i], σ_le_one E i⟩

/-- SVT-6. `σᵢ ^ 2 ≤ 1`. -/
theorem σ_sq_le_one (i : svIndex E) : σ E i ^ 2 ≤ 1 := by
  rw [σ_sq]
  exact σsq_le_one E i

/-- SVT-6. `σᵢ ^ 2 = 1 → σᵢ = 1` (as `σᵢ ≥ 0`). -/
theorem σ_eq_one_of_sq_eq_one {i : svIndex E} (h : σ E i ^ 2 = 1) : σ E i = 1 :=
  (pow_eq_one_iff_of_nonneg (σ_nonneg E i) two_ne_zero).mp h

/-- SVT-6. `A ψᵢ = 0` when `σᵢ = 0`. -/
theorem encoded_rv_eq_zero_of_σ_eq_zero {i : svIndex E} (h : σ E i = 0) :
    E.encoded (rv E i) = 0 := by
  rw [σ_eq_norm] at h
  exact norm_eq_zero.mp h

/-! ### Left singular vectors -/

/-- SVT-6. The `i`-th left singular vector `ψ̃ᵢ = A ψᵢ / σᵢ` (GSLW Def 11), set to `0` when
`σᵢ = 0` (then `A ψᵢ = 0` and there is no canonical choice; `0` keeps `A ψᵢ = σᵢ ψ̃ᵢ` true). -/
noncomputable def lv (i : svIndex E) : ℋ :=
  if σ E i = 0 then 0 else ((σ E i : ℂ)⁻¹) • E.encoded (rv E i)

/-- SVT-6. `ψ̃ᵢ = 0` when `σᵢ = 0`. -/
theorem lv_of_σ_eq_zero {i : svIndex E} (h : σ E i = 0) : lv E i = 0 := by
  rw [lv, ite_eq_left h]

/-- SVT-6. `ψ̃ᵢ = σᵢ⁻¹ A ψᵢ` when `σᵢ ≠ 0`. -/
theorem lv_of_σ_ne_zero {i : svIndex E} (h : σ E i ≠ 0) :
    lv E i = ((σ E i : ℂ)⁻¹) • E.encoded (rv E i) := by
  rw [lv, ite_eq_right h]

/-- SVT-6 (defining relation). `A ψᵢ = σᵢ ψ̃ᵢ`, for every `i`. -/
theorem A_rv (i : svIndex E) : E.encoded (rv E i) = (σ E i : ℂ) • lv E i := by
  by_cases h : σ E i = 0
  · rw [lv_of_σ_eq_zero E h, encoded_rv_eq_zero_of_σ_eq_zero E h, smul_zero]
  · rw [lv_of_σ_ne_zero E h, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h), one_smul]

/-- SVT-6. `Π̃ ψ̃ᵢ = ψ̃ᵢ` (`ψ̃ᵢ ∈ ran Π̃`). -/
theorem P'_lv (i : svIndex E) : E.P' (lv E i) = lv E i := by
  by_cases h : σ E i = 0
  · rw [lv_of_σ_eq_zero E h, map_zero]
  · rw [lv_of_σ_ne_zero E h, map_smul, ← Module.End.mul_apply, E.P'_mul_encoded]

/-- SVT-6 (defining relation). `A† ψ̃ᵢ = σᵢ ψᵢ`, for every `i` (from `A†A ψᵢ = σᵢ² ψᵢ`). -/
theorem A_adjoint_lv (i : svIndex E) : (E.encoded†) (lv E i) = (σ E i : ℂ) • rv E i := by
  by_cases h : σ E i = 0
  · rw [lv_of_σ_eq_zero E h, map_zero, h, Complex.ofReal_zero, zero_smul]
  · have hc : (σ E i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    rw [lv_of_σ_ne_zero E h, map_smul, ← Module.End.mul_apply, gram_rv, ← ofReal_σ_sq, smul_smul,
      sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- SVT-6. `‖ψ̃ᵢ‖ = 1` when `σᵢ ≠ 0`. -/
theorem norm_lv {i : svIndex E} (h : σ E i ≠ 0) : ‖lv E i‖ = 1 := by
  rw [lv_of_σ_ne_zero E h, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (σ_nonneg E i), ← σ_eq_norm, inv_mul_cancel₀ h]

/-- SVT-6. Orthonormality of the left singular vectors with nonzero singular values:
`⟪ψ̃ᵢ, ψ̃ⱼ⟫ = δᵢⱼ` (from `⟪A ψᵢ, A ψⱼ⟫ = ⟪ψᵢ, A†A ψⱼ⟫ = σⱼ² ⟪ψᵢ, ψⱼ⟫`). -/
theorem inner_lv_lv {i j : svIndex E} (hi : σ E i ≠ 0) (hj : σ E j ≠ 0) :
    inner ℂ (lv E i) (lv E j) = if i = j then (1 : ℂ) else 0 := by
  have hA : inner ℂ (E.encoded (rv E i)) (E.encoded (rv E j)) =
      (σ E j : ℂ) ^ 2 * inner ℂ (rv E i) (rv E j) := by
    rw [← LinearMap.adjoint_inner_right, ← Module.End.mul_apply, gram_rv, inner_smul_right,
      ofReal_σ_sq]
  rw [lv_of_σ_ne_zero E hi, lv_of_σ_ne_zero E hj, inner_smul_left, inner_smul_right, hA,
    inner_rv_rv, map_inv₀, Complex.conj_ofReal]
  split_ifs with hij
  · subst hij
    have hc : (σ E i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
    field_simp
  · simp

/-! ### The singular value transformation on singular vectors -/

/-- SVT-6. `R(A†A) ψᵢ = R(σᵢ²) ψᵢ` for every polynomial `R`. -/
theorem aeval_gram_rv (R : ℂ[X]) (i : svIndex E) :
    aeval (E.encoded† * E.encoded) R (rv E i) = R.eval ((σ E i : ℂ) ^ 2) • rv E i := by
  rw [Module.End.aeval_apply_of_hasEigenvector (hasEigenvector_rv E i), ofReal_σ_sq]

/-- SVT-6 (GSLW Def 16, even case). For even `p`, `svTransform p E ψᵢ = p(σᵢ) ψᵢ`. -/
theorem svTransform_apply_rv_of_isEven {p : ℂ[X]} (hp : IsEven p) (i : svIndex E) :
    svTransform p E (rv E i) = p.eval (σ E i : ℂ) • rv E i := by
  rw [svTransform_of_isEven E hp, Module.End.mul_apply, Module.End.mul_apply, P_rv, aeval_gram_rv,
    map_smul, P_rv, hp.eval_eq]

/-- SVT-6 (GSLW Def 16, odd case). For odd `p`, `svTransform p E ψᵢ = p(σᵢ) ψ̃ᵢ` (for `σᵢ = 0`
both sides vanish, as `p(0) = 0` and `ψ̃ᵢ = 0`). -/
theorem svTransform_apply_rv_of_isOdd {p : ℂ[X]} (hp : IsOdd p) (i : svIndex E) :
    svTransform p E (rv E i) = p.eval (σ E i : ℂ) • lv E i := by
  rw [svTransform_of_isOdd E hp, Module.End.mul_apply, aeval_gram_rv, map_smul, A_rv, smul_smul,
    hp.eval_eq, mul_comm]

/-! ### Extensionality through the right singular vectors -/

/-- SVT-6. Expansion of a vector of `ran Π` in the right singular vectors:
`x = ∑ᵢ ⟪ψᵢ, x⟫ ψᵢ`. -/
theorem sum_repr_rv (x : ℋ) (hx : E.P x = x) :
    x = ∑ i, inner ℂ (rv E i) x • rv E i := by
  have h := congrArg Subtype.val
    ((rvBasis E).sum_repr' ⟨x, (mem_range_proj_iff E.hP x).mpr hx⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul, Submodule.coe_inner] at h
  exact h.symm

/-- SVT-6. Two operators agreeing on every right singular vector `ψᵢ` and on `ker Π` are
equal. -/
theorem ext_of_rv {T S : L ℋ} (h1 : ∀ i, T (rv E i) = S (rv E i))
    (h2 : ∀ x, E.P x = 0 → T x = S x) : T = S := by
  ext x
  have hsplit : ∀ R : L ℋ, R x = R (E.P x) + R ((1 - E.P) x) := fun R => by
    rw [← map_add, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
  have hPx : T (E.P x) = S (E.P x) := by
    have hP : E.P (E.P x) = E.P x := by rw [← Module.End.mul_apply, E.hP.mul_self]
    rw [sum_repr_rv E (E.P x) hP, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h1 i]
  have hQx : T ((1 - E.P) x) = S ((1 - E.P) x) :=
    h2 _ (by rw [← Module.End.mul_apply, E.hP.mul_one_sub, LinearMap.zero_apply])
  rw [hsplit T, hsplit S, hPx, hQx]

/-- SVT-6. Two operators agreeing on every right singular vector `ψᵢ` agree after `Π`:
`T Π = S Π`. -/
theorem ext_mul_P_of_rv {T S : L ℋ} (h : ∀ i, T (rv E i) = S (rv E i)) :
    T * E.P = S * E.P := by
  refine ext_of_rv E (fun i => ?_) (fun x hx => ?_)
  · rw [Module.End.mul_apply, Module.End.mul_apply, P_rv, h i]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hx, map_zero, map_zero]

end Gram

end QSVT.SVT
