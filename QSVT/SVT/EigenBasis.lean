/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Projected
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Eigenbasis of a Hermitian projected unitary encoding (formal-spec SVT-3, steps 1 and 5)

Let `E : HermitianEncoding ℋ` with encoded operator `A = Π U Π` (`E.encoded`, self-adjoint).
This file provides the eigenbasis infrastructure for the eigenvalue transformation SVT-3:

* elementary facts: `A` is symmetric, `A Π = Π A = A`, `‖A x‖ ≤ ‖x‖`, `A` maps `ran Π` into
  itself (`norm_proj_apply_le`, `norm_unitary_apply`, `norm_encoded_apply_le`,
  `range_P_invariant`, `mem_range_P_iff`);
* the restriction `restricted E : ran Π →ₗ ran Π` of `A`, its symmetry, and the spectral
  theorem applied to it: an orthonormal eigenbasis `eigenBasis E` of `ran Π` with real
  eigenvalues `eigenValue E i ∈ [-1, 1]`; the eigenvectors viewed in `ℋ` are `eigenVec E i`
  (`P_eigenVec`, `encoded_eigenVec`, `norm_eigenVec`, `eigenValue_mem_Icc`);
* `aeval_eigenVec`: `p(A) ψᵢ = p(ςᵢ) ψᵢ` for every polynomial `p` (SVT-3 step 5);
* extensionality: two operators agreeing on every `eigenVec E i` and on `ker Π` are equal
  (`sum_repr_eigenVec`, `ext_of_eigenVec`, `ext_mul_P_of_eigenVec`).

## Mathlib facts used

`LinearMap.IsSymmetric.eigenvectorBasis` / `eigenvalues` / `apply_eigenvectorBasis`
(`Mathlib.Analysis.InnerProductSpace.Spectrum`), `LinearMap.IsSymmetric.restrict_invariant`,
`Submodule.innerProductSpace`, `Module.End.aeval_apply_of_hasEigenvector`,
`OrthonormalBasis.sum_repr'`.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Norm bounds for projections and unitaries -/

/-- SVT-3. A projection is a contraction: `‖Π x‖ ≤ ‖x‖`. -/
theorem norm_proj_apply_le {P : L ℋ} (hP : IsProjective P) (x : ℋ) : ‖P x‖ ≤ ‖x‖ := by
  have key : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    rw [← LinearMap.adjoint_inner_right P x (P x), hP.adjoint_eq, ← Module.End.mul_apply,
      hP.mul_self]
  have h1 : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ :=
    calc ‖P x‖ ^ 2 = RCLike.re (inner ℂ (P x) (P x)) := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = RCLike.re (inner ℂ x (P x)) := by rw [key]
      _ ≤ ‖inner ℂ x (P x)‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖P x‖ := norm_inner_le_norm x (P x)
  rcases (norm_nonneg (P x)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg x
  · exact le_of_mul_le_mul_right (by rwa [sq] at h1) h0

/-- SVT-3. A unitary preserves norms: `‖U x‖ = ‖x‖`. -/
theorem norm_unitary_apply {U : L ℋ} (hU : U ∈ unitary (L ℋ)) (x : ℋ) : ‖U x‖ = ‖x‖ := by
  have key : inner ℂ (U x) (U x) = inner ℂ x x := by
    rw [← LinearMap.adjoint_inner_right U x (U x), ← Module.End.mul_apply,
      ← LinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hU, Module.End.one_apply]
  have h := congrArg RCLike.re key
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), inner_self_eq_norm_sq (𝕜 := ℂ)] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- SVT-3. Membership in the range of a projection: `x ∈ ran Π ↔ Π x = x`. -/
theorem mem_range_proj_iff {P : L ℋ} (hP : IsProjective P) (x : ℋ) :
    x ∈ LinearMap.range P ↔ P x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Module.End.mul_apply, hP.mul_self]
  · intro h
    exact ⟨x, h⟩

section HermitianEncoding

variable (E : HermitianEncoding ℋ)

/-! ### Basic facts about the encoded operator `A = Π U Π` -/

/-- SVT-3. The encoded operator of a Hermitian encoding is symmetric. -/
theorem encoded_isSymmetric : LinearMap.IsSymmetric E.encoded :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr E.encoded_selfAdjoint

/-- SVT-3. `A Π = A`. -/
theorem encoded_mul_P : E.encoded * E.P = E.encoded := E.encoded_mul_P

/-- SVT-3. `Π A = A`. -/
theorem P_mul_encoded : E.P * E.encoded = E.encoded := by
  have h := E.P'_mul_encoded
  rwa [E.P'_eq] at h

/-- SVT-3. `‖A x‖ ≤ ‖x‖` (the encoded operator is a contraction). -/
theorem norm_encoded_apply_le (x : ℋ) : ‖E.encoded x‖ ≤ ‖x‖ := by
  rw [E.encoded_eq]
  calc ‖(E.P * E.U * E.P) x‖ = ‖E.P (E.U (E.P x))‖ := rfl
    _ ≤ ‖E.U (E.P x)‖ := norm_proj_apply_le E.hP _
    _ = ‖E.P x‖ := norm_unitary_apply E.hU _
    _ ≤ ‖x‖ := norm_proj_apply_le E.hP x

/-- SVT-3. `A x ∈ ran Π`. -/
theorem encoded_mem_range (x : ℋ) : E.encoded x ∈ LinearMap.range E.P :=
  ⟨E.encoded x, by rw [← Module.End.mul_apply, P_mul_encoded]⟩

/-- SVT-3. `ran Π` is invariant under `A`. -/
theorem range_P_invariant : ∀ x ∈ LinearMap.range E.P, E.encoded x ∈ LinearMap.range E.P :=
  fun x _ => encoded_mem_range E x

/-- SVT-3. `x ∈ ran Π ↔ Π x = x`. -/
theorem mem_range_P_iff (x : ℋ) : x ∈ LinearMap.range E.P ↔ E.P x = x :=
  mem_range_proj_iff E.hP x

/-! ### The eigenbasis of `A` on `ran Π` -/

/-- SVT-3. The subspace `ran Π` of `ℋ` (a finite-dimensional inner product space via
`Submodule.innerProductSpace`). -/
abbrev rangeP : Submodule ℂ ℋ := LinearMap.range E.P

/-- SVT-3. The restriction `A|_{ran Π} : ran Π → ran Π`. -/
def restricted : rangeP E →ₗ[ℂ] rangeP E :=
  (E.encoded).restrict (range_P_invariant E)

@[simp] theorem coe_restricted_apply (v : rangeP E) : (restricted E v : ℋ) = E.encoded v := rfl

/-- SVT-3. `A|_{ran Π}` is symmetric. -/
theorem restricted_isSymmetric : LinearMap.IsSymmetric (restricted E) :=
  (encoded_isSymmetric E).restrict_invariant (range_P_invariant E)

/-- SVT-3 (step 1). An orthonormal eigenbasis `{ψᵢ}` of `A|_{ran Π}`
(`LinearMap.IsSymmetric.eigenvectorBasis`). -/
noncomputable def eigenBasis :
    OrthonormalBasis (Fin (Module.finrank ℂ (rangeP E))) ℂ (rangeP E) :=
  (restricted_isSymmetric E).eigenvectorBasis rfl

/-- SVT-3 (step 1). The real eigenvalue `ςᵢ` of `A` on `ψᵢ`. -/
noncomputable def eigenValue (i : Fin (Module.finrank ℂ (rangeP E))) : ℝ :=
  (restricted_isSymmetric E).eigenvalues rfl i

/-- SVT-3 (step 1). The eigenvector `ψᵢ`, viewed as a vector of `ℋ`. -/
noncomputable def eigenVec (i : Fin (Module.finrank ℂ (rangeP E))) : ℋ :=
  (eigenBasis E i : ℋ)

/-- SVT-3. `ψᵢ ∈ ran Π`. -/
theorem eigenVec_mem (i : Fin (Module.finrank ℂ (rangeP E))) :
    eigenVec E i ∈ LinearMap.range E.P :=
  (eigenBasis E i).2

/-- SVT-3. `Π ψᵢ = ψᵢ`. -/
theorem P_eigenVec (i : Fin (Module.finrank ℂ (rangeP E))) : E.P (eigenVec E i) = eigenVec E i :=
  (mem_range_P_iff E _).mp (eigenVec_mem E i)

/-- SVT-3. `A ψᵢ = ςᵢ ψᵢ`. -/
theorem encoded_eigenVec (i : Fin (Module.finrank ℂ (rangeP E))) :
    E.encoded (eigenVec E i) = (eigenValue E i : ℂ) • eigenVec E i := by
  have h : restricted E (eigenBasis E i) = (eigenValue E i : ℂ) • eigenBasis E i :=
    (restricted_isSymmetric E).apply_eigenvectorBasis rfl i
  have h' := congrArg Subtype.val h
  rw [Submodule.coe_smul, coe_restricted_apply] at h'
  exact h'

/-- SVT-3. `‖ψᵢ‖ = 1`. -/
theorem norm_eigenVec (i : Fin (Module.finrank ℂ (rangeP E))) : ‖eigenVec E i‖ = 1 := by
  rw [eigenVec, Submodule.norm_coe]
  exact (eigenBasis E).orthonormal.1 i

/-- SVT-3. `ψᵢ ≠ 0`. -/
theorem eigenVec_ne_zero (i : Fin (Module.finrank ℂ (rangeP E))) : eigenVec E i ≠ 0 := by
  intro h
  have h1 := norm_eigenVec E i
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- SVT-3. `|ςᵢ| ≤ 1`, from `‖A ψᵢ‖ ≤ ‖ψᵢ‖`. -/
theorem abs_eigenValue_le_one (i : Fin (Module.finrank ℂ (rangeP E))) : |eigenValue E i| ≤ 1 := by
  have h := norm_encoded_apply_le E (eigenVec E i)
  rwa [encoded_eigenVec, norm_smul, norm_eigenVec, Complex.norm_real, Real.norm_eq_abs,
    mul_one] at h

/-- SVT-3 (step 1). `ςᵢ ∈ [-1, 1]`. -/
theorem eigenValue_mem_Icc (i : Fin (Module.finrank ℂ (rangeP E))) :
    eigenValue E i ∈ Set.Icc (-1 : ℝ) 1 :=
  Set.mem_Icc.mpr (abs_le.mp (abs_eigenValue_le_one E i))

/-- SVT-3. `ψᵢ` is an eigenvector of `A` (in the sense of `Module.End.HasEigenvector`). -/
theorem hasEigenvector_eigenVec (i : Fin (Module.finrank ℂ (rangeP E))) :
    Module.End.HasEigenvector E.encoded (eigenValue E i : ℂ) (eigenVec E i) :=
  ⟨Module.End.mem_eigenspace_iff.mpr (encoded_eigenVec E i), eigenVec_ne_zero E i⟩

/-- SVT-3 (step 5). `p(A) ψᵢ = p(ςᵢ) ψᵢ` for every polynomial `p`. -/
theorem aeval_eigenVec (p : Polynomial ℂ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    Polynomial.aeval E.encoded p (eigenVec E i) = p.eval (eigenValue E i : ℂ) • eigenVec E i :=
  Module.End.aeval_apply_of_hasEigenvector (hasEigenvector_eigenVec E i)

/-! ### Extensionality through the eigenbasis -/

/-- SVT-3. Expansion of a vector of `ran Π` in the eigenbasis: `x = ∑ᵢ ⟪ψᵢ, x⟫ ψᵢ`. -/
theorem sum_repr_eigenVec (x : ℋ) (hx : E.P x = x) :
    x = ∑ i, inner ℂ (eigenVec E i) x • eigenVec E i := by
  have h := congrArg Subtype.val
    ((eigenBasis E).sum_repr' ⟨x, (mem_range_P_iff E x).mpr hx⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul, Submodule.coe_inner] at h
  exact h.symm

/-- SVT-3 (step 5). Two operators agreeing on every eigenvector `ψᵢ` and on `ker Π` are equal. -/
theorem ext_of_eigenVec {T S : L ℋ} (h1 : ∀ i, T (eigenVec E i) = S (eigenVec E i))
    (h2 : ∀ x, E.P x = 0 → T x = S x) : T = S := by
  ext x
  have hsplit : ∀ R : L ℋ, R x = R (E.P x) + R ((1 - E.P) x) := fun R => by
    rw [← map_add, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
  have hPx : T (E.P x) = S (E.P x) := by
    have hP : E.P (E.P x) = E.P x := by rw [← Module.End.mul_apply, E.hP.mul_self]
    rw [sum_repr_eigenVec E (E.P x) hP, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h1 i]
  have hQx : T ((1 - E.P) x) = S ((1 - E.P) x) :=
    h2 _ (by rw [← Module.End.mul_apply, E.hP.mul_one_sub, LinearMap.zero_apply])
  rw [hsplit T, hsplit S, hPx, hQx]

/-- SVT-3 (step 5). Two operators agreeing on every eigenvector `ψᵢ` agree after `Π`:
`T Π = S Π`. -/
theorem ext_mul_P_of_eigenVec {T S : L ℋ} (h : ∀ i, T (eigenVec E i) = S (eigenVec E i)) :
    T * E.P = S * E.P := by
  refine ext_of_eigenVec E (fun i => ?_) (fun x hx => ?_)
  · rw [Module.End.mul_apply, Module.End.mul_apply, P_eigenVec, h i]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hx, map_zero, map_zero]

end HermitianEncoding

end QSVT.SVT
