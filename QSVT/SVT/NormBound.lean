/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.EigenBasis
import QSVT.Polynomial.SupNorm

/-!
# Norm bound for polynomials of a Hermitian encoding (formal-spec SVT-4)

Let `E : HermitianEncoding ℋ` with encoded operator `A = Π U Π` and let `p : ℂ[X]`.
Since `A` is self-adjoint with spectrum in `[-1, 1]` on `ran Π`, the operator `p(A) Π` is
bounded by the sup norm of `p` on `[-1, 1]`:

* `norm_aeval_apply_le`: `‖p(A) x‖ ≤ ‖p‖_∞ ‖x‖` for `x ∈ ran Π`;
* `norm_aeval_mul_P_apply_le`: `‖(p(A) Π) x‖ ≤ ‖p‖_∞ ‖x‖` for all `x`;
* `norm_aeval_sub_mul_P_apply_le`: `‖(p(A) Π - q(A) Π) x‖ ≤ ‖p - q‖_∞ ‖x‖`;
* `opNorm_aeval_mul_P_le`: the operator-norm form `‖p(A) Π‖ ≤ ‖p‖_∞`, stated through
  `LinearMap.toContinuousLinearMap` (finite dimension).

The proof expands `x` in the orthonormal eigenbasis `ψᵢ` of `A|_{ran Π}` (`QSVT.SVT.EigenBasis`):
`p(A) x = ∑ᵢ ⟪ψᵢ, x⟫ p(ςᵢ) ψᵢ`, Parseval gives `‖p(A) x‖² = ∑ᵢ ‖⟪ψᵢ, x⟫‖² ‖p(ςᵢ)‖²`, and
`‖p(ςᵢ)‖ ≤ ‖p‖_∞` since `ςᵢ ∈ [-1, 1]`.

## Mathlib facts used

`Orthonormal.comp_linearIsometry` (with `Submodule.subtypeₗᵢ`), `Orthonormal.inner_sum`,
`inner_self_eq_norm_sq`, `RCLike.conj_mul`, `le_of_sq_le_sq`, `pow_le_pow_left₀`,
`ContinuousLinearMap.opNorm_le_bound`, `LinearMap.coe_toContinuousLinearMap'`.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

section HermitianEncoding

variable (E : HermitianEncoding ℋ)

/-! ### Parseval in the eigenbasis -/

/-- SVT-4. The eigenvectors `ψᵢ`, viewed in `ℋ`, form an orthonormal family. -/
theorem orthonormal_eigenVec : Orthonormal ℂ (eigenVec E) :=
  (eigenBasis E).orthonormal.comp_linearIsometry (rangeP E).subtypeₗᵢ

/-- SVT-4. Parseval: `‖∑ᵢ cᵢ ψᵢ‖² = ∑ᵢ ‖cᵢ‖²`. -/
theorem norm_sum_smul_eigenVec_sq (c : Fin (Module.finrank ℂ (rangeP E)) → ℂ) :
    ‖∑ i, c i • eigenVec E i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), (orthonormal_eigenVec E).inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- SVT-4. `p(A) x = ∑ᵢ ⟪ψᵢ, x⟫ p(ςᵢ) ψᵢ` for `x ∈ ran Π`. -/
theorem aeval_apply_eq_sum (p : ℂ[X]) (x : ℋ) (hx : E.P x = x) :
    aeval E.encoded p x =
      ∑ i, (inner ℂ (eigenVec E i) x * p.eval (eigenValue E i : ℂ)) • eigenVec E i := by
  conv_lhs => rw [sum_repr_eigenVec E x hx]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, aeval_eigenVec, smul_smul]

/-! ### The norm bound -/

/-- SVT-4. `‖p(A) x‖ ≤ ‖p‖_∞ ‖x‖` for `x ∈ ran Π`, where `‖p‖_∞` is the sup norm of `p` on
`[-1, 1]` (`QSVT.Poly.supNorm`). -/
theorem norm_aeval_apply_le (p : ℂ[X]) (x : ℋ) (hx : E.P x = x) :
    ‖aeval E.encoded p x‖ ≤ supNorm p * ‖x‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (supNorm_nonneg p) (norm_nonneg x))
  rw [aeval_apply_eq_sum E p x hx, norm_sum_smul_eigenVec_sq, mul_pow]
  conv_rhs => rw [sum_repr_eigenVec E x hx, norm_sum_smul_eigenVec_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (sq_nonneg _)
  exact norm_eval_le_supNorm p (eigenValue_mem_Icc E i)

/-- SVT-4. `‖(p(A) Π) x‖ ≤ ‖p‖_∞ ‖x‖` for every `x`. -/
theorem norm_aeval_mul_P_apply_le (p : ℂ[X]) (x : ℋ) :
    ‖(aeval E.encoded p * E.P) x‖ ≤ supNorm p * ‖x‖ := by
  rw [Module.End.mul_apply]
  calc ‖aeval E.encoded p (E.P x)‖ ≤ supNorm p * ‖E.P x‖ :=
        norm_aeval_apply_le E p (E.P x) (by rw [← Module.End.mul_apply, E.hP.mul_self])
    _ ≤ supNorm p * ‖x‖ :=
        mul_le_mul_of_nonneg_left (norm_proj_apply_le E.hP x) (supNorm_nonneg p)

/-- SVT-4. `‖(p(A) Π - q(A) Π) x‖ ≤ ‖p - q‖_∞ ‖x‖`: the error of replacing `p` by `q` is
controlled by the sup norm of `p - q` on `[-1, 1]`. -/
theorem norm_aeval_sub_mul_P_apply_le (p q : ℂ[X]) (x : ℋ) :
    ‖(aeval E.encoded p * E.P - aeval E.encoded q * E.P) x‖ ≤ supNorm (p - q) * ‖x‖ := by
  rw [← sub_mul, ← map_sub]
  exact norm_aeval_mul_P_apply_le E (p - q) x

/-- SVT-4 (operator-norm form). `‖p(A) Π‖ ≤ ‖p‖_∞`, where `p(A) Π : L ℋ` is viewed as a
continuous linear map through `LinearMap.toContinuousLinearMap` (finite dimension). -/
theorem opNorm_aeval_mul_P_le (p : ℂ[X]) :
    ‖LinearMap.toContinuousLinearMap (aeval E.encoded p * E.P)‖ ≤ supNorm p :=
  ContinuousLinearMap.opNorm_le_bound _ (supNorm_nonneg p) fun x => by
    rw [LinearMap.coe_toContinuousLinearMap']
    exact norm_aeval_mul_P_apply_le E p x

/-- SVT-4 (operator-norm form). `‖p(A) Π - q(A) Π‖ ≤ ‖p - q‖_∞`. -/
theorem opNorm_aeval_sub_mul_P_le (p q : ℂ[X]) :
    ‖LinearMap.toContinuousLinearMap (aeval E.encoded p * E.P - aeval E.encoded q * E.P)‖ ≤
      supNorm (p - q) :=
  ContinuousLinearMap.opNorm_le_bound _ (supNorm_nonneg _) fun x => by
    rw [LinearMap.coe_toContinuousLinearMap']
    exact norm_aeval_sub_mul_P_apply_le E p q x

end HermitianEncoding

end QSVT.SVT
