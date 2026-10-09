/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Register

/-!
# Two ancilla registers: the register swap and the two lifts (formal-spec ENC-4)

## Design decision

Two ancilla registers of dimensions `a` and `b` attached to the qudit `ℋ` are modelled by the
iterated direct sum `Reg a (Reg b ℋ)`: a vector `v` has components `v i j : ℋ` for `i : Fin a`
(the `a`-register) and `j : Fin b` (the `b`-register). In the tensor-product picture this is
`ℂ^a ⊗ ℂ^b ⊗ ℋ`. An operator `T₂ : L (Reg b ℋ)` acts on the inner two factors through
`selectOp` (`innerLift T₂ = 1_a ⊗ T₂`); an operator `T₁ : L (Reg a ℋ)` acts on the outer factor
and `ℋ` by first swapping the two registers (`swapReg : Reg a (Reg b ℋ) ≃ₗᵢ[ℂ] Reg b (Reg a ℋ)`,
`(swapReg v) j i = v i j`), applying `selectOp (fun _ => T₁)`, and swapping back
(`outerLift T₁ = "1_b ⊗ T₁" `, with the registers in the order `a, b`).

## Contents

* `swapRegₗ`, `swapReg`: the register swap as a linear equivalence and as a linear isometric
  equivalence (it preserves the `L²` inner product), with the coordinate lemmas
  `swapReg_apply`, `proj_proj_swapReg`, `swapReg_symm_apply`, `swapReg_inj_inj`.
* `slice j v : Reg a ℋ`, the `j`-th slice `(v i j)_i`, with `slice_inj`.
* `conjSwap T = swapReg⁻¹ ∘ T ∘ swapReg`: transport of operators along the swap, with
  `conjSwap_mul`, `conjSwap_one`, `conjSwap_add`, `conjSwap_smul`, `conjSwap_adjoint`,
  `conjSwap_mem_unitary`.
* `innerLift T₂ = selectOp (fun _ : Fin a => T₂)` and `outerLift T₁ = conjSwap (selectOp (fun _ :
  Fin b => T₁))`, with coordinate lemmas (`proj_innerLift`, `innerLift_inj`, `slice_outerLift`,
  `proj_proj_outerLift`) and their algebra (`*_mul`, `*_one`, `*_adjoint`, `*_mem_unitary`).
* `outerLift_reg0_comm_innerLift`: the ancilla projector `|0⟩⟨0|_a ⊗ 1` commutes with every
  `innerLift T₂` (it acts on a different factor).

## Mathlib API used

`PiLp.ext`, `PiLp.toLp_apply`, `PiLp.norm_eq_of_L2`, `PiLp.norm_sq_eq_of_L2`
(`Mathlib.Analysis.Normed.Lp.PiLp`), `LinearIsometryEquiv.inner_map_map`,
`LinearIsometryEquiv.apply_symm_apply`, `LinearIsometryEquiv.symm_apply_apply`
(`Mathlib.Analysis.InnerProductSpace.LinearMap`, `Mathlib.Analysis.Normed.Operator.LinearIsometry`),
`LinearMap.eq_adjoint_iff`, `LinearMap.adjoint_inner_left`, `Finset.sum_comm`.

Pitfall: building `swapReg` through `LinearEquiv.isometryOfInner` times out at `isDefEq`
(unifying the `Qudit`-derived and the `PiLp` norm instances two levels deep); the direct
`where` definition with `norm_map'` from `PiLp.norm_eq_of_L2` elaborates in well under a second.
-/

namespace QSVT.Encoding

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ] {a b : ℕ}

/-! ### The register swap -/

/-- ENC-4. The register swap `ℂ^a ⊗ ℂ^b ⊗ ℋ ≅ ℂ^b ⊗ ℂ^a ⊗ ℋ` as a linear equivalence:
`(swapRegₗ v) j i = v i j`. -/
noncomputable def swapRegₗ : Reg a (Reg b ℋ) ≃ₗ[ℂ] Reg b (Reg a ℋ) where
  toFun v := WithLp.toLp 2 fun j => WithLp.toLp 2 fun i => v i j
  invFun w := WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => w j i
  map_add' v w := PiLp.ext fun j => PiLp.ext fun i => by simp
  map_smul' c v := PiLp.ext fun j => PiLp.ext fun i => by simp
  left_inv v := PiLp.ext fun i => PiLp.ext fun j => rfl
  right_inv w := PiLp.ext fun j => PiLp.ext fun i => rfl

theorem swapRegₗ_apply (v : Reg a (Reg b ℋ)) (j : Fin b) (i : Fin a) : swapRegₗ v j i = v i j :=
  rfl

/-- ENC-4. The register swap is an isometry: `⟪swap v, swap w⟫ = ⟪v, w⟫` since both sides are
`∑ᵢ ∑ⱼ ⟪v i j, w i j⟫`. -/
theorem inner_swapRegₗ_swapRegₗ (v w : Reg a (Reg b ℋ)) :
    inner ℂ (swapRegₗ v) (swapRegₗ w) = inner ℂ v w := by
  simp only [inner_reg, proj_apply, swapRegₗ_apply]
  exact Finset.sum_comm

/-- ENC-4. The register swap `ℂ^a ⊗ ℂ^b ⊗ ℋ ≅ ℂ^b ⊗ ℂ^a ⊗ ℋ` as a linear isometric equivalence:
`(swapReg v) j i = v i j`. -/
noncomputable def swapReg : Reg a (Reg b ℋ) ≃ₗᵢ[ℂ] Reg b (Reg a ℋ) where
  toLinearEquiv := swapRegₗ
  norm_map' v := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    simp only [PiLp.norm_sq_eq_of_L2, swapRegₗ_apply]
    exact Finset.sum_comm

theorem swapReg_apply (v : Reg a (Reg b ℋ)) (j : Fin b) (i : Fin a) : swapReg v j i = v i j := rfl

theorem swapReg_symm_apply (w : Reg b (Reg a ℋ)) (i : Fin a) (j : Fin b) :
    swapReg.symm w i j = w j i := rfl

@[simp] theorem proj_proj_swapReg (v : Reg a (Reg b ℋ)) (j : Fin b) (i : Fin a) :
    proj i (proj j (swapReg v)) = proj j (proj i v) := rfl

@[simp] theorem proj_proj_swapReg_symm (w : Reg b (Reg a ℋ)) (i : Fin a) (j : Fin b) :
    proj j (proj i (swapReg.symm w)) = proj i (proj j w) := rfl

/-- ENC-4. The swap exchanges the two ancilla labels: `swap (|i⟩|j⟩|x⟩) = |j⟩|i⟩|x⟩`. -/
theorem swapReg_inj_inj (i : Fin a) (j : Fin b) (x : ℋ) :
    swapReg (inj i (inj j x) : Reg a (Reg b ℋ)) = inj j (inj i x) :=
  ext_reg fun j' => ext_reg fun i' => by
    rw [proj_proj_swapReg, proj_inj, proj_inj]
    by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

theorem swapReg_symm_inj_inj (j : Fin b) (i : Fin a) (x : ℋ) :
    swapReg.symm (inj j (inj i x) : Reg b (Reg a ℋ)) = inj i (inj j x) := by
  rw [← swapReg_inj_inj, LinearIsometryEquiv.symm_apply_apply]

/-! ### Slices -/

/-- ENC-4. The `j`-th slice `(v i j)_i : Reg a ℋ` of `v : Reg a (Reg b ℋ)`
(the component "`b`-register `= |j⟩`"). -/
noncomputable def slice (j : Fin b) : Reg a (Reg b ℋ) →ₗ[ℂ] Reg a ℋ :=
  proj j ∘ₗ (swapReg : Reg a (Reg b ℋ) ≃ₗᵢ[ℂ] Reg b (Reg a ℋ)).toLinearEquiv.toLinearMap

theorem slice_apply (j : Fin b) (v : Reg a (Reg b ℋ)) : slice j v = proj j (swapReg v) := rfl

@[simp] theorem proj_slice (i : Fin a) (j : Fin b) (v : Reg a (Reg b ℋ)) :
    proj i (slice j v) = proj j (proj i v) := rfl

/-- `slice j (|i⟩ ⊗ y) = |i⟩ ⊗ (y j)`. -/
theorem slice_inj (j : Fin b) (i : Fin a) (y : Reg b ℋ) :
    slice j (inj i y : Reg a (Reg b ℋ)) = inj i (proj j y) :=
  ext_reg fun i' => by
    rw [proj_slice, proj_inj, proj_inj]
    split_ifs <;> simp

/-! ### Transport of operators along the swap -/

/-- ENC-4. Transport of an operator on `Reg b (Reg a ℋ)` to `Reg a (Reg b ℋ)` along the swap:
`conjSwap T = swap⁻¹ ∘ T ∘ swap`. -/
noncomputable def conjSwap (T : L (Reg b (Reg a ℋ))) : L (Reg a (Reg b ℋ)) :=
  (swapReg : Reg a (Reg b ℋ) ≃ₗᵢ[ℂ] Reg b (Reg a ℋ)).symm.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ
    (swapReg : Reg a (Reg b ℋ) ≃ₗᵢ[ℂ] Reg b (Reg a ℋ)).toLinearEquiv.toLinearMap

section conjSwap

variable (S T : L (Reg b (Reg a ℋ)))

theorem conjSwap_apply (v : Reg a (Reg b ℋ)) : conjSwap T v = swapReg.symm (T (swapReg v)) := rfl

theorem swapReg_conjSwap (v : Reg a (Reg b ℋ)) : swapReg (conjSwap T v) = T (swapReg v) := by
  rw [conjSwap_apply, LinearIsometryEquiv.apply_symm_apply]

theorem conjSwap_mul : conjSwap (S * T) = conjSwap S * conjSwap T :=
  LinearMap.ext fun v => by
    simp only [conjSwap_apply, Module.End.mul_apply, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem conjSwap_one : conjSwap (1 : L (Reg b (Reg a ℋ))) = 1 :=
  LinearMap.ext fun v => by
    simp only [conjSwap_apply, Module.End.one_apply, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem conjSwap_zero : conjSwap (0 : L (Reg b (Reg a ℋ))) = 0 :=
  LinearMap.ext fun v => by simp only [conjSwap_apply, LinearMap.zero_apply, map_zero]

theorem conjSwap_add : conjSwap (S + T) = conjSwap S + conjSwap T :=
  LinearMap.ext fun v => by simp only [conjSwap_apply, LinearMap.add_apply, map_add]

theorem conjSwap_smul (c : ℂ) : conjSwap (c • T) = c • conjSwap T :=
  LinearMap.ext fun v => by simp only [conjSwap_apply, LinearMap.smul_apply, map_smul]

/-- ENC-4. Transport commutes with adjoints (the swap is an isometry). -/
theorem conjSwap_adjoint : (conjSwap T)† = conjSwap (T†) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro v w
  rw [conjSwap_apply, conjSwap_apply, ← LinearIsometryEquiv.inner_map_map swapReg,
    LinearIsometryEquiv.apply_symm_apply, LinearMap.adjoint_inner_left,
    ← LinearIsometryEquiv.inner_map_map swapReg v, LinearIsometryEquiv.apply_symm_apply]

/-- ENC-4. Transport preserves unitarity. -/
theorem conjSwap_mem_unitary (hT : T ∈ unitary (L (Reg b (Reg a ℋ)))) :
    conjSwap T ∈ unitary (L (Reg a (Reg b ℋ))) := by
  have h1 : T† * T = 1 := Unitary.star_mul_self_of_mem hT
  have h2 : T * T† = 1 := Unitary.mul_star_self_of_mem hT
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, conjSwap_adjoint, ← conjSwap_mul,
    ← conjSwap_mul, h1, h2, conjSwap_one]
  exact ⟨rfl, rfl⟩

end conjSwap

/-! ### The two lifts -/

/-- ENC-4. `1_a ⊗ T₂`: an operator on the `b`-register and `ℋ`, acting on each `a`-summand. -/
noncomputable def innerLift (T₂ : L (Reg b ℋ)) : L (Reg a (Reg b ℋ)) :=
  selectOp fun _ : Fin a => T₂

/-- ENC-4. `T₁` on the `a`-register and `ℋ`, identity on the `b`-register: swap the registers,
apply `1_b ⊗ T₁`, swap back. -/
noncomputable def outerLift (T₁ : L (Reg a ℋ)) : L (Reg a (Reg b ℋ)) :=
  conjSwap (selectOp fun _ : Fin b => T₁)

section innerLift

variable (S₂ T₂ : L (Reg b ℋ))

@[simp] theorem proj_innerLift (i : Fin a) (v : Reg a (Reg b ℋ)) :
    proj i (innerLift T₂ v) = T₂ (proj i v) := rfl

theorem innerLift_inj (i : Fin a) (y : Reg b ℋ) :
    innerLift T₂ (inj i y : Reg a (Reg b ℋ)) = inj i (T₂ y) :=
  selectOp_inj _ i y

theorem innerLift_mul : (innerLift S₂ * innerLift T₂ : L (Reg a (Reg b ℋ))) = innerLift (S₂ * T₂) :=
  selectOp_mul _ _

@[simp] theorem innerLift_one : (innerLift 1 : L (Reg a (Reg b ℋ))) = 1 := selectOp_one

theorem innerLift_adjoint : (innerLift T₂ : L (Reg a (Reg b ℋ)))† = innerLift (T₂†) :=
  selectOp_adjoint _

/-- ENC-4. `1_a ⊗ T₂` is unitary when `T₂` is. -/
theorem innerLift_mem_unitary (h : T₂ ∈ unitary (L (Reg b ℋ))) :
    (innerLift T₂ : L (Reg a (Reg b ℋ))) ∈ unitary (L (Reg a (Reg b ℋ))) :=
  selectOp_mem_unitary _ fun _ => h

end innerLift

section outerLift

variable (S₁ T₁ : L (Reg a ℋ))

/-- `outerLift T₁` acts slice-wise by `T₁`. -/
@[simp] theorem slice_outerLift (j : Fin b) (v : Reg a (Reg b ℋ)) :
    slice j (outerLift T₁ v) = T₁ (slice j v) := by
  rw [slice_apply, outerLift, swapReg_conjSwap, proj_selectOp, slice_apply]

theorem proj_proj_outerLift (i : Fin a) (j : Fin b) (v : Reg a (Reg b ℋ)) :
    proj j (proj i (outerLift T₁ v)) = proj i (T₁ (slice j v)) := by
  rw [← proj_slice, slice_outerLift]

theorem outerLift_mul :
    (outerLift S₁ * outerLift T₁ : L (Reg a (Reg b ℋ))) = outerLift (S₁ * T₁) := by
  rw [outerLift, outerLift, outerLift, ← conjSwap_mul, selectOp_mul]

@[simp] theorem outerLift_one : (outerLift 1 : L (Reg a (Reg b ℋ))) = 1 := by
  rw [outerLift, selectOp_one, conjSwap_one]

theorem outerLift_adjoint : (outerLift T₁ : L (Reg a (Reg b ℋ)))† = outerLift (T₁†) := by
  rw [outerLift, outerLift, conjSwap_adjoint, selectOp_adjoint]

/-- ENC-4. `T₁ ⊗ 1_b` is unitary when `T₁` is. -/
theorem outerLift_mem_unitary (h : T₁ ∈ unitary (L (Reg a ℋ))) :
    (outerLift T₁ : L (Reg a (Reg b ℋ))) ∈ unitary (L (Reg a (Reg b ℋ))) :=
  conjSwap_mem_unitary _ (selectOp_mem_unitary _ fun _ => h)

/-- ENC-4. The lifted ancilla projector `|0⟩⟨0|_a ⊗ 1` in coordinates. -/
theorem proj_proj_outerLift_reg0 [NeZero a] (i : Fin a) (j : Fin b) (v : Reg a (Reg b ℋ)) :
    proj j (proj i (outerLift (reg0 : L (Reg a ℋ)) v)) =
      if i = 0 then proj j (proj 0 v) else 0 := by
  rw [proj_proj_outerLift, reg0_apply, proj_inj, proj_slice]

/-- ENC-4. `|0⟩⟨0|_a ⊗ 1` commutes with every `1_a ⊗ T₂` (they act on different factors). -/
theorem outerLift_reg0_comm_innerLift [NeZero a] (T₂ : L (Reg b ℋ)) :
    (outerLift (reg0 : L (Reg a ℋ)) * innerLift T₂ : L (Reg a (Reg b ℋ))) =
      innerLift T₂ * outerLift reg0 := by
  refine LinearMap.ext fun v => ext_reg fun i => ext_reg fun j => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, proj_proj_outerLift_reg0, proj_innerLift,
    proj_innerLift]
  split_ifs with h
  · subst h; rfl
  · have h0 : proj i (outerLift (reg0 : L (Reg a ℋ)) v) = 0 :=
      ext_reg fun j' => by rw [proj_proj_outerLift_reg0]; simp [h]
    rw [h0, map_zero, map_zero]

end outerLift

end QSVT.Encoding
