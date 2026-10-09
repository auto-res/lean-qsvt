/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# An `m`-dimensional ancilla register as a Hilbert direct sum (formal-spec ENC-2)

## Design decision

The one-ancilla module `QSVT.Encoding.Ancilla` models `ℂ² ⊗ ℋ` as the direct sum `ℋ ⊕ ℋ`.
This module generalizes it to an `m`-dimensional ancilla register: instead of a tensor
product `ℂ^m ⊗ ℋ`, the register is modelled by the Hilbert-space direct sum

`Reg m ℋ := PiLp 2 (fun _ : Fin m => ℋ) ≅ ℋ ⊕ ⋯ ⊕ ℋ` (`m` summands),

the `k`-th summand being "ancilla `= |k⟩`". Mathlib's `PiLp.innerProductSpace`
(`Mathlib.Analysis.InnerProductSpace.PiL2`) provides the `L²` inner product
`⟪v, w⟫ = ∑ k, ⟪v k, w k⟫`, so `Reg m ℋ` is again a `Qudit`.

Operators on `Reg m ℋ` are described through two building blocks, which are exactly the
tensor-product operators `V ⊗ 1` and `∑ₖ |k⟩⟨k| ⊗ Wₖ` in the usual picture:

* `matOp V` for `V : Matrix (Fin m) (Fin m) ℂ` acts as `(x_j)_j ↦ (∑ₖ V j k • x_k)_j`
  (the ancilla gate `V ⊗ 1`);
* `selectOp W` for `W : Fin m → L ℋ` acts summand-wise, `(x_k)_k ↦ (W k x_k)_k`
  (the "select" operator `∑ₖ |k⟩⟨k| ⊗ Wₖ`).

Both are multiplicative, `matOp (V * W) = matOp V * matOp W`, `selectOp` likewise, their
adjoints are `matOp Vᴴ` and `selectOp (fun k => (W k)†)`, and they are unitary when their
ingredients are. The `(0,0)` block `regTopLeft T = proj 0 ∘ T ∘ inj 0` is the operator
block-encoded by `T` (GSLW Def 43), and `reg0 = |0⟩⟨0| ⊗ 1` is the ancilla projector.

## Contents

* `Reg m ℋ`, `instance : Qudit (Reg m ℋ)`.
* `inj k : ℋ →ₗ[ℂ] Reg m ℋ`, `proj k : Reg m ℋ →ₗ[ℂ] ℋ` with `proj_inj`, `sum_inj_proj`,
  the extensionality lemmas `ext_reg`, `op_ext_reg`, inner products (`inner_reg`,
  `inner_inj_inj`), norms (`norm_inj`) and adjoints (`inj_adjoint : (inj k)† = proj k`).
* `matOp V` with `proj_matOp`, `matOp_one`, `matOp_mul`, `matOp_adjoint`, `matOp_add`,
  `matOp_smul`, `matOp_mem_unitary`.
* `selectOp W` with `proj_selectOp`, `selectOp_one`, `selectOp_mul`, `selectOp_adjoint`,
  `selectOp_add`, `selectOp_smul`, `selectOp_mem_unitary`, `selectOp_const_isProjective`.
* `regTopLeft T` (for `[NeZero m]`) with `regTopLeft_selectOp`, `regTopLeft_matOp`,
  `regTopLeft_add`,
  `regTopLeft_smul`.
* `reg0 = |0⟩⟨0| ⊗ 1`, `reg0_isProjective`, `reg0_mul_mul_reg0`, `regTopLeft_reg0_mul_mul_reg0`.

## Mathlib API used

`PiLp`, `PiLp.single`, `PiLp.projₗ`, `PiLp.ext`, `PiLp.single_eq_same`,
`PiLp.single_eq_of_ne`, `PiLp.norm_single` (`Mathlib.Analysis.Normed.Lp.PiLp`),
`PiLp.inner_apply` (`Mathlib.Analysis.InnerProductSpace.PiL2`), `WithLp.toLp`/`WithLp.ofLp`,
`WithLp.linearEquiv`, `LinearMap.single`, `Matrix.mem_unitaryGroup_iff`,
`Matrix.mem_unitaryGroup_iff'` (`Mathlib.LinearAlgebra.UnitaryGroup`), and
`LinearMap.eq_adjoint_iff` for adjoints between different spaces.
-/

namespace QSVT.Encoding

open QuantumState Matrix

universe u

/-- ENC-2. The qudit `ℋ` with an `m`-dimensional ancilla register attached, modelled as the
Hilbert-space direct sum of `m` copies of `ℋ` with the `L²` inner product. The `k`-th summand
is "ancilla `= |k⟩`". -/
abbrev Reg (m : ℕ) (ℋ : Type u) : Type u := PiLp 2 (fun _ : Fin m => ℋ)

variable {ℋ : Type u} [Qudit ℋ] {m : ℕ}

/-- ENC-2. `Reg m ℋ` is again a qudit (all fields are Mathlib instances on `PiLp 2`). -/
noncomputable instance instQuditReg : Qudit (Reg m ℋ) := {}

/-! ### Injections and projections -/

/-- Embedding of `ℋ` as the "ancilla `= |k⟩`" summand: `inj k x = (0, …, x, …, 0)`. -/
noncomputable def inj (k : Fin m) : ℋ →ₗ[ℂ] Reg m ℋ :=
  (WithLp.linearEquiv 2 ℂ (∀ _ : Fin m, ℋ)).symm.toLinearMap ∘ₗ
    LinearMap.single ℂ (fun _ : Fin m => ℋ) k

/-- Projection onto the "ancilla `= |k⟩`" summand. -/
noncomputable def proj (k : Fin m) : Reg m ℋ →ₗ[ℂ] ℋ := PiLp.projₗ 2 (fun _ : Fin m => ℋ) k

theorem inj_apply (k : Fin m) (x : ℋ) : (inj k x : Reg m ℋ) = PiLp.single 2 k x := rfl

theorem inj_apply' (k : Fin m) (x : ℋ) : (inj k x : Reg m ℋ) = WithLp.toLp 2 (Pi.single k x) :=
  rfl

theorem proj_apply (k : Fin m) (v : Reg m ℋ) : proj k v = v k := rfl

@[simp] theorem proj_inj_same (k : Fin m) (x : ℋ) : proj k (inj k x) = x := by
  rw [proj_apply, inj_apply, PiLp.single_eq_same]

@[simp] theorem proj_inj_ne {j k : Fin m} (h : j ≠ k) (x : ℋ) : proj j (inj k x) = 0 := by
  rw [proj_apply, inj_apply, PiLp.single_eq_of_ne 2 h]

theorem proj_inj (j k : Fin m) (x : ℋ) : proj j (inj k x) = if j = k then x else 0 := by
  split_ifs with h
  · subst h; exact proj_inj_same j x
  · exact proj_inj_ne h x

/-- Two vectors of `Reg m ℋ` agree iff all components agree. -/
theorem ext_reg {v w : Reg m ℋ} (h : ∀ k, proj k v = proj k w) : v = w := PiLp.ext h

theorem ext_reg_iff {v w : Reg m ℋ} : v = w ↔ ∀ k, proj k v = proj k w :=
  ⟨fun h k => congrArg (proj k) h, ext_reg⟩

/-- Every vector decomposes as `v = ∑ k, inj k (proj k v)`. -/
@[simp] theorem sum_inj_proj (v : Reg m ℋ) : ∑ k, inj k (proj k v) = v :=
  ext_reg fun j => by simp [map_sum, proj_inj]

/-- Operators on `Reg m ℋ` are determined by their values on the summands. -/
theorem op_ext_reg {S T : L (Reg m ℋ)} (h : ∀ k x, S (inj k x) = T (inj k x)) : S = T := by
  refine LinearMap.ext fun v => ?_
  rw [← sum_inj_proj v, map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => h k _

/-! ### Inner products, norms and adjoints -/

/-- The `L²` inner product on `Reg m ℋ` in terms of the components. -/
theorem inner_reg (v w : Reg m ℋ) : inner ℂ v w = ∑ k, inner ℂ (proj k v) (proj k w) := rfl

theorem inner_inj_right (v : Reg m ℋ) (k : Fin m) (y : ℋ) :
    inner ℂ v (inj k y) = inner ℂ (proj k v) y := by
  rw [inner_reg, Finset.sum_eq_single k]
  · rw [proj_inj_same]
  · intro i _ hik
    rw [proj_inj_ne hik, inner_zero_right]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem inner_inj_left (j : Fin m) (x : ℋ) (w : Reg m ℋ) :
    inner ℂ (inj j x) w = inner ℂ x (proj j w) := by
  rw [inner_reg, Finset.sum_eq_single j]
  · rw [proj_inj_same]
  · intro i _ hij
    rw [proj_inj_ne hij, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem inner_inj_inj (j k : Fin m) (x y : ℋ) :
    inner ℂ (inj j x) (inj k y) = if j = k then inner ℂ x y else 0 := by
  rw [inner_inj_left, proj_inj]
  split_ifs with h
  · subst h; rfl
  · exact inner_zero_right x

@[simp] theorem norm_inj (k : Fin m) (x : ℋ) : ‖(inj k x : Reg m ℋ)‖ = ‖x‖ :=
  PiLp.norm_single 2 (fun _ : Fin m => ℋ) k x

/-- `(inj k)† = proj k`. -/
@[simp] theorem inj_adjoint (k : Fin m) :
    LinearMap.adjoint (inj k : ℋ →ₗ[ℂ] Reg m ℋ) = proj k :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun v y => (inner_inj_right v k y).symm).symm

/-- `(proj k)† = inj k`. -/
@[simp] theorem proj_adjoint (k : Fin m) :
    LinearMap.adjoint (proj k : Reg m ℋ →ₗ[ℂ] ℋ) = inj k := by
  rw [← inj_adjoint, LinearMap.adjoint_adjoint]

/-! ### The ancilla gate `V ⊗ 1` -/

/-- ENC-2. The ancilla gate `V ⊗ 1` for a matrix `V` on the register:
`(x_j)_j ↦ (∑ₖ V j k • x_k)_j`. -/
noncomputable def matOp (V : Matrix (Fin m) (Fin m) ℂ) : L (Reg m ℋ) where
  toFun v := WithLp.toLp 2 fun j => ∑ k, V j k • v k
  map_add' v w := PiLp.ext fun j => by
    simp only [PiLp.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c v := PiLp.ext fun j => by
    simp only [PiLp.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul,
      mul_comm c]

section matOp

variable (V W : Matrix (Fin m) (Fin m) ℂ)

theorem matOp_apply (v : Reg m ℋ) : matOp V v = WithLp.toLp 2 fun j => ∑ k, V j k • v k := rfl

@[simp] theorem proj_matOp (j : Fin m) (v : Reg m ℋ) :
    proj j (matOp V v) = ∑ k, V j k • proj k v := rfl

theorem proj_matOp_inj (j k : Fin m) (x : ℋ) : proj j (matOp V (inj k x)) = V j k • x := by
  simp [proj_inj, smul_ite]

theorem matOp_add : matOp (V + W) = (matOp V + matOp W : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by
    simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem matOp_smul (c : ℂ) : matOp (c • V) = (c • matOp V : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by
    simp [Matrix.smul_apply, smul_smul, Finset.smul_sum]

theorem matOp_sub : matOp (V - W) = (matOp V - matOp W : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by
    simp [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

@[simp] theorem matOp_zero : matOp (0 : Matrix (Fin m) (Fin m) ℂ) = (0 : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by simp

@[simp] theorem matOp_one : matOp (1 : Matrix (Fin m) (Fin m) ℂ) = (1 : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by simp [Matrix.one_apply, ite_smul]

/-- ENC-2. `(V W) ⊗ 1 = (V ⊗ 1)(W ⊗ 1)`. -/
theorem matOp_mul : matOp (V * W) = (matOp V * matOp W : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun j => by
    simp only [proj_matOp, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_comm

/-- ENC-2. `(V ⊗ 1)† = Vᴴ ⊗ 1`. -/
theorem matOp_adjoint : (matOp V : L (Reg m ℋ))† = matOp Vᴴ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro v w
  simp only [inner_reg, proj_matOp, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_comm

/-- ENC-2. `V ⊗ 1` is unitary when `V` is. -/
theorem matOp_mem_unitary (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    (matOp V : L (Reg m ℋ)) ∈ unitary (L (Reg m ℋ)) := by
  have h1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, matOp_adjoint, ← matOp_mul, ← matOp_mul, h1,
    h2, matOp_one]
  exact ⟨rfl, rfl⟩

end matOp

/-! ### The select operator `∑ₖ |k⟩⟨k| ⊗ Wₖ` -/

/-- ENC-2. The select operator `∑ₖ |k⟩⟨k| ⊗ Wₖ`, acting summand-wise:
`(x_k)_k ↦ (W k x_k)_k`. -/
noncomputable def selectOp (W : Fin m → L ℋ) : L (Reg m ℋ) where
  toFun v := WithLp.toLp 2 fun k => W k (v k)
  map_add' v w := PiLp.ext fun k => by simp
  map_smul' c v := PiLp.ext fun k => by simp

section selectOp

variable (W W' : Fin m → L ℋ)

theorem selectOp_apply (v : Reg m ℋ) : selectOp W v = WithLp.toLp 2 fun k => W k (v k) := rfl

@[simp] theorem proj_selectOp (k : Fin m) (v : Reg m ℋ) :
    proj k (selectOp W v) = W k (proj k v) := rfl

theorem selectOp_inj (k : Fin m) (x : ℋ) : selectOp W (inj k x) = inj k (W k x) :=
  ext_reg fun j => by
    by_cases h : j = k
    · subst h; simp
    · simp [proj_inj_ne h]

theorem selectOp_add : selectOp (W + W') = (selectOp W + selectOp W' : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun k => by simp

theorem selectOp_smul (c : ℂ) : selectOp (c • W) = (c • selectOp W : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun k => by simp

theorem selectOp_sub : selectOp (W - W') = (selectOp W - selectOp W' : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun k => by simp

@[simp] theorem selectOp_zero : selectOp (fun _ : Fin m => (0 : L ℋ)) = (0 : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun k => by simp

@[simp] theorem selectOp_one : selectOp (fun _ : Fin m => (1 : L ℋ)) = (1 : L (Reg m ℋ)) :=
  LinearMap.ext fun v => ext_reg fun k => by simp

/-- ENC-2. Select operators multiply summand-wise. -/
theorem selectOp_mul : (selectOp W * selectOp W' : L (Reg m ℋ)) = selectOp fun k => W k * W' k :=
  LinearMap.ext fun v => ext_reg fun k => by simp

/-- ENC-2. The adjoint of a select operator is the select operator of the adjoints. -/
theorem selectOp_adjoint : (selectOp W : L (Reg m ℋ))† = selectOp fun k => (W k)† := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro v w
  simp only [inner_reg, proj_selectOp, LinearMap.adjoint_inner_left]

/-- ENC-2. `∑ₖ |k⟩⟨k| ⊗ Wₖ` is unitary when every `Wₖ` is. -/
theorem selectOp_mem_unitary (h : ∀ k, W k ∈ unitary (L ℋ)) :
    (selectOp W : L (Reg m ℋ)) ∈ unitary (L (Reg m ℋ)) := by
  have h1 : (fun k => (W k)† * W k) = fun _ : Fin m => (1 : L ℋ) :=
    funext fun k => Unitary.star_mul_self_of_mem (h k)
  have h2 : (fun k => W k * (W k)†) = fun _ : Fin m => (1 : L ℋ) :=
    funext fun k => Unitary.mul_star_self_of_mem (h k)
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, selectOp_adjoint, selectOp_mul, selectOp_mul,
    h1, h2, selectOp_one]
  exact ⟨rfl, rfl⟩

/-- ENC-2. `1 ⊗ P` is a projection when `P` is. -/
theorem selectOp_const_isProjective {P : L ℋ} (hP : IsProjective P) :
    IsProjective (selectOp fun _ : Fin m => P) :=
  isProjective_iff_isStarProjection.mpr
    ⟨show (selectOp fun _ : Fin m => P) * (selectOp fun _ : Fin m => P) = _ by
        rw [selectOp_mul]; simp only [hP.mul_self],
      show (selectOp fun _ : Fin m => P)† = _ by
        rw [selectOp_adjoint]; simp only [hP.adjoint_eq]⟩

/-- Compressing a select operator by `1 ⊗ P` on both sides compresses every summand. -/
theorem selectOp_const_mul_selectOp_mul (P : L ℋ) :
    ((selectOp fun _ : Fin m => P) * selectOp W * selectOp fun _ : Fin m => P) =
      selectOp fun k => P * W k * P := by
  rw [selectOp_mul, selectOp_mul]

end selectOp

/-! ### The top-left block -/

section regTopLeft

variable [NeZero m]

/-- ENC-2. The `(0,0)` block `(⟨0| ⊗ 1) T (|0⟩ ⊗ 1) = proj 0 ∘ T ∘ inj 0` of an operator on
`Reg m ℋ` (GSLW Def 43: the operator block-encoded by `T`). -/
noncomputable def regTopLeft (T : L (Reg m ℋ)) : L ℋ := proj 0 ∘ₗ T ∘ₗ inj 0

theorem regTopLeft_apply (T : L (Reg m ℋ)) (x : ℋ) : regTopLeft T x = proj 0 (T (inj 0 x)) := rfl

@[simp] theorem regTopLeft_selectOp (W : Fin m → L ℋ) : regTopLeft (selectOp W) = W 0 :=
  LinearMap.ext fun x => by simp [regTopLeft_apply]

@[simp] theorem regTopLeft_matOp (V : Matrix (Fin m) (Fin m) ℂ) :
    regTopLeft (matOp V : L (Reg m ℋ)) = V 0 0 • (1 : L ℋ) :=
  LinearMap.ext fun x => by simp [regTopLeft_apply, proj_inj, smul_ite]

theorem regTopLeft_add (S T : L (Reg m ℋ)) : regTopLeft (S + T) = regTopLeft S + regTopLeft T := by
  simp [regTopLeft, LinearMap.add_comp, LinearMap.comp_add]

theorem regTopLeft_smul (c : ℂ) (T : L (Reg m ℋ)) : regTopLeft (c • T) = c • regTopLeft T := by
  simp [regTopLeft, LinearMap.smul_comp, LinearMap.comp_smul]

@[simp] theorem regTopLeft_one : regTopLeft (1 : L (Reg m ℋ)) = 1 := by
  rw [← selectOp_one, regTopLeft_selectOp]

@[simp] theorem regTopLeft_zero : regTopLeft (0 : L (Reg m ℋ)) = 0 := by
  rw [← selectOp_zero, regTopLeft_selectOp]

/-! ### The ancilla projector `|0⟩⟨0| ⊗ 1` -/

/-- ENC-2. The projector `|0⟩⟨0| ⊗ 1` onto the "ancilla `= |0⟩`" summand. -/
noncomputable def reg0 : L (Reg m ℋ) := selectOp fun k => if k = 0 then 1 else 0

theorem reg0_apply (v : Reg m ℋ) : reg0 v = inj 0 (proj 0 v) :=
  ext_reg fun j => by
    simp only [reg0, proj_selectOp, proj_inj]
    split_ifs with h
    · subst h; rfl
    · rfl

@[simp] theorem reg0_adjoint : (reg0 : L (Reg m ℋ))† = reg0 := by
  rw [reg0, selectOp_adjoint]
  congr 1
  funext k
  split_ifs <;> simp

@[simp] theorem reg0_mul_reg0 : (reg0 : L (Reg m ℋ)) * reg0 = reg0 := by
  rw [reg0, selectOp_mul]
  congr 1
  funext k
  split_ifs <;> simp

/-- ENC-2. `|0⟩⟨0| ⊗ 1` is an orthogonal projection. -/
theorem reg0_isProjective : IsProjective (reg0 : L (Reg m ℋ)) :=
  isProjective_iff_isStarProjection.mpr ⟨reg0_mul_reg0, reg0_adjoint⟩

@[simp] theorem regTopLeft_reg0 : regTopLeft (reg0 : L (Reg m ℋ)) = 1 := by
  rw [reg0, regTopLeft_selectOp]
  simp

/-- ENC-2. Compressing by the ancilla projector keeps only the `(0,0)` block. -/
theorem reg0_mul_mul_reg0 (T : L (Reg m ℋ)) :
    reg0 * T * reg0 = selectOp fun k => if k = 0 then regTopLeft T else 0 := by
  refine LinearMap.ext fun v => ext_reg fun j => ?_
  simp only [Module.End.mul_apply, reg0_apply, proj_selectOp, proj_inj]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem regTopLeft_reg0_mul_mul_reg0 (T : L (Reg m ℋ)) :
    regTopLeft (reg0 * T * reg0) = regTopLeft T := by
  rw [reg0_mul_mul_reg0, regTopLeft_selectOp]
  simp

end regTopLeft

end QSVT.Encoding
