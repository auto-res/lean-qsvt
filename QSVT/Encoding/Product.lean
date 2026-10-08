/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Swap
import QSVT.Encoding.Projected
import QSVT.IR.Denote

/-!
# Product of block encodings (formal-spec ENC-4, GSLW Lemma 53)

Given an encoding `U₁` on `Reg a ℋ` (ancilla register of dimension `a`) of `A₁ = regTopLeft U₁`
and an encoding `U₂` on `Reg b ℋ` of `A₂ = regTopLeft U₂`, the operator

`prodU U₁ U₂ = (1_b ⊗ U₁)(1_a ⊗ U₂) = outerLift U₁ * innerLift U₂`

on `Reg a (Reg b ℋ)` (`ℂ^a ⊗ ℂ^b ⊗ ℋ`) encodes the product `A₁ A₂`: its `(0,0),(0,0)` block
`topLeft₂ (prodU U₁ U₂) = ⟨0_a 0_b| prodU U₁ U₂ |0_a 0_b⟩` is `A₁ A₂` (`topLeft₂_prodU`). This is
GSLW Lemma 53 in the exact (`ε = 0`) direct-sum model: the subnormalisations multiply
(`α β`), the ancilla counts add (`a + b` qubits, here dimensions `a · b`), and the error bound
`α δ + β ε` is left to the norm layer.

The packaged version `prodEncoding E₁ E₂ P₁' P₂` is a `ProjUnitaryEncoding (Reg a (Reg b ℋ))`
with unitary `prodU E₁.U E₂.U` and projectors `prodP P₂ = |0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ P₂` (input) and
`prodP P₁'` (output). When `E₁` and `E₂` are pure block encodings (all projectors
`|0⟩⟨0| ⊗ 1 = reg0`), its compressed encoded operator is the product of the compressed
encoded operators (`prodBlockEncoding_topLeft₂_encoded`); more generally it suffices that the
inner projectors `E₁.P` and `E₂.P'` are `reg0` (`prodEncoding_topLeft₂_encoded`).

## Resources

`prodU U₁ U₂` uses `U₁` once and `U₂` once, so query counts add; the ancilla registers are
kept separate (dimension `a · b` in total).

## Contents

* `prodU`, `prodU_mem_unitary`, `prodU_adjoint`.
* `prodP P = atZero (atZero P)`, `prodP_isProjective`, `prodP_mul`, `prodP_adjoint`,
  `prodP_eq_innerLift_mul_outerLift`.
* `topLeft₂ T = regTopLeft (regTopLeft T)` with `topLeft₂_add`, `topLeft₂_smul`, `topLeft₂_one`,
  `topLeft₂_outerLift`, `topLeft₂_innerLift`, `topLeft₂_prodP`.
* `topLeft₂_prodU` (GSLW Lemma 53), `regTopLeft_atZero_mul_mul_atZero`,
  `topLeft₂_prodP_mul_mul_prodP`, `topLeft₂_prodP_prodU`.
* `prodEncoding`, `prodEncoding_encoded`, `topLeft₂_prodEncoding_encoded`,
  `prodEncoding_topLeft₂_encoded`, `prodBlockEncoding`, `prodBlockEncoding_topLeft₂_encoded`.

The IR constructor for products is a later step (`QSVT.IR` is untouched here).
-/

namespace QSVT.Encoding

open QuantumState QSVT.IR

universe u

variable {ℋ : Type u} [Qudit ℋ] {a b : ℕ}

/-! ### The product unitary -/

/-- ENC-4 (GSLW Lemma 53). The product circuit `(1_b ⊗ U₁)(1_a ⊗ U₂)` on `ℂ^a ⊗ ℂ^b ⊗ ℋ`:
`U₂` acts on the `b`-register and `ℋ`, then `U₁` acts on the `a`-register and `ℋ`. -/
noncomputable def prodU (U₁ : L (Reg a ℋ)) (U₂ : L (Reg b ℋ)) : L (Reg a (Reg b ℋ)) :=
  outerLift U₁ * innerLift U₂

section prodU

variable (U₁ : L (Reg a ℋ)) (U₂ : L (Reg b ℋ))

/-- ENC-4. The product circuit is unitary when both factors are. -/
theorem prodU_mem_unitary (h₁ : U₁ ∈ unitary (L (Reg a ℋ))) (h₂ : U₂ ∈ unitary (L (Reg b ℋ))) :
    prodU U₁ U₂ ∈ unitary (L (Reg a (Reg b ℋ))) :=
  mul_mem (outerLift_mem_unitary U₁ h₁) (innerLift_mem_unitary U₂ h₂)

theorem prodU_adjoint : (prodU U₁ U₂)† = innerLift (U₂†) * outerLift (U₁†) := by
  rw [prodU, ← LinearMap.star_eq_adjoint, star_mul, LinearMap.star_eq_adjoint,
    LinearMap.star_eq_adjoint, innerLift_adjoint, outerLift_adjoint]

end prodU

variable [NeZero a] [NeZero b]

/-! ### The product projector -/

/-- ENC-4. The projector `|0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ P` on `Reg a (Reg b ℋ)` (GSLW Def 43 with
`a + b` ancilla qubits). -/
noncomputable def prodP (P : L ℋ) : L (Reg a (Reg b ℋ)) := atZero (atZero P)

section prodP

variable (P P' : L ℋ)

theorem prodP_mul : (prodP P * prodP P' : L (Reg a (Reg b ℋ))) = prodP (P * P') := by
  rw [prodP, prodP, prodP, atZero_mul, atZero_mul]

theorem prodP_adjoint : (prodP P : L (Reg a (Reg b ℋ)))† = prodP (P†) := by
  rw [prodP, prodP, atZero_adjoint, atZero_adjoint]

/-- ENC-4. `|0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ P` is an orthogonal projection when `P` is. -/
theorem prodP_isProjective {P : L ℋ} (hP : IsProjective P) :
    IsProjective (prodP P : L (Reg a (Reg b ℋ))) :=
  atZero_isProjective (atZero_isProjective hP)

/-- `|0⟩⟨0| ⊗ 1 = reg0` (definitional). -/
theorem atZero_one {m : ℕ} [NeZero m] : (atZero (1 : L ℋ) : L (Reg m ℋ)) = reg0 := rfl

/-- ENC-4. The product projector factors as `(1_a ⊗ |0⟩⟨0|_b ⊗ P)(|0⟩⟨0|_a ⊗ 1)`. -/
theorem prodP_eq_innerLift_mul_outerLift :
    (prodP P : L (Reg a (Reg b ℋ))) = innerLift (atZero P) * outerLift reg0 := by
  refine LinearMap.ext fun v => ext_reg fun i => ext_reg fun j => ?_
  simp only [Module.End.mul_apply, proj_innerLift, prodP, atZero, proj_selectOp]
  rw [proj_proj_outerLift_reg0]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

end prodP

/-! ### The doubly compressed block -/

/-- ENC-4. The `(0,0),(0,0)` block `⟨0_a 0_b| T |0_a 0_b⟩` of an operator on `Reg a (Reg b ℋ)`:
both ancilla registers projected onto `|0⟩`. -/
noncomputable def topLeft₂ (T : L (Reg a (Reg b ℋ))) : L ℋ := regTopLeft (regTopLeft T)

section topLeft₂

variable (S T : L (Reg a (Reg b ℋ)))

theorem topLeft₂_apply (x : ℋ) : topLeft₂ T x = proj 0 (proj 0 (T (inj 0 (inj 0 x)))) := rfl

theorem topLeft₂_add : topLeft₂ (S + T) = topLeft₂ S + topLeft₂ T := by
  rw [topLeft₂, topLeft₂, topLeft₂, regTopLeft_add, regTopLeft_add]

theorem topLeft₂_smul (c : ℂ) : topLeft₂ (c • T) = c • topLeft₂ T := by
  rw [topLeft₂, topLeft₂, regTopLeft_smul, regTopLeft_smul]

@[simp] theorem topLeft₂_one : topLeft₂ (1 : L (Reg a (Reg b ℋ))) = 1 := by
  rw [topLeft₂, regTopLeft_one, regTopLeft_one]

@[simp] theorem topLeft₂_zero : topLeft₂ (0 : L (Reg a (Reg b ℋ))) = 0 := by
  rw [topLeft₂, regTopLeft_zero, regTopLeft_zero]

/-- ENC-4. Compressing `U₁ ⊗ 1_b` gives the compression of `U₁`. -/
@[simp] theorem topLeft₂_outerLift (U₁ : L (Reg a ℋ)) :
    topLeft₂ (outerLift U₁ : L (Reg a (Reg b ℋ))) = regTopLeft U₁ :=
  LinearMap.ext fun x => by
    rw [topLeft₂_apply, proj_proj_outerLift, slice_inj, proj_inj_same]
    rfl

/-- ENC-4. Compressing `1_a ⊗ U₂` gives the compression of `U₂`. -/
@[simp] theorem topLeft₂_innerLift (U₂ : L (Reg b ℋ)) :
    topLeft₂ (innerLift U₂ : L (Reg a (Reg b ℋ))) = regTopLeft U₂ := by
  rw [topLeft₂, innerLift, regTopLeft_selectOp]

@[simp] theorem topLeft₂_prodP (P : L ℋ) : topLeft₂ (prodP P : L (Reg a (Reg b ℋ))) = P := by
  rw [topLeft₂, prodP, regTopLeft_atZero, regTopLeft_atZero]

end topLeft₂

/-! ### GSLW Lemma 53: the compressed product -/

/-- ENC-4 (GSLW Lemma 53).
`⟨0_a 0_b| (1_b ⊗ U₁)(1_a ⊗ U₂) |0_a 0_b⟩ = ⟨0_a| U₁ |0_a⟩ ⟨0_b| U₂ |0_b⟩`: the product circuit
block-encodes the product of the block-encoded operators. -/
theorem topLeft₂_prodU (U₁ : L (Reg a ℋ)) (U₂ : L (Reg b ℋ)) :
    topLeft₂ (prodU U₁ U₂) = regTopLeft U₁ * regTopLeft U₂ :=
  LinearMap.ext fun x => by
    rw [topLeft₂_apply, prodU, Module.End.mul_apply, innerLift_inj, proj_proj_outerLift, slice_inj]
    rfl

/-- ENC-4 (helper). Compressing a sandwich by `|0⟩⟨0| ⊗ B` and `|0⟩⟨0| ⊗ C` sandwiches the
compression: `regTopLeft ((|0⟩⟨0| ⊗ B) T (|0⟩⟨0| ⊗ C)) = B (regTopLeft T) C`. -/
theorem regTopLeft_atZero_mul_mul_atZero {m : ℕ} [NeZero m] (B C : L ℋ) (T : L (Reg m ℋ)) :
    regTopLeft (atZero B * T * atZero C) = B * regTopLeft T * C :=
  LinearMap.ext fun x => by
    simp only [regTopLeft_apply, Module.End.mul_apply, atZero, proj_selectOp, selectOp_inj]
    simp

/-- ENC-4. Compressing a sandwich by the product projectors sandwiches the compression. -/
theorem topLeft₂_prodP_mul_mul_prodP (P₁' P₂ : L ℋ) (T : L (Reg a (Reg b ℋ))) :
    topLeft₂ (prodP P₁' * T * prodP P₂) = P₁' * topLeft₂ T * P₂ := by
  rw [topLeft₂, prodP, prodP, regTopLeft_atZero_mul_mul_atZero, regTopLeft_atZero_mul_mul_atZero,
    topLeft₂]

/-- ENC-4 (GSLW Lemma 53, projected form). -/
theorem topLeft₂_prodP_prodU (P₁' P₂ : L ℋ) (U₁ : L (Reg a ℋ)) (U₂ : L (Reg b ℋ)) :
    topLeft₂ (prodP P₁' * prodU U₁ U₂ * prodP P₂) = P₁' * (regTopLeft U₁ * regTopLeft U₂) * P₂ := by
  rw [topLeft₂_prodP_mul_mul_prodP, topLeft₂_prodU]

/-! ### The packaged product encoding -/

/-- ENC-4 (GSLW Lemma 53). The product of two projected unitary encodings with separate ancilla
registers: unitary `(1_b ⊗ E₁.U)(1_a ⊗ E₂.U)`, input projector `|0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ P₂`
(the base part of `E₂.P`), output projector `|0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ P₁'` (the base part of
`E₁.P'`). Queries add: `E₁.U` and `E₂.U` are each used once. -/
noncomputable def prodEncoding (E₁ : ProjUnitaryEncoding (Reg a ℋ))
    (E₂ : ProjUnitaryEncoding (Reg b ℋ)) (P₁' P₂ : L ℋ) (hP₁' : IsProjective P₁')
    (hP₂ : IsProjective P₂) : ProjUnitaryEncoding (Reg a (Reg b ℋ)) where
  U := prodU E₁.U E₂.U
  hU := prodU_mem_unitary E₁.U E₂.U E₁.hU E₂.hU
  P := prodP P₂
  P' := prodP P₁'
  hP := prodP_isProjective hP₂
  hP' := prodP_isProjective hP₁'

section prodEncoding

variable (E₁ : ProjUnitaryEncoding (Reg a ℋ)) (E₂ : ProjUnitaryEncoding (Reg b ℋ))
  {P₁' P₂ : L ℋ} (hP₁' : IsProjective P₁') (hP₂ : IsProjective P₂)

@[simp] theorem prodEncoding_U : (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).U = prodU E₁.U E₂.U := rfl

@[simp] theorem prodEncoding_P : (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).P = prodP P₂ := rfl

@[simp] theorem prodEncoding_P' : (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).P' = prodP P₁' := rfl

theorem prodEncoding_encoded :
    (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).encoded = prodP P₁' * prodU E₁.U E₂.U * prodP P₂ := rfl

/-- ENC-4. The compressed encoded operator of the product encoding is
`P₁' (⟨0| E₁.U |0⟩) (⟨0| E₂.U |0⟩) P₂`. -/
theorem topLeft₂_prodEncoding_encoded :
    topLeft₂ (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).encoded =
      P₁' * (regTopLeft E₁.U * regTopLeft E₂.U) * P₂ := by
  rw [prodEncoding_encoded, topLeft₂_prodP_prodU]

/-- ENC-4 (GSLW Lemma 53). If the outer projectors are `|0⟩⟨0| ⊗ P₁'` and `|0⟩⟨0| ⊗ P₂` and the
inner projectors `E₁.P`, `E₂.P'` are the pure ancilla projectors `|0⟩⟨0| ⊗ 1`, the compressed
encoded operator of the product encoding is the product of the compressed encoded operators. -/
theorem prodEncoding_topLeft₂_encoded (h₁' : E₁.P' = atZero P₁') (h₁ : E₁.P = reg0)
    (h₂' : E₂.P' = reg0) (h₂ : E₂.P = atZero P₂) :
    topLeft₂ (prodEncoding E₁ E₂ P₁' P₂ hP₁' hP₂).encoded =
      regTopLeft E₁.encoded * regTopLeft E₂.encoded := by
  rw [topLeft₂_prodEncoding_encoded, ProjUnitaryEncoding.encoded, ProjUnitaryEncoding.encoded,
    h₁', h₁, h₂', h₂, ← atZero_one, ← atZero_one, regTopLeft_atZero_mul_mul_atZero,
    regTopLeft_atZero_mul_mul_atZero, mul_one, one_mul]
  simp only [mul_assoc]

end prodEncoding

/-- ENC-4 (GSLW Lemma 53). The product of two pure block encodings (projectors `|0⟩⟨0| ⊗ 1`):
the product encoding with `P₁' = P₂ = 1`, whose projectors are `|0⟩⟨0|_a ⊗ |0⟩⟨0|_b ⊗ 1`. -/
noncomputable def prodBlockEncoding (E₁ : ProjUnitaryEncoding (Reg a ℋ))
    (E₂ : ProjUnitaryEncoding (Reg b ℋ)) : ProjUnitaryEncoding (Reg a (Reg b ℋ)) :=
  prodEncoding E₁ E₂ 1 1 isProjective_one isProjective_one

section prodBlockEncoding

variable (E₁ : ProjUnitaryEncoding (Reg a ℋ)) (E₂ : ProjUnitaryEncoding (Reg b ℋ))

@[simp] theorem prodBlockEncoding_U : (prodBlockEncoding E₁ E₂).U = prodU E₁.U E₂.U := rfl

@[simp] theorem prodBlockEncoding_P : (prodBlockEncoding E₁ E₂).P = atZero reg0 := rfl

@[simp] theorem prodBlockEncoding_P' : (prodBlockEncoding E₁ E₂).P' = atZero reg0 := rfl

/-- ENC-4 (GSLW Lemma 53). For pure block encodings `E₁`, `E₂` (all projectors `|0⟩⟨0| ⊗ 1`),
the compressed encoded operator of the product encoding is the product `A₁ A₂` of the
compressed encoded operators. -/
theorem prodBlockEncoding_topLeft₂_encoded (h₁ : E₁.P = reg0) (h₁' : E₁.P' = reg0)
    (h₂ : E₂.P = reg0) (h₂' : E₂.P' = reg0) :
    topLeft₂ (prodBlockEncoding E₁ E₂).encoded = regTopLeft E₁.encoded * regTopLeft E₂.encoded :=
  prodEncoding_topLeft₂_encoded E₁ E₂ isProjective_one isProjective_one h₁' h₁ h₂' h₂

end prodBlockEncoding

end QSVT.Encoding
