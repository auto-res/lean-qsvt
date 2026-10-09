/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Swap
import QSVT.Encoding.Product

/-!
# QSVTTest.Product

Regression tests for the register swap and the two lifts (`QSVT.Encoding.Swap`) and the product
of block encodings (ENC-4, GSLW Lemma 53, `QSVT.Encoding.Product`). Each check is a compile-time
assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.IR

universe u

variable {ℋ : Type u} [Qudit ℋ] {a b : ℕ}

/-! ### The register swap -/

/-- The swap exchanges the two coordinates. -/
example (v : Reg a (Reg b ℋ)) (i : Fin a) (j : Fin b) : swapReg v j i = v i j := swapReg_apply v j i

/-- The swap is involutive. -/
example (v : Reg a (Reg b ℋ)) : swapReg.symm (swapReg v) = v := swapReg.symm_apply_apply v

/-- The swap preserves inner products (it is a `LinearIsometryEquiv`). -/
example (v w : Reg a (Reg b ℋ)) : inner ℂ (swapReg v) (swapReg w) = inner ℂ v w :=
  swapReg.inner_map_map v w

/-- The swap preserves norms. -/
example (v : Reg a (Reg b ℋ)) : ‖swapReg v‖ = ‖v‖ := swapReg.norm_map v

/-- `swap |i⟩|j⟩|x⟩ = |j⟩|i⟩|x⟩`. -/
example (i : Fin a) (j : Fin b) (x : ℋ) :
    swapReg (inj i (inj j x) : Reg a (Reg b ℋ)) = inj j (inj i x) := swapReg_inj_inj i j x

/-- Transport of the identity is the identity. -/
example : conjSwap (1 : L (Reg b (Reg a ℋ))) = 1 := conjSwap_one

/-! ### The lifts -/

/-- `1_a ⊗ T₂` on a product vector. -/
example (T₂ : L (Reg b ℋ)) (i : Fin a) (y : Reg b ℋ) :
    innerLift T₂ (inj i y : Reg a (Reg b ℋ)) = inj i (T₂ y) := innerLift_inj T₂ i y

/-- `T₁ ⊗ 1_b` acts slice-wise. -/
example (T₁ : L (Reg a ℋ)) (j : Fin b) (v : Reg a (Reg b ℋ)) :
    slice j (outerLift T₁ v) = T₁ (slice j v) := slice_outerLift T₁ j v

/-- Both lifts of the identity are the identity. -/
example : (outerLift (1 : L (Reg a ℋ)) : L (Reg a (Reg b ℋ))) = 1 := outerLift_one

example : (innerLift (1 : L (Reg b ℋ)) : L (Reg a (Reg b ℋ))) = 1 := innerLift_one

/-! ### The product (GSLW Lemma 53) -/

section

variable [NeZero a] [NeZero b]

/-- The compressed product circuit is the product of the compressed circuits. -/
example (U₁ : L (Reg a ℋ)) (U₂ : L (Reg b ℋ)) :
    topLeft₂ (prodU U₁ U₂) = regTopLeft U₁ * regTopLeft U₂ := topLeft₂_prodU U₁ U₂

/-- Compressing the product projector returns the base projector. -/
example (P : L ℋ) : topLeft₂ (prodP P : L (Reg a (Reg b ℋ))) = P := topLeft₂_prodP P

/-- Trivially lifted operators (`1 ⊗ A`, `1 ⊗ B`): the product encodes `A * B`. -/
example (A B : L ℋ) :
    topLeft₂ (prodU (selectOp fun _ : Fin a => A) (selectOp fun _ : Fin b => B)) = A * B := by
  rw [topLeft₂_prodU, regTopLeft_selectOp, regTopLeft_selectOp]

/-- The projected form with `P₁'` on the left and `P₂` on the right. -/
example (P₁' P₂ A B : L ℋ) :
    topLeft₂ (prodP P₁' * prodU (selectOp fun _ : Fin a => A) (selectOp fun _ : Fin b => B) *
      prodP P₂) = P₁' * (A * B) * P₂ := by
  rw [topLeft₂_prodP_prodU, regTopLeft_selectOp, regTopLeft_selectOp]

end

/-- On a one-dimensional register the ancilla projector `|0⟩⟨0| ⊗ 1` is the identity. -/
theorem reg0_fin_one : (reg0 : L (Reg 1 ℋ)) = 1 := by
  rw [reg0, ← selectOp_one]
  congr 1
  funext k
  simp [Subsingleton.elim k 0]

/-- `a = b = 1`: the product of the trivial encodings of two unitaries encodes their product. -/
example (U₁ U₂ : L ℋ) (h₁ : U₁ ∈ unitary (L ℋ)) (h₂ : U₂ ∈ unitary (L ℋ)) :
    topLeft₂ (prodBlockEncoding
      (ProjUnitaryEncoding.ofUnitary (selectOp fun _ : Fin 1 => U₁)
        (selectOp_mem_unitary _ fun _ => h₁))
      (ProjUnitaryEncoding.ofUnitary (selectOp fun _ : Fin 1 => U₂)
        (selectOp_mem_unitary _ fun _ => h₂))).encoded = U₁ * U₂ := by
  rw [prodBlockEncoding_topLeft₂_encoded _ _ reg0_fin_one.symm reg0_fin_one.symm reg0_fin_one.symm
    reg0_fin_one.symm, ProjUnitaryEncoding.encoded_ofUnitary, ProjUnitaryEncoding.encoded_ofUnitary,
    regTopLeft_selectOp, regTopLeft_selectOp]

/-- `a = b = 1`: the product circuit of two trivially lifted unitaries is unitary. -/
example (U₁ U₂ : L ℋ) (h₁ : U₁ ∈ unitary (L ℋ)) (h₂ : U₂ ∈ unitary (L ℋ)) :
    prodU (selectOp fun _ : Fin 1 => U₁) (selectOp fun _ : Fin 1 => U₂) ∈
      unitary (L (Reg 1 (Reg 1 ℋ))) :=
  prodU_mem_unitary _ _ (selectOp_mem_unitary _ fun _ => h₁) (selectOp_mem_unitary _ fun _ => h₂)

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Encoding.swapReg_inj_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.swapReg_inj_inj

/-- info: 'QSVT.Encoding.inner_swapRegₗ_swapRegₗ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.inner_swapRegₗ_swapRegₗ

/-- info: 'QSVT.Encoding.conjSwap_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.conjSwap_adjoint

/-- info: 'QSVT.Encoding.outerLift_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.outerLift_mem_unitary

/-- info: 'QSVT.Encoding.prodU_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.prodU_mem_unitary

/-- info: 'QSVT.Encoding.topLeft₂_prodU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.topLeft₂_prodU

/-- info: 'QSVT.Encoding.prodEncoding_topLeft₂_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.prodEncoding_topLeft₂_encoded

/-- info: 'QSVT.Encoding.prodBlockEncoding_topLeft₂_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.prodBlockEncoding_topLeft₂_encoded

/-- info: 'QSVT.Encoding.prodP_eq_innerLift_mul_outerLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.prodP_eq_innerLift_mul_outerLift
