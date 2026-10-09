/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import QSVT.Encoding.Ancilla
import QSVT.Encoding.LCU

/-!
# QSVTTest.LCU

Regression tests for the one-ancilla block-operator layer (ENC-2, `QSVT.Encoding.Ancilla`) and
the two-term LCU (ENC-3, `QSVT.Encoding.LCU`). Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- `Anc ℋ` is a qudit. -/
noncomputable example : Qudit (Anc ℋ) := inferInstance

/-- The first component of `inl x` is `x`. -/
example (x : ℋ) : fst (inl x) = x := fst_inl x

/-- The second component of `inl x` is `0`. -/
example (x : ℋ) : snd (inl x) = 0 := snd_inl x

/-- `inl` and `inr` are orthogonal. -/
example (x y : ℋ) : inner ℂ (inl x) (inr y) = 0 := inner_inl_inr x y

/-- The top-left block of a block-diagonal operator is its `(0,0)` entry. -/
example (T₀ T₁ : L ℋ) : topLeft (blockDiag T₀ T₁) = T₀ := topLeft_blockDiag T₀ T₁

/-- The top-left block of a general block operator. -/
example (A B C D : L ℋ) : topLeft (block A B C D) = A := topLeft_block A B C D

/-- `anc0 = |0⟩⟨0| ⊗ I` is idempotent. -/
example : (anc0 : L (Anc ℋ)) * anc0 = anc0 := anc0_mul_anc0

/-- `H ⊗ I` squares to the identity. -/
example : (hadA : L (Anc ℋ)) * hadA = 1 := hadA_mul_hadA

/-- The LCU of a unitary with itself block-encodes that unitary. -/
example (U : L ℋ) : topLeft (lcu2 U U) = U := by
  rw [topLeft_lcu2, ← two_smul ℂ U, smul_smul, one_div, inv_mul_cancel₀ (two_ne_zero' ℂ),
    one_smul]

/-- The LCU of `U` and `−U` block-encodes `0`. -/
example (U : L ℋ) : topLeft (lcu2 U (-U)) = 0 := by
  rw [topLeft_lcu2, add_neg_cancel, smul_zero]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Encoding.topLeft_lcu2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.topLeft_lcu2

/-- info: 'QSVT.Encoding.lcu2_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.lcu2_mem_unitary

/-- info: 'QSVT.Encoding.block_mul_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.block_mul_block

/-- info: 'QSVT.Encoding.block_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.block_adjoint

/-- info: 'QSVT.Encoding.anc0_isProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.anc0_isProjective

/-- info: 'QSVT.Encoding.hadA_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.hadA_mem_unitary
