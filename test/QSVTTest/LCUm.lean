/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import QSVT.Encoding.Register
import QSVT.Encoding.LCUm

/-!
# QSVTTest.LCUm

Regression tests for the `m`-dimensional ancilla register (ENC-2, `QSVT.Encoding.Register`) and
the `m`-term LCU with Householder state preparation (ENC-3, `QSVT.Encoding.LCUm`). Each check is
a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding Matrix

universe u

variable {ℋ : Type u} [Qudit ℋ] {m : ℕ}

/-- `Reg m ℋ` is a qudit. -/
noncomputable example : Qudit (Reg m ℋ) := inferInstance

/-- The `k`-th component of `inj k x` is `x`. -/
example (k : Fin m) (x : ℋ) : proj k (inj k x) = x := proj_inj_same k x

/-- Distinct summands are orthogonal. -/
example {j k : Fin m} (h : j ≠ k) (x y : ℋ) : inner ℂ (inj j x) (inj k y) = 0 := by
  simp [inner_inj_inj, h]

/-- `(inj k)† = proj k`. -/
example (k : Fin m) : LinearMap.adjoint (inj k : ℋ →ₗ[ℂ] Reg m ℋ) = proj k := inj_adjoint k

/-- The select operator of constant `1` is the identity. -/
example : selectOp (fun _ : Fin m => (1 : L ℋ)) = (1 : L (Reg m ℋ)) := selectOp_one

/-- The ancilla gate of the identity matrix is the identity. -/
example : matOp (1 : Matrix (Fin m) (Fin m) ℂ) = (1 : L (Reg m ℋ)) := matOp_one

/-- The top-left block of a select operator is its `0`-th entry. -/
example [NeZero m] (W : Fin m → L ℋ) : topLeft (selectOp W) = W 0 := topLeft_selectOp W

/-- `reg0 = |0⟩⟨0| ⊗ 1` is idempotent. -/
example [NeZero m] : (reg0 : L (Reg m ℋ)) * reg0 = reg0 := reg0_mul_reg0

/-- A Householder reflection squares to the identity. -/
example (d : Fin m → ℂ) : reflection d * reflection d = 1 := reflection_mul_self d

/-- The reflection along `0` is the identity. -/
example : reflection (0 : Fin m → ℂ) = 1 := reflection_zero

/-- `householder e₀ = 1`. -/
example [NeZero m] : householder (Pi.single (0 : Fin m) (1 : ℂ)) = 1 := by
  rw [householder, sub_self, reflection_zero]

/-- The LCU of `m` copies of a unitary with uniform weights block-encodes that unitary. -/
example [NeZero m] (U : L ℋ) :
    topLeft (lcu (householder fun _ : Fin m => ((Real.sqrt (1 / (m : ℝ)) : ℝ) : ℂ))
      fun _ => U) = U := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  refine (topLeft_lcu_householder (fun _ : Fin m => 1 / (m : ℝ)) (fun _ => U)
    (fun _ => by positivity) (by simp [hm])).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp

/-- `m = 2`, weights `(1/2, 1/2)`: the Householder LCU block-encodes `(U₀ + U₁)/2`, as `lcu2`. -/
example (U₀ U₁ : L ℋ) :
    topLeft (lcu (householder fun _ : Fin 2 => ((Real.sqrt (1 / 2) : ℝ) : ℂ)) ![U₀, U₁]) =
      (1 / 2 : ℂ) • (U₀ + U₁) := by
  refine (topLeft_lcu_householder (fun _ : Fin 2 => (1 / 2 : ℝ)) ![U₀, U₁]
    (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])).trans ?_
  simp [Fin.sum_univ_two, smul_add]

/-- `m = 2`, coefficients `(1/2, −1/2)`: the complex-coefficient LCU block-encodes
`(U₀ − U₁)/2`. -/
example (U₀ U₁ : L ℋ) :
    topLeft (lcu (householder fun k : Fin 2 => ((Real.sqrt ‖![(1 / 2 : ℂ), -(1 / 2)] k‖ : ℝ) : ℂ))
      fun k => phase (![(1 / 2 : ℂ), -(1 / 2)] k) • ![U₀, U₁] k) = (1 / 2 : ℂ) • (U₀ - U₁) := by
  rw [lcu_complex _ _ (by norm_num [Fin.sum_univ_two])]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The phase of a nonzero complex number has norm one. -/
example : ‖phase (3 + 4 * Complex.I)‖ = 1 := norm_phase _

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Encoding.topLeft_lcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.topLeft_lcu

/-- info: 'QSVT.Encoding.lcu_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.lcu_mem_unitary

/-- info: 'QSVT.Encoding.householder_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.householder_mem_unitaryGroup

/-- info: 'QSVT.Encoding.householder_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.householder_mulVec_single

/-- info: 'QSVT.Encoding.topLeft_lcu_householder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.topLeft_lcu_householder

/-- info: 'QSVT.Encoding.lcu_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.lcu_complex

/-- info: 'QSVT.Encoding.matOp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.matOp_adjoint

/-- info: 'QSVT.Encoding.selectOp_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.selectOp_mem_unitary

/-- info: 'QSVT.Encoding.reg0_isProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Encoding.reg0_isProjective
