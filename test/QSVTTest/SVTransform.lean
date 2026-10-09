/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.NormBound
import QSVT.SVT.SVTransform

/-!
# QSVTTest.SVTransform

Regression tests for SVT-4 (`QSVT.SVT.NormBound`) and SVT-5 (`QSVT.SVT.SVTransform`).
Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### SVT-5: constant and linear polynomials -/

/-- `svTransform 1 E = Π`. -/
example (E : ProjUnitaryEncoding ℋ) : svTransform 1 E = E.P :=
  svTransform_one E

/-- `svTransform X E = A`. -/
example (E : ProjUnitaryEncoding ℋ) : svTransform X E = E.encoded :=
  svTransform_X E

/-- `svTransform (X ^ 2) E = Π A†A Π`. -/
example (E : ProjUnitaryEncoding ℋ) :
    svTransform (X ^ 2) E = E.P * (E.encoded† * E.encoded) * E.P :=
  svTransform_X_sq E

/-- The trivial encoding of a unitary `U` (`Π = Π̃ = 1`): `svTransform X` is `U` itself. -/
example (U : L ℋ) (hU : U ∈ unitary (L ℋ)) :
    svTransform X (ProjUnitaryEncoding.ofUnitary U hU) = U := by
  rw [svTransform_X, ProjUnitaryEncoding.encoded_ofUnitary]

/-- Linearity: `svTransform (1 + X) E = Π + A`. -/
example (E : ProjUnitaryEncoding ℋ) : svTransform (1 + X) E = E.P + E.encoded := by
  rw [svTransform_add, svTransform_one, svTransform_X]

/-- Hermitian consistency with SVT-3, specialised to `p = X`: `A = A Π`. -/
example (E : HermitianEncoding ℋ) : E.encoded = E.encoded * E.P := by
  have h := svTransform_eq_aeval E X
  rwa [svTransform_X, aeval_X] at h

/-! ### SVT-4: the bound specialised to a constant polynomial -/

/-- For `p = 1` the bound reads `‖Π x‖ ≤ 1 * ‖x‖`. -/
example (E : HermitianEncoding ℋ) (x : ℋ) : ‖(aeval E.encoded (1 : ℂ[X]) * E.P) x‖ ≤ 1 * ‖x‖ := by
  have h := norm_aeval_mul_P_apply_le E 1 x
  rwa [supNorm_one] at h

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.norm_aeval_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.norm_aeval_apply_le

/-- info: 'QSVT.SVT.norm_aeval_sub_mul_P_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.norm_aeval_sub_mul_P_apply_le

/-- info: 'QSVT.SVT.opNorm_aeval_mul_P_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.opNorm_aeval_mul_P_le

/-- info: 'QSVT.SVT.svTransform_eq_aeval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.svTransform_eq_aeval
