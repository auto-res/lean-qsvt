/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic

/-!
# Projected unitary encodings (formal-spec ENC-1)

A *projected unitary encoding* (GSLW Def 11, first half) of an operator `A` on a
finite-dimensional Hilbert space `ℋ` is a unitary `U` together with two orthogonal
projections `Π`, `Π̃` such that `A = Π̃ U Π`.

Since `Π` is not a valid Lean identifier, the projections are called `P` (GSLW `Π`) and
`P'` (GSLW `Π̃`).

* `ProjUnitaryEncoding ℋ`: the structure `(U, P, P')` with its proofs.
* `ProjUnitaryEncoding.encoded E = E.P' * E.U * E.P`: the encoded operator `A`.
* `HermitianEncoding ℋ`: the special case `P' = P` with `A` self-adjoint.
* `ProjUnitaryEncoding.ofUnitary U hU`: the trivial encoding `P = P' = 1` of a unitary.

TODO: the operator-norm bound `‖E.encoded‖ ≤ 1` (spec `encoded_norm_le_one`) needs a
`Norm (L ℋ)` instance (via `LinearMap.toContinuousLinearMap`), which is not set up yet.
-/

namespace QSVT.Encoding

open QuantumState

universe u

/-- ENC-1. Projected unitary encoding (GSLW Def 11, first half): a unitary `U` on `ℋ`
together with orthogonal projections `P` (GSLW `Π`) and `P'` (GSLW `Π̃`). The encoded
operator is `A = P' * U * P` (`ProjUnitaryEncoding.encoded`). -/
structure ProjUnitaryEncoding (ℋ : Type u) [Qudit ℋ] where
  /-- The unitary `U`. -/
  U : L ℋ
  /-- `U` is unitary: `U† * U = 1 ∧ U * U† = 1` (see `U_adjoint_mul_U`, `U_mul_U_adjoint`). -/
  hU : U ∈ unitary (L ℋ)
  /-- The input projection `Π`. -/
  P : L ℋ
  /-- The output projection `Π̃`. -/
  P' : L ℋ
  /-- `P` is an orthogonal projection. -/
  hP : IsProjective P
  /-- `P'` is an orthogonal projection. -/
  hP' : IsProjective P'

variable {ℋ : Type u} [Qudit ℋ]

namespace ProjUnitaryEncoding

variable (E : ProjUnitaryEncoding ℋ)

/-- ENC-1. The encoded operator `A = Π̃ U Π`. -/
def encoded : L ℋ := E.P' * E.U * E.P

@[simp] theorem U_adjoint_mul_U : E.U† * E.U = 1 := Unitary.star_mul_self_of_mem E.hU

@[simp] theorem U_mul_U_adjoint : E.U * E.U† = 1 := Unitary.mul_star_self_of_mem E.hU

/-- Unitarity of `U` in the two-equation form of the specification. -/
theorem hU' : E.U† * E.U = 1 ∧ E.U * E.U† = 1 := ⟨E.U_adjoint_mul_U, E.U_mul_U_adjoint⟩

theorem U_adjoint_mem_unitary : E.U† ∈ unitary (L ℋ) := Unitary.star_mem E.hU

/-- `A† = Π U† Π̃`. -/
theorem encoded_adjoint : (E.encoded)† = E.P * E.U† * E.P' := by
  rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint]
  simp only [encoded, star_mul, E.hP.isSelfAdjoint.star_eq, E.hP'.isSelfAdjoint.star_eq, mul_assoc]

/-- `Π̃ A = A`. -/
theorem P'_mul_encoded : E.P' * E.encoded = E.encoded := by
  rw [encoded, ← mul_assoc, ← mul_assoc, E.hP'.mul_self]

/-- `A Π = A`. -/
theorem encoded_mul_P : E.encoded * E.P = E.encoded := by
  simp only [encoded, mul_assoc, E.hP.mul_self]

/-- The trivial encoding of a unitary by itself: `Π = Π̃ = 1`, so `A = U`. -/
def ofUnitary (U : L ℋ) (hU : U ∈ unitary (L ℋ)) : ProjUnitaryEncoding ℋ where
  U := U
  hU := hU
  P := 1
  P' := 1
  hP := isProjective_one
  hP' := isProjective_one

@[simp] theorem encoded_ofUnitary (U : L ℋ) (hU : U ∈ unitary (L ℋ)) :
    (ofUnitary U hU).encoded = U := by
  simp [encoded, ofUnitary]

end ProjUnitaryEncoding

/-- ENC-1. Hermitian projected unitary encoding: `Π̃ = Π` and `A = Π U Π` is self-adjoint
(the setting of the eigenvalue transformation SVT-3). -/
structure HermitianEncoding (ℋ : Type u) [Qudit ℋ] extends ProjUnitaryEncoding ℋ where
  /-- The two projections coincide. -/
  P'_eq : P' = P
  /-- The encoded operator `A = P' * U * P` is self-adjoint. -/
  encoded_selfAdjoint : IsSelfAdjoint (P' * U * P)

namespace HermitianEncoding

variable (E : HermitianEncoding ℋ)

/-- `A† = A` for a Hermitian encoding. -/
theorem encoded_adjoint_eq : (E.encoded)† = E.encoded := E.encoded_selfAdjoint.star_eq

/-- `A = Π U Π` for a Hermitian encoding. -/
theorem encoded_eq : E.encoded = E.P * E.U * E.P := by
  rw [ProjUnitaryEncoding.encoded, E.P'_eq]

end HermitianEncoding

end QSVT.Encoding
