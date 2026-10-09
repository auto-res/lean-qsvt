/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-!
# Basic operator vocabulary on a qudit

Adapted from lean-quantum (https://github.com/Hayata-Yamasaki-Group/lean-quantum;
Apache License 2.0, Copyright 2025 Hayata Yamasaki); the copied declarations keep their
names, so that a later switch to a `lean-quantum` dependency is a drop-in replacement.
The copied file is `Quantum/QuantumMechanics/QuantumState.lean`, whose header reads verbatim:

```
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
```

Copied declarations (namespace `QuantumState`): the class `Qudit`, the abbreviations `L`
(operators) and `I` (identity), the notations `⟨x∣y⟩` (inner product) and `X†` (adjoint),
the trace `Tr`, and the predicates `IsPositiveDefinite`, `IsProjective`, `IsDensity`.
As in lean-quantum, normal / Hermitian / positive-semidefinite / unitary operators are
Mathlib's `IsStarNormal`, `IsSelfAdjoint`, `LinearMap.IsPositive`, `X ∈ unitary (L ℋ)`.

Added here (not in lean-quantum): elementary lemmas about `IsProjective`
(`IsProjective.adjoint_eq`, `IsProjective.mul_self`, `IsProjective.one_sub`,
`IsProjective.mul_one_sub`, `isProjective_one`, `isProjective_zero`, and the bridge
`isProjective_iff_isStarProjection` to Mathlib's `IsStarProjection`).

## Pitfall

The braket notation `⟨x∣y⟩` (kept verbatim from lean-quantum, where it is also never used in
proofs) competes with the anonymous constructor `⟨a, b⟩` and the divisibility notation `x ∣ y`:
when the expected type is known (e.g. `ℂ`) Lean elaborates it as `Complex.mk` and fails.
Write `inner ℂ x y` in proofs.

## Mathlib facts used

* `L ℋ = ℋ →ₗ[ℂ] ℋ` is a `StarRing` with `star = LinearMap.adjoint`
  (`LinearMap.star_eq_adjoint` is `rfl`), so `X†` and `star X` are interchangeable.
* `LinearMap.IsPositive T := T.IsSymmetric ∧ ∀ x, 0 ≤ re ⟪T x, x⟫`; in finite dimension
  `LinearMap.IsPositive.isSelfAdjoint` and `LinearMap.IsSymmetric.adjoint_eq`.
-/

namespace QuantumState

universe u

/-- A qudit: a finite-dimensional complex Hilbert space. -/
class Qudit (a : Type u) extends
  NormedAddCommGroup a,
  InnerProductSpace ℂ a,
  CompleteSpace a,
  FiniteDimensional ℂ a

/-- The (linear) operators on `ℋ`. -/
abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

/-- The identity operator. -/
abbrev I (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : L ℋ :=
  LinearMap.id

/-- Braket notation for the inner product. -/
notation "⟨" x "∣" y "⟩" => inner ℂ x y

/-- The adjoint of an operator (`LinearMap.adjoint`, which is `star` on `L ℋ`). -/
notation X"†" => LinearMap.adjoint X

variable {ℋ : Type u} [Qudit ℋ]

/-- The trace. -/
noncomputable abbrev Tr : L ℋ →ₗ[ℂ] ℂ := LinearMap.trace ℂ ℋ

-- Normal operators are defined by `IsStarNormal`.
example (X : L ℋ) : Prop := IsStarNormal X

-- Hermitian operators are defined by `IsSelfAdjoint`.
example (X : L ℋ) : Prop := IsSelfAdjoint X

-- Positive semidefinite operators are defined by `LinearMap.IsPositive`.
example (X : L ℋ) : Prop := X.IsPositive

/-- Positive definite operators. -/
def IsPositiveDefinite (X : L ℋ) : Prop :=
  X.IsPositive ∧ X.det ≠ 0

/-- Projection operators (orthogonal projections): positive and idempotent. -/
def IsProjective (X : L ℋ) : Prop :=
  X.IsPositive ∧ IsIdempotentElem X

/-- Density operators. -/
def IsDensity (X : L ℋ) : Prop :=
  X.IsPositive ∧ Tr X = 1

-- Unitary operators are defined by `unitary`.
example (X : L ℋ) : Prop := X ∈ unitary (L ℋ)

/-! ### Lemmas on projections (added for lean-qsvt) -/

/-- A self-adjoint idempotent operator is positive: `⟪Q x, x⟫ = ⟪Q x, Q x⟫ ≥ 0`. -/
theorem isPositive_of_isStarProjection {Q : L ℋ} (hQ : IsStarProjection Q) : Q.IsPositive := by
  refine ⟨(LinearMap.isSymmetric_iff_isSelfAdjoint Q).mpr hQ.isSelfAdjoint, fun x => ?_⟩
  have hQQ : Q (Q x) = Q x := by
    rw [← Module.End.mul_apply, hQ.isIdempotentElem.eq]
  have hadj : Q† = Q := hQ.isSelfAdjoint.star_eq
  have key : inner ℂ (Q x) (Q x) = inner ℂ (Q x) x := by
    rw [← LinearMap.adjoint_inner_left Q x (Q x), hadj, hQQ]
  calc (0 : ℝ) ≤ RCLike.re (inner ℂ (Q x) (Q x)) := inner_self_nonneg
    _ = RCLike.re (inner ℂ (Q x) x) := by rw [key]

/-- `IsProjective` agrees with Mathlib's `IsStarProjection` on `L ℋ`. -/
theorem isProjective_iff_isStarProjection {X : L ℋ} :
    IsProjective X ↔ IsStarProjection X :=
  ⟨fun h => ⟨h.2, h.1.isSelfAdjoint⟩,
    fun h => ⟨isPositive_of_isStarProjection h, h.isIdempotentElem⟩⟩

namespace IsProjective

variable {P : L ℋ}

theorem isPositive (h : IsProjective P) : P.IsPositive := h.1

theorem isIdempotentElem (h : IsProjective P) : IsIdempotentElem P := h.2

theorem isStarProjection (h : IsProjective P) : IsStarProjection P :=
  isProjective_iff_isStarProjection.mp h

theorem isSelfAdjoint (h : IsProjective P) : IsSelfAdjoint P := h.1.isSelfAdjoint

/-- A projection is self-adjoint: `P† = P`. -/
theorem adjoint_eq (h : IsProjective P) : P† = P := h.isSelfAdjoint.star_eq

/-- A projection is idempotent: `P * P = P`. -/
theorem mul_self (h : IsProjective P) : P * P = P := h.2.eq

/-- The complementary projection `1 - P`. -/
theorem one_sub (h : IsProjective P) : IsProjective (1 - P) :=
  isProjective_iff_isStarProjection.mpr h.isStarProjection.one_sub

theorem mul_one_sub (h : IsProjective P) : P * (1 - P) = 0 := h.2.mul_one_sub_self

theorem one_sub_mul (h : IsProjective P) : (1 - P) * P = 0 := h.2.one_sub_mul_self

end IsProjective

theorem isProjective_one : IsProjective (1 : L ℋ) :=
  ⟨LinearMap.isPositive_one, IsIdempotentElem.one⟩

theorem isProjective_zero : IsProjective (0 : L ℋ) :=
  ⟨LinearMap.isPositive_zero, IsIdempotentElem.zero⟩

end QuantumState
