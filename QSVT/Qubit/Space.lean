/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The `n`-qubit Hilbert space and its matrix calculus (formal-spec CIRC-1)

## Design decision (plan D1)

The core theorems of `lean-qsvt` are basis-independent (`L ℋ` for a `Qudit ℋ`); the circuit
layer works with qubit-indexed matrices. The `n`-qubit Hilbert space is

`Qubits n := EuclideanSpace ℂ (Fin n → Bool)`,

the `L²` space of functions on bit strings of length `n`. Indexing by bit strings (rather than
by `Fin (2 ^ n)`) makes "the operator acting on qubit `i`" and "the register split into its
leading bit and its tail" (`Fin.cons`/`Fin.tail`) definable without `Nat.mul_assoc`-type casts
(see `00note/survey.md` §D).

Operators `L (Qubits n)` and matrices `Matrix (Fin n → Bool) (Fin n → Bool) ℂ` are identified by
Mathlib's `Matrix.toEuclideanLin` (`toOp`, inverse `toMat`); this identification is a ring
isomorphism (`toOp_mul`, `toOp_one`) compatible with adjoints (`toOp_adjoint`, from
`Matrix.toEuclideanLin_conjTranspose_eq_adjoint`), so unitary matrices give unitary operators
(`toOp_mem_unitary_of_mem_unitaryGroup`).

## Contents

* `Qubits n`, `instance : Qudit (Qubits n)`, `finrank_qubits : finrank ℂ (Qubits n) = 2 ^ n`.
* The computational basis `ket b = |b⟩`, `inner_ket_ket`, `norm_ket`, the orthonormal basis
  `ketBasis n` and the extensionality lemma `op_ext_ket`.
* `toOp`, `toMat`, with `toOp_apply_coe : (toOp M w) b = ∑ c, M b c * w c`,
  `toOp_ket_coe : (toOp M (ket c)) b = M b c`, `toOp_mul`, `toOp_one`, `toOp_add`, `toOp_smul`,
  `toOp_adjoint`, `toOp_mem_unitary_of_mem_unitaryGroup`, `toOp_inj`.

## Mathlib API used

`EuclideanSpace`, `EuclideanSpace.single`, `EuclideanSpace.basisFun`, `finrank_euclideanSpace`
(`Mathlib.Analysis.InnerProductSpace.PiL2`); `Matrix.toEuclideanLin = Matrix.toLpLin 2 2` with
`Matrix.toLpLin_apply`, `Matrix.toLpLin_mul_same`, `Matrix.toLpLin_one`
(`Mathlib.Analysis.Normed.Lp.Matrix`); `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`
(`Mathlib.Analysis.InnerProductSpace.Adjoint`); `Matrix.mem_unitaryGroup_iff`,
`Matrix.mem_unitaryGroup_iff'` (`Mathlib.LinearAlgebra.UnitaryGroup`).
-/

namespace QSVT.Qubit

open QuantumState Matrix

/-- CIRC-1. The Hilbert space of `n` qubits, indexed by bit strings: `ℂ^{2^n}` with the
computational basis `|b⟩`, `b : Fin n → Bool`. -/
abbrev Qubits (n : ℕ) : Type := EuclideanSpace ℂ (Fin n → Bool)

variable {n : ℕ}

/-- CIRC-1. `Qubits n` is a qudit (all fields are Mathlib instances on `EuclideanSpace`). -/
noncomputable instance instQuditQubits : Qudit (Qubits n) := {}

/-- CIRC-1. `finrank ℂ (Qubits n) = 2 ^ n`. -/
theorem finrank_qubits : Module.finrank ℂ (Qubits n) = 2 ^ n := by simp

/-! ### The computational basis -/

/-- CIRC-1. The computational basis vector `|b⟩`. -/
noncomputable def ket (b : Fin n → Bool) : Qubits n := EuclideanSpace.single b 1

theorem ket_apply (b c : Fin n → Bool) : ket b c = if c = b then 1 else 0 :=
  PiLp.single_apply 2 ℂ b 1 c

@[simp] theorem ket_apply_self (b : Fin n → Bool) : ket b b = 1 := by simp [ket_apply]

theorem ket_apply_of_ne {b c : Fin n → Bool} (h : c ≠ b) : ket b c = 0 := by simp [ket_apply, h]

/-- CIRC-1. `⟪|b⟩, |c⟩⟫ = δ_{bc}`. -/
theorem inner_ket_ket (b c : Fin n → Bool) : inner ℂ (ket b) (ket c) = if b = c then 1 else 0 := by
  rw [ket, ket, EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]

@[simp] theorem norm_ket (b : Fin n → Bool) : ‖ket b‖ = 1 := by simp [ket]

/-- CIRC-1. The computational basis as an orthonormal basis. -/
noncomputable def ketBasis (n : ℕ) : OrthonormalBasis (Fin n → Bool) ℂ (Qubits n) :=
  EuclideanSpace.basisFun (Fin n → Bool) ℂ

@[simp] theorem ketBasis_apply (b : Fin n → Bool) : ketBasis n b = ket b :=
  EuclideanSpace.basisFun_apply _ ℂ b

/-- Operators on `Qubits n` are determined by their values on the computational basis. -/
theorem op_ext_ket {S T : L (Qubits n)} (h : ∀ b, S (ket b) = T (ket b)) : S = T :=
  (ketBasis n).toBasis.ext fun b => by simpa using h b

/-- Vectors of `Qubits n` are determined by their coefficients. -/
theorem ext_qubits {v w : Qubits n} (h : ∀ b, v b = w b) : v = w := PiLp.ext h

/-! ### Operators and matrices -/

/-- CIRC-1. The operator of a matrix in the computational basis (`Matrix.toEuclideanLin`). -/
noncomputable def toOp (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : L (Qubits n) :=
  Matrix.toEuclideanLin M

/-- CIRC-1. The matrix of an operator in the computational basis. -/
noncomputable def toMat (T : L (Qubits n)) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.toEuclideanLin.symm T

@[simp] theorem toMat_toOp (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : toMat (toOp M) = M :=
  Matrix.toEuclideanLin.symm_apply_apply M

@[simp] theorem toOp_toMat (T : L (Qubits n)) : toOp (toMat T) = T :=
  Matrix.toEuclideanLin.apply_symm_apply T

theorem toOp_injective : Function.Injective (toOp : Matrix (Fin n → Bool) (Fin n → Bool) ℂ → _) :=
  Matrix.toEuclideanLin.injective

theorem toOp_inj {M N : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} : toOp M = toOp N ↔ M = N :=
  toOp_injective.eq_iff

section toOp

variable (M N : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)

theorem toOp_apply (w : Qubits n) : toOp M w = WithLp.toLp 2 (M *ᵥ WithLp.ofLp w) := rfl

/-- `(M w)_b = ∑ c, M b c * w c`. -/
theorem toOp_apply_coe (w : Qubits n) (b : Fin n → Bool) : toOp M w b = ∑ c, M b c * w c := rfl

/-- The columns of `M` are the images of the basis vectors: `(M |c⟩)_b = M b c`. -/
theorem toOp_ket_coe (b c : Fin n → Bool) : toOp M (ket c) b = M b c := by
  simp [toOp_apply_coe, ket_apply]

theorem toOp_ket (c : Fin n → Bool) : toOp M (ket c) = ∑ b, M b c • ket b :=
  ext_qubits fun b => by
    rw [toOp_ket_coe, WithLp.ofLp_sum, Finset.sum_apply]
    simp [ket_apply]

theorem toOp_add : toOp (M + N) = toOp M + toOp N := map_add Matrix.toEuclideanLin M N

theorem toOp_smul (c : ℂ) : toOp (c • M) = c • toOp M := map_smul Matrix.toEuclideanLin c M

theorem toOp_sub : toOp (M - N) = toOp M - toOp N := map_sub Matrix.toEuclideanLin M N

theorem toOp_neg : toOp (-M) = -toOp M := map_neg Matrix.toEuclideanLin M

@[simp] theorem toOp_zero : toOp (0 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 :=
  map_zero Matrix.toEuclideanLin

/-- CIRC-1. `toOp 1 = 1`. -/
@[simp] theorem toOp_one : toOp (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 1 :=
  Matrix.toLpLin_one 2

/-- CIRC-1. `toOp` is multiplicative. -/
theorem toOp_mul : toOp (M * N) = toOp M * toOp N := Matrix.toLpLin_mul_same 2 M N

/-- CIRC-1. The adjoint corresponds to the conjugate transpose. -/
theorem toOp_adjoint : (toOp M)† = toOp Mᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm

/-- CIRC-1. Unitary matrices give unitary operators. -/
theorem toOp_mem_unitary_of_mem_unitaryGroup (hM : M ∈ Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    toOp M ∈ unitary (L (Qubits n)) := by
  have h1 : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hM
  have h2 : M * Mᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hM
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, toOp_adjoint, ← toOp_mul, ← toOp_mul, h1, h2,
    toOp_one]
  exact ⟨rfl, rfl⟩

end toOp

end QSVT.Qubit
