/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Space
import QSVT.Encoding.Ancilla

/-!
# Single-qubit gates on an `n`-qubit register (formal-spec CIRC-1)

A one-qubit gate is a matrix `G : Matrix Bool Bool ℂ`; applied to qubit `i` of `Qubits n` it
becomes the operator `applyAt i G = I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I` (`G` in position `i`). With bit-string
indices this is the matrix

`gateMat i G b c = if (∀ j ≠ i, b j = c j) then G (b i) (c i) else 0`,

which avoids Kronecker products and the `Fin (2 ^ n)` casts of the `kron` approach
(`00note/survey.md` §D). The construction is a `*`-homomorphism in `G` (`applyAt_mul`,
`applyAt_one`, `applyAt_adjoint`), so unitary gates give unitary operators
(`applyAt_mem_unitary`), and it acts on the computational basis by
`applyAt i G |c⟩ = ∑ₓ G x (c i) |c[i ↦ x]⟩` (`applyAt_ket`).

## Contents

* `AgreeOff i b c` (bit strings agreeing off position `i`) and the reindexing lemma
  `sum_ite_agreeOff`, which turns a sum over strings agreeing with `b` off `i` into a sum over
  the two values of bit `i`.
* The gate matrices `σx`, `σz`, `hadamardMat`, `rzMat φ = diag(e^{iφ}, e^{−iφ})` with their
  algebra and unitarity (`σx_mem_unitaryGroup`, …).
* `gateMat`, `applyAt` with `applyAt_apply_coe`, `applyAt_ket`, `applyAt_one`, `applyAt_mul`,
  `applyAt_adjoint`, `applyAt_smul`, `applyAt_add`, `applyAt_mem_unitary`.
* The gates `pauliX i`, `pauliZ i`, `hadamard i`, `rz i φ` with involution / group laws,
  adjoints, unitarity, and their action on basis vectors (`pauliX_ket`, `pauliZ_ket`).

`rzMat φ = diag(e^{iφ}, e^{−iφ}) = e^{iφ Z}` matches `QSVT.Encoding.ancPhase φ`, so that
`QSVT.Qubit.Bridge` can identify the ancilla phase with `rz 0 φ`.
-/

namespace QSVT.Qubit

open QuantumState Matrix

variable {n : ℕ}

/-! ### Bit strings agreeing off one position -/

/-- `AgreeOff i b c`: the bit strings `b` and `c` agree on every bit other than `i`. -/
def AgreeOff (i : Fin n) (b c : Fin n → Bool) : Prop := ∀ j, j ≠ i → b j = c j

instance (i : Fin n) (b c : Fin n → Bool) : Decidable (AgreeOff i b c) :=
  inferInstanceAs (Decidable (∀ j, j ≠ i → b j = c j))

theorem agreeOff_refl (i : Fin n) (b : Fin n → Bool) : AgreeOff i b b := fun _ _ => rfl

theorem agreeOff_comm {i : Fin n} {b c : Fin n → Bool} : AgreeOff i b c ↔ AgreeOff i c b :=
  ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem agreeOff_update_left (i : Fin n) (b c : Fin n → Bool) (x : Bool) :
    AgreeOff i (Function.update b i x) c ↔ AgreeOff i b c := by
  unfold AgreeOff
  constructor <;> intro h j hj <;> simpa [Function.update_of_ne hj] using h j hj

theorem agreeOff_update_right (i : Fin n) (b c : Fin n → Bool) (x : Bool) :
    AgreeOff i b (Function.update c i x) ↔ AgreeOff i b c := by
  rw [agreeOff_comm, agreeOff_update_left, agreeOff_comm]

theorem eq_update_iff_agreeOff {i : Fin n} {b c : Fin n → Bool} {x : Bool} :
    c = Function.update b i x ↔ AgreeOff i b c ∧ c i = x := by
  rw [Function.eq_update_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun j hj => (h2 j hj).symm, h1⟩,
    fun ⟨h2, h1⟩ => ⟨h1, fun j hj => (h2 j hj).symm⟩⟩

theorem eq_iff_agreeOff (i : Fin n) {b c : Fin n → Bool} : b = c ↔ AgreeOff i b c ∧ b i = c i := by
  constructor
  · rintro rfl
    exact ⟨agreeOff_refl i b, rfl⟩
  · rintro ⟨h, hi⟩
    funext j
    by_cases hj : j = i
    · subst hj; exact hi
    · exact h j hj

/-- Reindexing: a sum over the bit strings agreeing with `b` off `i` is a sum over the two
values of bit `i`. -/
theorem sum_ite_agreeOff (i : Fin n) (b : Fin n → Bool) (f : (Fin n → Bool) → ℂ) :
    ∑ c, (if AgreeOff i b c then f c else 0) = ∑ x : Bool, f (Function.update b i x) := by
  symm
  calc ∑ x : Bool, f (Function.update b i x)
      = ∑ x : Bool, ∑ c, if c = Function.update b i x then f c else 0 := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ c, ∑ x : Bool, if c = Function.update b i x then f c else 0 := Finset.sum_comm
    _ = ∑ c, if AgreeOff i b c then f c else 0 := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [eq_update_iff_agreeOff]
        by_cases h : AgreeOff i b c
        · simp [h]
        · simp [h]

/-! ### One-qubit gate matrices -/

/-- CIRC-1. The Pauli `X` matrix `[[0, 1], [1, 0]]` (indexed by `Bool`). -/
def σx : Matrix Bool Bool ℂ := Matrix.of fun b c => if b = c then 0 else 1

/-- CIRC-1. The Pauli `Z` matrix `diag(1, −1)`. -/
def σz : Matrix Bool Bool ℂ := Matrix.diagonal fun b => if b then -1 else 1

/-- CIRC-1. The Hadamard matrix `(1/√2) [[1, 1], [1, −1]]`. -/
noncomputable def hadamardMat : Matrix Bool Bool ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • Matrix.of fun b c => if b && c then -1 else 1

/-- CIRC-1. The phase matrix `e^{iφ Z} = diag(e^{iφ}, e^{−iφ})` (the matrix of
`QSVT.Encoding.ancPhase φ`). -/
noncomputable def rzMat (φ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.exp (-(Complex.I * φ)) else Complex.exp (Complex.I * φ)

@[simp] theorem σx_conjTranspose : σxᴴ = σx := by
  ext b c; cases b <;> cases c <;> simp [σx]

@[simp] theorem σx_mul_σx : σx * σx = 1 := by
  ext b c; cases b <;> cases c <;> simp [σx, Matrix.mul_apply]

theorem σx_mem_unitaryGroup : σx ∈ Matrix.unitaryGroup Bool ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, σx_conjTranspose, σx_mul_σx])

@[simp] theorem σz_conjTranspose : σzᴴ = σz := by
  ext b c; cases b <;> cases c <;> simp [σz]

@[simp] theorem σz_mul_σz : σz * σz = 1 := by
  ext b c; cases b <;> cases c <;> simp [σz, Matrix.mul_apply]

theorem σz_mem_unitaryGroup : σz ∈ Matrix.unitaryGroup Bool ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, σz_conjTranspose, σz_mul_σz])

@[simp] theorem hadamardMat_conjTranspose : hadamardMatᴴ = hadamardMat := by
  ext b c; cases b <;> cases c <;> simp [hadamardMat]

@[simp] theorem hadamardMat_mul_hadamardMat : hadamardMat * hadamardMat = 1 := by
  have hc := QSVT.Encoding.invSqrtTwo_mul_self
  ext b c
  cases b <;> cases c <;> simp [hadamardMat, Matrix.mul_apply] <;>
    linear_combination (2 : ℂ) * hc

theorem hadamardMat_mem_unitaryGroup : hadamardMat ∈ Matrix.unitaryGroup Bool ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, hadamardMat_conjTranspose, hadamardMat_mul_hadamardMat])

@[simp] theorem rzMat_zero : rzMat 0 = 1 := by
  rw [rzMat, ← Matrix.diagonal_one]
  congr 1
  funext b
  cases b <;> simp

theorem rzMat_mul_rzMat (φ ψ : ℝ) : rzMat φ * rzMat ψ = rzMat (φ + ψ) := by
  rw [rzMat, rzMat, rzMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> rw [← Complex.exp_add] <;>
    congr 1 <;> push_cast <;> ring

theorem rzMat_conjTranspose (φ : ℝ) : (rzMat φ)ᴴ = rzMat (-φ) := by
  have e1 : Complex.I * ((-φ : ℝ) : ℂ) = -(Complex.I * φ) := by push_cast; ring
  have hc : (starRingEnd ℂ) (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hc' : (starRingEnd ℂ) (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
    rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
      neg_neg]
  rw [rzMat, rzMat, Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  cases b <;> simp [hc, hc']

theorem rzMat_mem_unitaryGroup (φ : ℝ) : rzMat φ ∈ Matrix.unitaryGroup Bool ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, rzMat_conjTranspose, rzMat_mul_rzMat, add_neg_cancel,
      rzMat_zero])

/-! ### Applying a one-qubit gate to qubit `i` -/

/-- CIRC-1. The matrix of the one-qubit gate `G` applied to qubit `i` (identity on the other
qubits): `G (b i) (c i)` if `b` and `c` agree off `i`, and `0` otherwise. -/
def gateMat (i : Fin n) (G : Matrix Bool Bool ℂ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun b c => if AgreeOff i b c then G (b i) (c i) else 0

theorem gateMat_apply (i : Fin n) (G : Matrix Bool Bool ℂ) (b c : Fin n → Bool) :
    gateMat i G b c = if AgreeOff i b c then G (b i) (c i) else 0 := rfl

section gateMat

variable (i : Fin n) (G G' : Matrix Bool Bool ℂ)

@[simp] theorem gateMat_one : gateMat i (1 : Matrix Bool Bool ℂ) = 1 := by
  ext b c
  simp only [gateMat_apply, Matrix.one_apply, eq_iff_agreeOff i, ite_and]

theorem gateMat_mul : gateMat i G * gateMat i G' = gateMat i (G * G') := by
  ext b d
  simp only [Matrix.mul_apply, gateMat_apply, ite_zero_mul]
  rw [sum_ite_agreeOff]
  simp only [Function.update_self, agreeOff_update_left]
  split_ifs with h
  · simp
  · simp

theorem gateMat_conjTranspose : (gateMat i G)ᴴ = gateMat i Gᴴ := by
  ext b c
  simp only [Matrix.conjTranspose_apply, gateMat_apply, agreeOff_comm (b := c)]
  split_ifs <;> simp

theorem gateMat_smul (c : ℂ) : gateMat i (c • G) = c • gateMat i G := by
  ext b d
  simp only [gateMat_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_zero]

theorem gateMat_add : gateMat i (G + G') = gateMat i G + gateMat i G' := by
  ext b d
  simp only [gateMat_apply, Matrix.add_apply]
  split_ifs <;> simp

end gateMat

/-- CIRC-1. The one-qubit gate `G` applied to qubit `i` of `Qubits n`:
`applyAt i G = I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`. -/
noncomputable def applyAt (i : Fin n) (G : Matrix Bool Bool ℂ) : L (Qubits n) :=
  toOp (gateMat i G)

section applyAt

variable (i : Fin n) (G G' : Matrix Bool Bool ℂ)

/-- `(applyAt i G w)_b = ∑ₓ G (b i) x · w (b[i ↦ x])`. -/
theorem applyAt_apply_coe (w : Qubits n) (b : Fin n → Bool) :
    applyAt i G w b = ∑ x : Bool, G (b i) x * w (Function.update b i x) := by
  simp only [applyAt, toOp_apply_coe, gateMat_apply, ite_zero_mul]
  rw [sum_ite_agreeOff]
  simp only [Function.update_self]

/-- CIRC-1. `applyAt i G |c⟩ = ∑ₓ G x (c i) |c[i ↦ x]⟩`. -/
theorem applyAt_ket (c : Fin n → Bool) :
    applyAt i G (ket c) = ∑ x : Bool, G x (c i) • ket (Function.update c i x) := by
  refine ext_qubits fun b => ?_
  rw [applyAt, toOp_ket_coe, gateMat_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, ket_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    eq_update_iff_agreeOff, agreeOff_comm (b := c)]
  by_cases h : AgreeOff i b c
  · simp [h]
  · simp [h]

@[simp] theorem applyAt_one : applyAt i (1 : Matrix Bool Bool ℂ) = 1 := by
  rw [applyAt, gateMat_one, toOp_one]

/-- CIRC-1. `applyAt i` is multiplicative. -/
theorem applyAt_mul : applyAt i G * applyAt i G' = applyAt i (G * G') := by
  rw [applyAt, applyAt, applyAt, ← toOp_mul, gateMat_mul]

/-- CIRC-1. `(applyAt i G)† = applyAt i Gᴴ`. -/
theorem applyAt_adjoint : (applyAt i G)† = applyAt i Gᴴ := by
  rw [applyAt, applyAt, toOp_adjoint, gateMat_conjTranspose]

theorem applyAt_smul (c : ℂ) : applyAt i (c • G) = c • applyAt i G := by
  rw [applyAt, applyAt, gateMat_smul, toOp_smul]

theorem applyAt_add : applyAt i (G + G') = applyAt i G + applyAt i G' := by
  rw [applyAt, applyAt, applyAt, gateMat_add, toOp_add]

/-- CIRC-1. A unitary one-qubit gate applied to qubit `i` is unitary. -/
theorem applyAt_mem_unitary (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    applyAt i G ∈ unitary (L (Qubits n)) := by
  have h1 : Gᴴ * G = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hG
  have h2 : G * Gᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hG
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, applyAt_adjoint, applyAt_mul, applyAt_mul, h1,
    h2, applyAt_one]
  exact ⟨rfl, rfl⟩

end applyAt

/-! ### The standard gates -/

/-- CIRC-1. Pauli `X` on qubit `i`. -/
noncomputable def pauliX (i : Fin n) : L (Qubits n) := applyAt i σx

/-- CIRC-1. Pauli `Z` on qubit `i`. -/
noncomputable def pauliZ (i : Fin n) : L (Qubits n) := applyAt i σz

/-- CIRC-1. Hadamard on qubit `i`. -/
noncomputable def hadamard (i : Fin n) : L (Qubits n) := applyAt i hadamardMat

/-- CIRC-1. The phase gate `e^{iφ Z}` on qubit `i`. -/
noncomputable def rz (i : Fin n) (φ : ℝ) : L (Qubits n) := applyAt i (rzMat φ)

section gates

variable (i : Fin n)

/-- CIRC-1. `X |b⟩ = |b[i ↦ ¬ b i]⟩`. -/
theorem pauliX_ket (b : Fin n → Bool) : pauliX i (ket b) = ket (Function.update b i (!b i)) := by
  rw [pauliX, applyAt_ket, Fintype.sum_bool]
  cases h : b i <;> simp [σx]

@[simp] theorem pauliX_mul_pauliX : pauliX i * pauliX i = 1 := by
  rw [pauliX, applyAt_mul, σx_mul_σx, applyAt_one]

@[simp] theorem pauliX_adjoint : (pauliX i)† = pauliX i := by
  rw [pauliX, applyAt_adjoint, σx_conjTranspose]

theorem pauliX_mem_unitary : pauliX i ∈ unitary (L (Qubits n)) :=
  applyAt_mem_unitary i σx σx_mem_unitaryGroup

/-- CIRC-1. `Z |b⟩ = (−1)^{b i} |b⟩`. -/
theorem pauliZ_ket (b : Fin n → Bool) : pauliZ i (ket b) = (if b i then -1 else 1 : ℂ) • ket b := by
  rw [pauliZ, applyAt_ket, Fintype.sum_bool]
  cases h : b i
  · have e : Function.update b i false = b := by rw [← h]; exact Function.update_eq_self i b
    simp [σz, e]
  · have e : Function.update b i true = b := by rw [← h]; exact Function.update_eq_self i b
    simp [σz, e]

@[simp] theorem pauliZ_mul_pauliZ : pauliZ i * pauliZ i = 1 := by
  rw [pauliZ, applyAt_mul, σz_mul_σz, applyAt_one]

@[simp] theorem pauliZ_adjoint : (pauliZ i)† = pauliZ i := by
  rw [pauliZ, applyAt_adjoint, σz_conjTranspose]

theorem pauliZ_mem_unitary : pauliZ i ∈ unitary (L (Qubits n)) :=
  applyAt_mem_unitary i σz σz_mem_unitaryGroup

@[simp] theorem hadamard_mul_hadamard : hadamard i * hadamard i = 1 := by
  rw [hadamard, applyAt_mul, hadamardMat_mul_hadamardMat, applyAt_one]

@[simp] theorem hadamard_adjoint : (hadamard i)† = hadamard i := by
  rw [hadamard, applyAt_adjoint, hadamardMat_conjTranspose]

theorem hadamard_mem_unitary : hadamard i ∈ unitary (L (Qubits n)) :=
  applyAt_mem_unitary i hadamardMat hadamardMat_mem_unitaryGroup

@[simp] theorem rz_zero : rz i 0 = 1 := by
  rw [rz, rzMat_zero, applyAt_one]

theorem rz_mul_rz (φ ψ : ℝ) : rz i φ * rz i ψ = rz i (φ + ψ) := by
  rw [rz, rz, rz, applyAt_mul, rzMat_mul_rzMat]

theorem rz_adjoint (φ : ℝ) : (rz i φ)† = rz i (-φ) := by
  rw [rz, rz, applyAt_adjoint, rzMat_conjTranspose]

theorem rz_mem_unitary (φ : ℝ) : rz i φ ∈ unitary (L (Qubits n)) :=
  applyAt_mem_unitary i (rzMat φ) (rzMat_mem_unitaryGroup φ)

end gates

end QSVT.Qubit
