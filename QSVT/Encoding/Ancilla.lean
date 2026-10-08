/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# One ancilla qubit as a direct sum, and 2×2 block operators (formal-spec ENC-2)

## Design decision

Instead of a tensor product `ℂ² ⊗ ℋ`, a single ancilla qubit attached to the qudit `ℋ` is
modelled by the Hilbert-space direct sum
`Anc ℋ := WithLp 2 (ℋ × ℋ) ≅ ℋ ⊕ ℋ`,
whose first summand is "ancilla `= |0⟩`" and whose second summand is "ancilla `= |1⟩`".
Mathlib provides the `L²` inner product `⟪(x₀, x₁), (y₀, y₁)⟫ = ⟪x₀, y₀⟫ + ⟪x₁, y₁⟫` on
`WithLp 2 (ℋ × ℋ)` (`WithLp.instProdInnerProductSpace`), so `Anc ℋ` is again a `Qudit`.

An operator on `Anc ℋ` is then a 2×2 *block operator* `block T₀₀ T₀₁ T₁₀ T₁₁` with entries in
`L ℋ`; this is exactly `∑ᵢⱼ |i⟩⟨j| ⊗ Tᵢⱼ` in the tensor-product picture. This suffices for
GSLW Cor 18 (the LCU of `U_Φ` and `U_{−Φ}`, `QSVT.Encoding.LCU`) and for GSLW Lemma 19 (the
ancilla gadget for controlled phase operators). The genuine qubit / tensor-product picture is
deferred to the circuit layer.

## Contents

* `Anc ℋ`, `instance : Qudit (Anc ℋ)`.
* The injections `inl`, `inr : ℋ →ₗ[ℂ] Anc ℋ` and projections `fst`, `snd : Anc ℋ →ₗ[ℂ] ℋ`
  with their inner products, norms and adjoints (`inl_adjoint : inl† = fst`, ...).
* `block T₀₀ T₀₁ T₁₀ T₁₁ : L (Anc ℋ)`, `blockDiag T₀ T₁`, and their algebra: `block_add`,
  `block_smul`, `block_mul_block`, `block_one`, `block_adjoint`, `blockDiag_mul`,
  `blockDiag_adjoint`, `blockDiag_mem_unitary`.
* `topLeft T = fst ∘ T ∘ inl`, the `(0,0)` block `(⟨0| ⊗ I) T (|0⟩ ⊗ I)` of ENC-2.
* The ancilla projector `anc0 = |0⟩⟨0| ⊗ I`, the ancilla Hadamard `hadA = H ⊗ I`, and the
  ancilla phase `ancPhase φ = e^{iφ Z} ⊗ I`.

## Mathlib API used

`WithLp.toLp`/`WithLp.ofLp`, `WithLp.fst`/`WithLp.snd` and the linear maps `WithLp.fstₗ`,
`WithLp.sndₗ` (`Mathlib.Analysis.Normed.Lp.ProdLp`), `WithLp.linearEquiv 2 ℂ (ℋ × ℋ)`
(`Mathlib.Analysis.Normed.Lp.WithLp`), `WithLp.prod_inner_apply`
(`Mathlib.Analysis.InnerProductSpace.ProdL2`), and `LinearMap.adjoint` between two different
finite-dimensional spaces (`LinearMap.eq_adjoint_iff`, `LinearMap.adjoint_inner_left`).
-/

namespace QSVT.Encoding

open QuantumState

universe u

/-- ENC-2. The qudit `ℋ` with one ancilla qubit attached, modelled as the Hilbert-space direct
sum `ℋ ⊕ ℋ` with the `L²` inner product. The first summand is "ancilla `= |0⟩`". -/
abbrev Anc (ℋ : Type u) : Type u := WithLp 2 (ℋ × ℋ)

variable {ℋ : Type u} [Qudit ℋ]

/-- ENC-2. `Anc ℋ` is again a qudit (all fields are Mathlib instances on `WithLp 2 (ℋ × ℋ)`). -/
noncomputable instance instQuditAnc : Qudit (Anc ℋ) := {}

/-! ### Injections and projections -/

/-- Embedding of `ℋ` as the "ancilla `= |0⟩`" summand: `inl x = (x, 0)`. -/
noncomputable def inl : ℋ →ₗ[ℂ] Anc ℋ :=
  (WithLp.linearEquiv 2 ℂ (ℋ × ℋ)).symm.toLinearMap ∘ₗ LinearMap.inl ℂ ℋ ℋ

/-- Embedding of `ℋ` as the "ancilla `= |1⟩`" summand: `inr x = (0, x)`. -/
noncomputable def inr : ℋ →ₗ[ℂ] Anc ℋ :=
  (WithLp.linearEquiv 2 ℂ (ℋ × ℋ)).symm.toLinearMap ∘ₗ LinearMap.inr ℂ ℋ ℋ

/-- Projection onto the "ancilla `= |0⟩`" summand. -/
noncomputable def fst : Anc ℋ →ₗ[ℂ] ℋ := WithLp.fstₗ 2 ℂ ℋ ℋ

/-- Projection onto the "ancilla `= |1⟩`" summand. -/
noncomputable def snd : Anc ℋ →ₗ[ℂ] ℋ := WithLp.sndₗ 2 ℂ ℋ ℋ

theorem inl_apply (x : ℋ) : (inl x : Anc ℋ) = WithLp.toLp 2 (x, 0) := rfl

theorem inr_apply (x : ℋ) : (inr x : Anc ℋ) = WithLp.toLp 2 (0, x) := rfl

theorem fst_apply (v : Anc ℋ) : fst v = v.fst := rfl

theorem snd_apply (v : Anc ℋ) : snd v = v.snd := rfl

/-- Normalize Mathlib's `WithLp.fst` to the linear map `fst` (the simp normal form here). -/
@[simp] theorem withLp_fst_eq (v : Anc ℋ) : v.fst = fst v := rfl

/-- Normalize Mathlib's `WithLp.snd` to the linear map `snd` (the simp normal form here). -/
@[simp] theorem withLp_snd_eq (v : Anc ℋ) : v.snd = snd v := rfl

@[simp] theorem fst_inl (x : ℋ) : fst (inl x) = x := rfl

@[simp] theorem fst_inr (x : ℋ) : fst (inr x) = 0 := rfl

@[simp] theorem snd_inl (x : ℋ) : snd (inl x) = 0 := rfl

@[simp] theorem snd_inr (x : ℋ) : snd (inr x) = x := rfl

/-- Two vectors of `Anc ℋ` agree iff both components agree. -/
theorem ext_anc {v w : Anc ℋ} (h₀ : fst v = fst w) (h₁ : snd v = snd w) : v = w :=
  (WithLp.ext_iff 2).mpr (Prod.ext h₀ h₁)

theorem ext_anc_iff {v w : Anc ℋ} : v = w ↔ fst v = fst w ∧ snd v = snd w :=
  ⟨fun h => ⟨congrArg fst h, congrArg snd h⟩, fun h => ext_anc h.1 h.2⟩

/-- Every vector decomposes as `v = inl (fst v) + inr (snd v)`. -/
@[simp] theorem inl_add_inr (v : Anc ℋ) : inl (fst v) + inr (snd v) = v :=
  ext_anc (by simp) (by simp)

/-- Operators on `Anc ℋ` are determined by their values on the two summands. -/
theorem op_ext_anc {S T : L (Anc ℋ)} (h₀ : ∀ x, S (inl x) = T (inl x))
    (h₁ : ∀ x, S (inr x) = T (inr x)) : S = T := by
  ext v
  rw [← inl_add_inr v, map_add, map_add, h₀, h₁]

/-! ### Inner products, norms and adjoints -/

/-- The `L²` inner product on `Anc ℋ` in terms of the components. -/
theorem inner_anc (v w : Anc ℋ) : inner ℂ v w = inner ℂ (fst v) (fst w) + inner ℂ (snd v) (snd w) :=
  rfl

@[simp] theorem inner_inl_inl (x y : ℋ) : inner ℂ (inl x) (inl y) = inner ℂ x y := by
  rw [inner_anc]; simp

@[simp] theorem inner_inr_inr (x y : ℋ) : inner ℂ (inr x) (inr y) = inner ℂ x y := by
  rw [inner_anc]; simp

@[simp] theorem inner_inl_inr (x y : ℋ) : inner ℂ (inl x) (inr y) = 0 := by
  rw [inner_anc]; simp

@[simp] theorem inner_inr_inl (x y : ℋ) : inner ℂ (inr x) (inl y) = 0 := by
  rw [inner_anc]; simp

@[simp] theorem norm_inl (x : ℋ) : ‖(inl x : Anc ℋ)‖ = ‖x‖ :=
  WithLp.norm_toLp_fst 2 ℋ ℋ x

@[simp] theorem norm_inr (x : ℋ) : ‖(inr x : Anc ℋ)‖ = ‖x‖ :=
  WithLp.norm_toLp_snd 2 ℋ ℋ x

/-- `inl† = fst`. -/
@[simp] theorem inl_adjoint : LinearMap.adjoint (inl : ℋ →ₗ[ℂ] Anc ℋ) = fst :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun v y => by rw [inner_anc]; simp).symm

/-- `inr† = snd`. -/
@[simp] theorem inr_adjoint : LinearMap.adjoint (inr : ℋ →ₗ[ℂ] Anc ℋ) = snd :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun v y => by rw [inner_anc]; simp).symm

/-- `fst† = inl`. -/
@[simp] theorem fst_adjoint : LinearMap.adjoint (fst : Anc ℋ →ₗ[ℂ] ℋ) = inl := by
  rw [← inl_adjoint, LinearMap.adjoint_adjoint]

/-- `snd† = inr`. -/
@[simp] theorem snd_adjoint : LinearMap.adjoint (snd : Anc ℋ →ₗ[ℂ] ℋ) = inr := by
  rw [← inr_adjoint, LinearMap.adjoint_adjoint]

/-! ### Block operators -/

/-- ENC-2. The 2×2 block operator
`block T₀₀ T₀₁ T₁₀ T₁₁ = ∑ᵢⱼ |i⟩⟨j| ⊗ Tᵢⱼ` on `Anc ℋ`:
`(x₀, x₁) ↦ (T₀₀ x₀ + T₀₁ x₁, T₁₀ x₀ + T₁₁ x₁)`. -/
noncomputable def block (T₀₀ T₀₁ T₁₀ T₁₁ : L ℋ) : L (Anc ℋ) :=
  inl ∘ₗ (T₀₀ ∘ₗ fst + T₀₁ ∘ₗ snd) + inr ∘ₗ (T₁₀ ∘ₗ fst + T₁₁ ∘ₗ snd)

/-- The block-diagonal operator `|0⟩⟨0| ⊗ T₀ + |1⟩⟨1| ⊗ T₁`. -/
noncomputable def blockDiag (T₀ T₁ : L ℋ) : L (Anc ℋ) := block T₀ 0 0 T₁

section block

variable (A B C D A' B' C' D' : L ℋ)

theorem block_apply (v : Anc ℋ) :
    block A B C D v = inl (A (fst v) + B (snd v)) + inr (C (fst v) + D (snd v)) := rfl

@[simp] theorem fst_block (v : Anc ℋ) : fst (block A B C D v) = A (fst v) + B (snd v) := by
  simp [block_apply]

@[simp] theorem snd_block (v : Anc ℋ) : snd (block A B C D v) = C (fst v) + D (snd v) := by
  simp [block_apply]

theorem block_apply_inl (x : ℋ) : block A B C D (inl x) = inl (A x) + inr (C x) := by
  simp [block_apply]

theorem block_apply_inr (x : ℋ) : block A B C D (inr x) = inl (B x) + inr (D x) := by
  simp [block_apply]

@[simp] theorem fst_block_inl (x : ℋ) : fst (block A B C D (inl x)) = A x := by simp

@[simp] theorem snd_block_inl (x : ℋ) : snd (block A B C D (inl x)) = C x := by simp

@[simp] theorem fst_block_inr (x : ℋ) : fst (block A B C D (inr x)) = B x := by simp

@[simp] theorem snd_block_inr (x : ℋ) : snd (block A B C D (inr x)) = D x := by simp

/-- Block operators are determined by their four blocks. -/
theorem block_inj :
    block A B C D = block A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  refine ⟨fun h => ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x
    · simpa using congrArg (fun T : L (Anc ℋ) => fst (T (inl x))) h
    · simpa using congrArg (fun T : L (Anc ℋ) => fst (T (inr x))) h
    · simpa using congrArg (fun T : L (Anc ℋ) => snd (T (inl x))) h
    · simpa using congrArg (fun T : L (Anc ℋ) => snd (T (inr x))) h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem block_add :
    block A B C D + block A' B' C' D' = block (A + A') (B + B') (C + C') (D + D') := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp [add_add_add_comm]
  · simp [add_add_add_comm]

theorem block_smul (c : ℂ) : c • block A B C D = block (c • A) (c • B) (c • C) (c • D) := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp
  · simp

theorem block_neg : -block A B C D = block (-A) (-B) (-C) (-D) := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp only [LinearMap.neg_apply, map_neg, fst_block, neg_add]
  · simp only [LinearMap.neg_apply, map_neg, snd_block, neg_add]

theorem block_sub :
    block A B C D - block A' B' C' D' = block (A - A') (B - B') (C - C') (D - D') := by
  rw [sub_eq_add_neg, block_neg, block_add]
  simp only [sub_eq_add_neg]

@[simp] theorem block_zero : block (0 : L ℋ) 0 0 0 = 0 := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp
  · simp

/-- ENC-2. Multiplication of block operators is matrix multiplication of the blocks. -/
theorem block_mul_block :
    block A B C D * block A' B' C' D' =
      block (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp only [Module.End.mul_apply, fst_block, snd_block, map_add, LinearMap.add_apply]
    abel
  · simp only [Module.End.mul_apply, fst_block, snd_block, map_add, LinearMap.add_apply]
    abel

@[simp] theorem block_one : block (1 : L ℋ) 0 0 1 = 1 := by
  refine LinearMap.ext fun v => ext_anc ?_ ?_
  · simp
  · simp

/-- ENC-2. The adjoint of a block operator is the conjugate-transposed block operator. -/
theorem block_adjoint : (block A B C D)† = block (A†) (C†) (B†) (D†) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro v w
  simp only [inner_anc, fst_block, snd_block, inner_add_left, inner_add_right,
    LinearMap.adjoint_inner_left]
  ring

theorem blockDiag_mul (T₀ T₁ S₀ S₁ : L ℋ) :
    blockDiag T₀ T₁ * blockDiag S₀ S₁ = blockDiag (T₀ * S₀) (T₁ * S₁) := by
  simp [blockDiag, block_mul_block]

theorem blockDiag_adjoint (T₀ T₁ : L ℋ) : (blockDiag T₀ T₁)† = blockDiag (T₀†) (T₁†) := by
  simp [blockDiag, block_adjoint]

@[simp] theorem blockDiag_one : blockDiag (1 : L ℋ) 1 = 1 := block_one

theorem blockDiag_smul (c : ℂ) (T₀ T₁ : L ℋ) :
    c • blockDiag T₀ T₁ = blockDiag (c • T₀) (c • T₁) := by
  simp [blockDiag, block_smul]

theorem blockDiag_add (T₀ T₁ S₀ S₁ : L ℋ) :
    blockDiag T₀ T₁ + blockDiag S₀ S₁ = blockDiag (T₀ + S₀) (T₁ + S₁) := by
  simp [blockDiag, block_add]

/-- ENC-2. `|0⟩⟨0| ⊗ T₀ + |1⟩⟨1| ⊗ T₁` is unitary when `T₀` and `T₁` are. -/
theorem blockDiag_mem_unitary {T₀ T₁ : L ℋ} (h₀ : T₀ ∈ unitary (L ℋ)) (h₁ : T₁ ∈ unitary (L ℋ)) :
    blockDiag T₀ T₁ ∈ unitary (L (Anc ℋ)) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, blockDiag_adjoint, blockDiag_mul, blockDiag_mul,
    ← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem h₀,
    Unitary.star_mul_self_of_mem h₁, Unitary.mul_star_self_of_mem h₀,
    Unitary.mul_star_self_of_mem h₁, blockDiag_one]
  exact ⟨rfl, rfl⟩

end block

/-! ### The top-left block -/

/-- ENC-2. The `(0,0)` block `(⟨0| ⊗ I) T (|0⟩ ⊗ I) = fst ∘ T ∘ inl` of an operator on `Anc ℋ`
(GSLW Def 43: the operator block-encoded by `T`). -/
noncomputable def topLeft (T : L (Anc ℋ)) : L ℋ := fst ∘ₗ T ∘ₗ inl

theorem topLeft_apply (T : L (Anc ℋ)) (x : ℋ) : topLeft T x = fst (T (inl x)) := rfl

@[simp] theorem topLeft_block (A B C D : L ℋ) : topLeft (block A B C D) = A := by
  ext x
  simp [topLeft_apply]

@[simp] theorem topLeft_blockDiag (T₀ T₁ : L ℋ) : topLeft (blockDiag T₀ T₁) = T₀ :=
  topLeft_block T₀ 0 0 T₁

theorem topLeft_add (S T : L (Anc ℋ)) : topLeft (S + T) = topLeft S + topLeft T := by
  simp [topLeft, LinearMap.add_comp, LinearMap.comp_add]

theorem topLeft_smul (c : ℂ) (T : L (Anc ℋ)) : topLeft (c • T) = c • topLeft T := by
  simp [topLeft, LinearMap.smul_comp, LinearMap.comp_smul]

@[simp] theorem topLeft_one : topLeft (1 : L (Anc ℋ)) = 1 := by
  rw [← block_one, topLeft_block]

/-! ### The ancilla projector `|0⟩⟨0| ⊗ I` -/

/-- ENC-2. The projector `|0⟩⟨0| ⊗ I` onto the "ancilla `= |0⟩`" summand. -/
noncomputable def anc0 : L (Anc ℋ) := blockDiag 1 0

theorem anc0_apply (v : Anc ℋ) : anc0 v = inl (fst v) := by
  simp [anc0, blockDiag, block_apply]

@[simp] theorem anc0_adjoint : (anc0 : L (Anc ℋ))† = anc0 := by
  rw [anc0, blockDiag_adjoint, LinearMap.adjoint_one, map_zero]

@[simp] theorem anc0_mul_anc0 : (anc0 : L (Anc ℋ)) * anc0 = anc0 := by
  rw [anc0, blockDiag_mul, one_mul, zero_mul]

/-- ENC-2. `|0⟩⟨0| ⊗ I` is an orthogonal projection. -/
theorem anc0_isProjective : IsProjective (anc0 : L (Anc ℋ)) :=
  isProjective_iff_isStarProjection.mpr ⟨anc0_mul_anc0, anc0_adjoint⟩

/-- Compressing a block operator by the ancilla projector keeps only the `(0,0)` block. -/
theorem anc0_mul_block (A B C D : L ℋ) : anc0 * block A B C D * anc0 = block A 0 0 0 := by
  simp [anc0, blockDiag, block_mul_block]

theorem anc0_mul_mul_anc0 (T : L (Anc ℋ)) :
    anc0 * T * anc0 = blockDiag (topLeft T) 0 := by
  refine op_ext_anc (fun x => ?_) (fun x => ?_)
  · simp only [Module.End.mul_apply, anc0_apply, fst_inl, blockDiag, block_apply_inl,
      topLeft_apply, LinearMap.zero_apply, map_zero, add_zero]
  · simp only [Module.End.mul_apply, anc0_apply, fst_inr, map_zero, blockDiag, block_apply_inr,
      LinearMap.zero_apply, add_zero]

/-! ### The ancilla Hadamard `H ⊗ I` -/

/-- ENC-2. The Hadamard gate on the ancilla, `H ⊗ I = (1/√2) [[1, 1], [1, −1]]`. -/
noncomputable def hadA : L (Anc ℋ) := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • block 1 1 1 (-1)

/-- `(1/√2)² = 1/2` in `ℂ`. -/
theorem invSqrtTwo_mul_self : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

theorem hadA_mul_hadA : (hadA : L (Anc ℋ)) * hadA = 1 := by
  rw [hadA, smul_mul_smul_comm, invSqrtTwo_mul_self, block_mul_block, block_smul]
  simp only [mul_one, mul_neg, neg_neg, add_neg_cancel, smul_zero]
  rw [← two_smul ℂ (1 : L ℋ), smul_smul, one_div, inv_mul_cancel₀ (two_ne_zero' ℂ), one_smul,
    block_one]

theorem hadA_adjoint : (hadA : L (Anc ℋ))† = hadA := by
  rw [hadA, map_smulₛₗ LinearMap.adjoint, block_adjoint, LinearMap.adjoint_one, map_neg,
    LinearMap.adjoint_one]
  congr 1
  rw [starRingEnd_apply, Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- ENC-2. `H ⊗ I` is unitary. -/
theorem hadA_mem_unitary : (hadA : L (Anc ℋ)) ∈ unitary (L (Anc ℋ)) :=
  Unitary.mem_iff.mpr ⟨by rw [LinearMap.star_eq_adjoint, hadA_adjoint, hadA_mul_hadA],
    by rw [LinearMap.star_eq_adjoint, hadA_adjoint, hadA_mul_hadA]⟩

/-! ### The ancilla phase `e^{iφ Z} ⊗ I` -/

/-- ENC-2 / GSLW Lemma 19. The phase gate `e^{iφ Z} ⊗ I = diag(e^{iφ}, e^{−iφ}) ⊗ I` on the
ancilla; it is the ancilla-side ingredient of the gadget realizing `phaseOp` by a controlled
phase. -/
noncomputable def ancPhase (φ : ℝ) : L (Anc ℋ) :=
  blockDiag (Complex.exp (Complex.I * φ) • 1) (Complex.exp (-(Complex.I * φ)) • 1)

@[simp] theorem ancPhase_zero : (ancPhase 0 : L (Anc ℋ)) = 1 := by
  simp [ancPhase]

theorem ancPhase_mul_ancPhase (φ ψ : ℝ) :
    (ancPhase φ : L (Anc ℋ)) * ancPhase ψ = ancPhase (φ + ψ) := by
  have e1 : Complex.I * ((φ + ψ : ℝ) : ℂ) = Complex.I * φ + Complex.I * ψ := by
    push_cast; ring
  simp only [ancPhase, blockDiag_mul, smul_mul_smul_comm, one_mul, e1, neg_add, Complex.exp_add]

theorem ancPhase_adjoint (φ : ℝ) : (ancPhase φ : L (Anc ℋ))† = ancPhase (-φ) := by
  have e1 : Complex.I * ((-φ : ℝ) : ℂ) = -(Complex.I * φ) := by push_cast; ring
  have hc : (starRingEnd ℂ) (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hc' : (starRingEnd ℂ) (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
    rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
      neg_neg]
  rw [ancPhase, blockDiag_adjoint, map_smulₛₗ LinearMap.adjoint, map_smulₛₗ LinearMap.adjoint,
    LinearMap.adjoint_one, hc, hc', ancPhase, e1, neg_neg]

/-- ENC-2. `e^{iφ Z} ⊗ I` is unitary. -/
theorem ancPhase_mem_unitary (φ : ℝ) : (ancPhase φ : L (Anc ℋ)) ∈ unitary (L (Anc ℋ)) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, ancPhase_adjoint, ancPhase_mul_ancPhase,
    ancPhase_mul_ancPhase, neg_add_cancel, add_neg_cancel, ancPhase_zero]
  exact ⟨rfl, rfl⟩

end QSVT.Encoding
