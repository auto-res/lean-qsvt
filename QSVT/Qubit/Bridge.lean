/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Gates
import QSVT.Circuit.Gadget

/-!
# The direct-sum ancilla as one more qubit (formal-spec CIRC-1, CIRC-5; plan D1, D8)

The encoding and circuit layers (`QSVT.Encoding.Ancilla`, `QSVT.Circuit.Gadget`) model one
ancilla qubit attached to a qudit `ℋ` by the Hilbert direct sum `Anc ℋ = ℋ ⊕ ℋ` (first summand
= ancilla `|0⟩`). When `ℋ = Qubits n` is itself a qubit register, `Anc (Qubits n)` is just
`Qubits (n + 1)` with the ancilla as the *leading* qubit: the vector `(x₀, x₁)` corresponds to
`|0⟩ ⊗ x₀ + |1⟩ ⊗ x₁`, i.e. to the function `b ↦ x_{b 0} (Fin.tail b)` on bit strings. This
module provides that identification as a linear isometric equivalence `ancEquiv n`, transports
operators along it (`liftAnc`), and identifies the direct-sum primitives with the standard
qubit gates of `QSVT.Qubit.Gates`:

| direct-sum model (`Anc (Qubits n)`) | qubit model (`Qubits (n + 1)`)                 |
|-------------------------------------|------------------------------------------------|
| `blockDiag T T = liftU T = I ⊗ T`   | `tensorId T` (`T` on the tail qubits)          |
| `cpiNot 1 = block 0 1 1 0 = X ⊗ I`  | `pauliX 0`                                     |
| `hadA = H ⊗ I`                      | `hadamard 0`                                   |
| `ancPhase φ = e^{iφ Z} ⊗ I`         | `rz 0 φ`                                       |
| `anc0 = |0⟩⟨0| ⊗ I`                 | `bitProj 0 false`                              |
| `cpiNot (diagProj d)`               | `ctrlX d` (flip qubit `0` iff `d (tail b)`)    |

The last line is CIRC-5: for a projector `Π` that is diagonal in the computational basis
(`diagProj d`, in particular `Π = |0…0⟩⟨0…0| ⊗ I = zeroProj a`), `C_Π NOT` is the
multi-controlled NOT `ctrlX d`, a permutation of the computational basis
(`liftAnc_cpiNot_diagProj`, `liftAnc_cpiNot_zeroProj`, `ctrlX_ket`). The gadget of GSLW
Lemma 19 becomes `ctrlX d * rz 0 (−φ) * ctrlX d` (`liftAnc_gadget_diagProj`).

## Contents

* `slice x : Qubits (n + 1) →ₗ[ℂ] Qubits n` (the component with leading bit `x`), `joinAnc`,
  and `ancEquiv n : Anc (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + 1)` with `ancEquiv_apply`,
  `ancEquiv_apply_cons`, `ancEquiv_inl_ket`, `ancEquiv_inr_ket`, `slice_ancEquiv`.
* `liftAnc T = ancEquiv ∘ T ∘ ancEquiv⁻¹` with `liftAnc_apply`, `liftAnc_eq_iff`, `liftAnc_mul`,
  `liftAnc_one`, `liftAnc_add`, `liftAnc_smul`, `liftAnc_adjoint`, `liftAnc_mem_unitary`,
  `liftAnc_injective`.
* `tensorId T = 1 ⊗ T` with `liftAnc_blockDiag`, `liftAnc_liftU`, the transported algebra
  `tensorId_mul`, `tensorId_one`, `tensorId_adjoint`, `tensorId_mem_unitary`, and its matrix
  (Kronecker product `1 ⊗ₖ M` in bit-string indices) `tensorId_toOp`.
* `liftAnc_block_const` (a block operator with scalar blocks is a gate on qubit `0`) and its
  instances `liftAnc_cpiNot_one`, `liftAnc_hadA`, `liftAnc_ancPhase`, `liftAnc_anc0`.
* Diagonal projectors `diagProj d`, `bitProj i x`, `zeroProj a` (`diagProj_isProjective`, …),
  the controlled flip `flipIf d`, the multi-controlled NOT `ctrlX d` (`ctrlX_apply_coe`,
  `ctrlX_ket`, `ctrlX_mem_unitary`, `ctrlX_true`) and CIRC-5 (`liftAnc_cpiNot_diagProj`,
  `liftAnc_cpiNot_bitProj`, `liftAnc_cpiNot_zeroProj`, `liftAnc_gadget_diagProj`).

## Mathlib API used

`Fin.cons`, `Fin.tail`, `Fin.consEquiv`, `Fin.cons_self_tail`, `Fin.tail_update_zero`
(`Mathlib.Data.Fin.Tuple.Basic`); `PiLp.norm_sq_eq_of_L2`, `WithLp.prod_norm_sq_eq_of_L2`
(`Mathlib.Analysis.Normed.Lp.PiLp`, `ProdLp`) and `Equiv.sum_comp`, `Fintype.sum_prod_type`,
`Fintype.sum_bool` for `norm_joinAnc`; `LinearEquiv.conj` (`conj_apply_apply`, `conj_comp`,
`conj_id`) for `liftAnc`; `LinearIsometryEquiv.inner_map_map` for `liftAnc_adjoint`;
`Function.Involutive.eq_iff`, `Finset.sum_ite_eq` for `ctrlX_apply_coe`. Mathlib also offers
`WithLp.sumPiLpEquivProdLpPiLp` and `LinearIsometryEquiv.piLpCongrLeft`, from which `ancEquiv`
could be assembled; the direct definition keeps `ancEquiv_apply` definitional.

## TODO

The register version `Reg (2 ^ k) (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + k)` (plan D8, `m`-term LCU) is
not yet provided; for `k = 1` it is `ancEquiv` composed with `Reg 2 ℋ ≃ Anc ℋ`.
-/

namespace QSVT.Qubit

open QuantumState QSVT.Encoding QSVT.Circuit

variable {n : ℕ}

/-! ### Splitting a register along its leading qubit -/

/-- The component of `w : Qubits (n + 1)` with leading bit `x`, as a vector on the tail qubits:
`slice x w = (t ↦ w (x :: t))`. -/
noncomputable def slice (x : Bool) : Qubits (n + 1) →ₗ[ℂ] Qubits n where
  toFun w := WithLp.toLp 2 fun t => w (Fin.cons x t)
  map_add' _ _ := PiLp.ext fun _ => rfl
  map_smul' _ _ := PiLp.ext fun _ => rfl

theorem slice_apply (x : Bool) (w : Qubits (n + 1)) (t : Fin n → Bool) :
    slice x w t = w (Fin.cons x t) := rfl

/-- The underlying map of `ancEquiv`: `(x₀, x₁) ↦ (b ↦ x_{b 0} (Fin.tail b))`. -/
noncomputable def joinAnc (v : Anc (Qubits n)) : Qubits (n + 1) :=
  WithLp.toLp 2 fun b => cond (b 0) (snd v (Fin.tail b)) (fst v (Fin.tail b))

theorem joinAnc_apply (v : Anc (Qubits n)) (b : Fin (n + 1) → Bool) :
    joinAnc v b = cond (b 0) (snd v (Fin.tail b)) (fst v (Fin.tail b)) := rfl

theorem joinAnc_cons (v : Anc (Qubits n)) (x : Bool) (t : Fin n → Bool) :
    joinAnc v (Fin.cons x t) = cond x (snd v t) (fst v t) := by
  rw [joinAnc_apply, Fin.cons_zero, Fin.tail_cons]

/-- `joinAnc` is an isometry: `‖(x₀, x₁)‖² = ‖x₀‖² + ‖x₁‖²` is the sum over bit strings split by
the leading bit. -/
theorem norm_joinAnc (v : Anc (Qubits n)) : ‖joinAnc v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, withLp_fst_eq, withLp_snd_eq, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  have hre : ∑ b : Fin (n + 1) → Bool, ‖joinAnc v b‖ ^ 2 =
      ∑ p : Bool × (Fin n → Bool), ‖cond p.1 (snd v p.2) (fst v p.2)‖ ^ 2 :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun p =>
      congrArg (fun z : ℂ => ‖z‖ ^ 2) (joinAnc_cons v p.1 p.2).symm).symm
  rw [hre, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.cond_true, Bool.cond_false]
  exact add_comm _ _

/-- CIRC-1 (plan D8). The direct-sum ancilla model is the qubit model with the ancilla as the
leading qubit: `Anc (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + 1)`, `(x₀, x₁) ↦ |0⟩ ⊗ x₀ + |1⟩ ⊗ x₁`. -/
noncomputable def ancEquiv (n : ℕ) : Anc (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + 1) where
  toFun := joinAnc
  invFun w := WithLp.toLp 2 (slice false w, slice true w)
  map_add' v w := PiLp.ext fun b => by
    simp only [joinAnc_apply, map_add, PiLp.add_apply]
    cases b 0 <;> rfl
  map_smul' c v := PiLp.ext fun b => by
    simp only [joinAnc_apply, map_smul, PiLp.smul_apply, RingHom.id_apply]
    cases b 0 <;> rfl
  left_inv v := ext_anc
    (PiLp.ext fun t => by
      change slice false (joinAnc v) t = fst v t
      rw [slice_apply, joinAnc_cons]; rfl)
    (PiLp.ext fun t => by
      change slice true (joinAnc v) t = snd v t
      rw [slice_apply, joinAnc_cons]; rfl)
  right_inv w := PiLp.ext fun b => by
    rw [joinAnc_apply]
    cases h : b 0
    · change w (Fin.cons false (Fin.tail b)) = w b
      rw [← h, Fin.cons_self_tail]
    · change w (Fin.cons true (Fin.tail b)) = w b
      rw [← h, Fin.cons_self_tail]
  norm_map' := norm_joinAnc

theorem ancEquiv_apply (v : Anc (Qubits n)) (b : Fin (n + 1) → Bool) :
    ancEquiv n v b = cond (b 0) (snd v (Fin.tail b)) (fst v (Fin.tail b)) := rfl

theorem ancEquiv_apply_cons (v : Anc (Qubits n)) (x : Bool) (t : Fin n → Bool) :
    ancEquiv n v (Fin.cons x t) = cond x (snd v t) (fst v t) := joinAnc_cons v x t

theorem fst_ancEquiv_symm (w : Qubits (n + 1)) : fst ((ancEquiv n).symm w) = slice false w := rfl

theorem snd_ancEquiv_symm (w : Qubits (n + 1)) : snd ((ancEquiv n).symm w) = slice true w := rfl

/-- `slice x (ancEquiv v)` is the summand `x` of `v`. -/
theorem slice_ancEquiv (x : Bool) (v : Anc (Qubits n)) :
    slice x (ancEquiv n v) = cond x (snd v) (fst v) :=
  PiLp.ext fun t => by
    rw [slice_apply, ancEquiv_apply_cons]
    cases x <;> rfl

/-- CIRC-1. The summand "ancilla `= |0⟩`" is the leading bit `false`: `inl |t⟩ ↦ |0 t⟩`. -/
theorem ancEquiv_inl_ket (t : Fin n → Bool) :
    ancEquiv n (inl (ket t)) = ket (Fin.cons false t) := by
  refine ext_qubits fun b => ?_
  obtain ⟨x, s, rfl⟩ : ∃ x s, b = Fin.cons x s := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
  rw [ancEquiv_apply_cons, ket_apply]
  simp only [fst_inl, snd_inl, PiLp.zero_apply, ket_apply, Fin.cons_inj]
  cases x <;> simp

/-- CIRC-1. The summand "ancilla `= |1⟩`" is the leading bit `true`: `inr |t⟩ ↦ |1 t⟩`. -/
theorem ancEquiv_inr_ket (t : Fin n → Bool) :
    ancEquiv n (inr (ket t)) = ket (Fin.cons true t) := by
  refine ext_qubits fun b => ?_
  obtain ⟨x, s, rfl⟩ : ∃ x s, b = Fin.cons x s := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
  rw [ancEquiv_apply_cons, ket_apply]
  simp only [fst_inr, snd_inr, PiLp.zero_apply, ket_apply, Fin.cons_inj]
  cases x <;> simp

/-! ### Transport of operators -/

/-- CIRC-1. Transport of an operator on the direct-sum model to the qubit model:
`liftAnc T = ancEquiv ∘ T ∘ ancEquiv⁻¹`. -/
noncomputable def liftAnc (T : L (Anc (Qubits n))) : L (Qubits (n + 1)) :=
  (ancEquiv n).toLinearEquiv.conj T

theorem liftAnc_apply (T : L (Anc (Qubits n))) (w : Qubits (n + 1)) :
    liftAnc T w = ancEquiv n (T ((ancEquiv n).symm w)) := rfl

theorem liftAnc_apply_ancEquiv (T : L (Anc (Qubits n))) (v : Anc (Qubits n)) :
    liftAnc T (ancEquiv n v) = ancEquiv n (T v) := by
  rw [liftAnc_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The characteristic property of the transport: `liftAnc T = S` iff `S` intertwines with `T`
along `ancEquiv`. -/
theorem liftAnc_eq_iff {T : L (Anc (Qubits n))} {S : L (Qubits (n + 1))} :
    liftAnc T = S ↔ ∀ v, ancEquiv n (T v) = S (ancEquiv n v) := by
  constructor
  · rintro rfl v
    exact (liftAnc_apply_ancEquiv T v).symm
  · intro h
    refine LinearMap.ext fun w => ?_
    rw [liftAnc_apply, h, LinearIsometryEquiv.apply_symm_apply]

theorem liftAnc_injective :
    Function.Injective (liftAnc : L (Anc (Qubits n)) → L (Qubits (n + 1))) :=
  (ancEquiv n).toLinearEquiv.conj.injective

theorem liftAnc_inj {S T : L (Anc (Qubits n))} : liftAnc S = liftAnc T ↔ S = T :=
  liftAnc_injective.eq_iff

/-- CIRC-1. `liftAnc` is multiplicative. -/
theorem liftAnc_mul (S T : L (Anc (Qubits n))) : liftAnc (S * T) = liftAnc S * liftAnc T :=
  LinearEquiv.conj_comp _ T S

@[simp] theorem liftAnc_one : liftAnc (1 : L (Anc (Qubits n))) = 1 := LinearEquiv.conj_id _

theorem liftAnc_add (S T : L (Anc (Qubits n))) : liftAnc (S + T) = liftAnc S + liftAnc T :=
  map_add (ancEquiv n).toLinearEquiv.conj S T

theorem liftAnc_smul (c : ℂ) (T : L (Anc (Qubits n))) : liftAnc (c • T) = c • liftAnc T :=
  map_smul (ancEquiv n).toLinearEquiv.conj c T

theorem liftAnc_sub (S T : L (Anc (Qubits n))) : liftAnc (S - T) = liftAnc S - liftAnc T :=
  map_sub (ancEquiv n).toLinearEquiv.conj S T

@[simp] theorem liftAnc_zero : liftAnc (0 : L (Anc (Qubits n))) = 0 :=
  map_zero (ancEquiv n).toLinearEquiv.conj

/-- CIRC-1. Transport commutes with adjoints (`ancEquiv` is an isometry). -/
theorem liftAnc_adjoint (T : L (Anc (Qubits n))) : liftAnc (T†) = (liftAnc T)† := by
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  calc inner ℂ (liftAnc (T†) x) y
      = inner ℂ (ancEquiv n ((T†) ((ancEquiv n).symm x))) (ancEquiv n ((ancEquiv n).symm y)) := by
        rw [liftAnc_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ ((T†) ((ancEquiv n).symm x)) ((ancEquiv n).symm y) :=
        (ancEquiv n).inner_map_map _ _
    _ = inner ℂ ((ancEquiv n).symm x) (T ((ancEquiv n).symm y)) :=
        LinearMap.adjoint_inner_left T _ _
    _ = inner ℂ (ancEquiv n ((ancEquiv n).symm x)) (ancEquiv n (T ((ancEquiv n).symm y))) :=
        ((ancEquiv n).inner_map_map _ _).symm
    _ = inner ℂ x (liftAnc T y) := by rw [LinearIsometryEquiv.apply_symm_apply, liftAnc_apply]

/-- CIRC-1. Transport preserves unitarity. -/
theorem liftAnc_mem_unitary {T : L (Anc (Qubits n))} (hT : T ∈ unitary (L (Anc (Qubits n)))) :
    liftAnc T ∈ unitary (L (Qubits (n + 1))) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, ← liftAnc_adjoint, ← liftAnc_mul, ← liftAnc_mul,
    ← LinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hT, Unitary.mul_star_self_of_mem hT,
    liftAnc_one]
  exact ⟨rfl, rfl⟩

/-- Transport preserves projections. -/
theorem liftAnc_isProjective {P : L (Anc (Qubits n))} (hP : IsProjective P) :
    IsProjective (liftAnc P) :=
  isProjective_iff_isStarProjection.mpr
    ⟨show liftAnc P * liftAnc P = liftAnc P by rw [← liftAnc_mul, hP.mul_self],
      show star (liftAnc P) = liftAnc P by
        rw [LinearMap.star_eq_adjoint, ← liftAnc_adjoint, hP.adjoint_eq]⟩

/-! ### `1 ⊗ T`: an operator on the tail qubits -/

/-- CIRC-1. The operator `1 ⊗ T` on `Qubits (n + 1)`: `T` acting on the tail qubits, the leading
qubit untouched: `(1 ⊗ T) w = (b ↦ (T (slice (b 0) w)) (Fin.tail b))`. -/
noncomputable def tensorId (T : L (Qubits n)) : L (Qubits (n + 1)) where
  toFun w := WithLp.toLp 2 fun b => T (slice (b 0) w) (Fin.tail b)
  map_add' w w' := PiLp.ext fun b => by
    simp only [map_add, PiLp.add_apply]
  map_smul' c w := PiLp.ext fun b => by
    simp only [map_smul, PiLp.smul_apply, RingHom.id_apply]

theorem tensorId_apply_coe (T : L (Qubits n)) (w : Qubits (n + 1)) (b : Fin (n + 1) → Bool) :
    tensorId T w b = T (slice (b 0) w) (Fin.tail b) := rfl

/-- CIRC-1. `|0⟩⟨0| ⊗ T + |1⟩⟨1| ⊗ T` is `1 ⊗ T`. -/
theorem liftAnc_blockDiag (T : L (Qubits n)) : liftAnc (blockDiag T T) = tensorId T := by
  rw [liftAnc_eq_iff]
  intro v
  refine ext_qubits fun b => ?_
  rw [tensorId_apply_coe, slice_ancEquiv, ancEquiv_apply]
  simp only [blockDiag, fst_block, snd_block, LinearMap.zero_apply, add_zero, zero_add]
  cases b 0 <;> rfl

/-- CIRC-1 / CIRC-3. The lifted oracle `liftU U = I ⊗ U` of the gadget layer is `1 ⊗ U`. -/
theorem liftAnc_liftU (U : L (Qubits n)) : liftAnc (liftU U) = tensorId U :=
  liftAnc_blockDiag U

theorem tensorId_mul (S T : L (Qubits n)) : tensorId (S * T) = tensorId S * tensorId T := by
  rw [← liftAnc_blockDiag, ← liftAnc_blockDiag, ← liftAnc_blockDiag, ← blockDiag_mul,
    liftAnc_mul]

@[simp] theorem tensorId_one : tensorId (1 : L (Qubits n)) = 1 := by
  rw [← liftAnc_blockDiag, blockDiag_one, liftAnc_one]

theorem tensorId_adjoint (T : L (Qubits n)) : (tensorId T)† = tensorId (T†) := by
  rw [← liftAnc_blockDiag, ← liftAnc_blockDiag, ← liftAnc_adjoint, blockDiag_adjoint]

/-- CIRC-1. The matrix of `1 ⊗ T` is the Kronecker product `1 ⊗ₖ M` in bit-string indices:
`(1 ⊗ M) b c = M (tail b) (tail c)` if `b 0 = c 0`, and `0` otherwise. -/
theorem tensorId_toOp (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    tensorId (toOp M) =
      toOp (Matrix.of fun b c => if b 0 = c 0 then M (Fin.tail b) (Fin.tail c) else 0) := by
  refine LinearMap.ext fun w => ext_qubits fun b => ?_
  rw [tensorId_apply_coe, toOp_apply_coe, toOp_apply_coe]
  have hre : ∑ c, Matrix.of (fun b c : Fin (n + 1) → Bool =>
      if b 0 = c 0 then M (Fin.tail b) (Fin.tail c) else 0) b c * w c =
      ∑ p : Bool × (Fin n → Bool), (if b 0 = p.1 then M (Fin.tail b) p.2 else 0) *
        w (Fin.cons p.1 p.2) :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun p => by
      change _ = Matrix.of (fun b c : Fin (n + 1) → Bool =>
        if b 0 = c 0 then M (Fin.tail b) (Fin.tail c) else 0) b
          (Fin.cons p.1 p.2 : Fin (n + 1) → Bool) * w (Fin.cons p.1 p.2 : Fin (n + 1) → Bool)
      rw [Matrix.of_apply, Fin.cons_zero, Fin.tail_cons]).symm
  rw [hre, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [slice_apply]
  cases b 0 <;> simp

/-- CIRC-1. `1 ⊗ U` is unitary when `U` is. -/
theorem tensorId_mem_unitary {U : L (Qubits n)} (hU : U ∈ unitary (L (Qubits n))) :
    tensorId U ∈ unitary (L (Qubits (n + 1))) := by
  rw [← liftAnc_blockDiag]
  exact liftAnc_mem_unitary (blockDiag_mem_unitary hU hU)

/-! ### Scalar block operators are gates on the leading qubit -/

/-- CIRC-1. A block operator whose blocks are scalars `G x y • 1` is the one-qubit gate `G` on the
leading qubit: `liftAnc (G ⊗ I) = applyAt 0 G`. -/
theorem liftAnc_block_const (G : Matrix Bool Bool ℂ) :
    liftAnc (block (G false false • (1 : L (Qubits n))) (G false true • 1) (G true false • 1)
      (G true true • 1)) = applyAt 0 G := by
  rw [liftAnc_eq_iff]
  intro v
  refine ext_qubits fun b => ?_
  rw [applyAt_apply_coe, Fintype.sum_bool]
  simp only [ancEquiv_apply, Function.update_self, Fin.tail_update_zero, fst_block, snd_block,
    LinearMap.smul_apply, Module.End.one_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Bool.cond_true, Bool.cond_false]
  cases b 0 <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring

/-- CIRC-1 / CIRC-5. The ancilla `X` (`cpiNot 1 = X ⊗ I`) is Pauli `X` on the leading qubit. -/
theorem liftAnc_cpiNot_one : liftAnc (cpiNot (1 : L (Qubits n))) = pauliX 0 := by
  have h : block (0 : L (Qubits n)) 1 1 0 =
      block (σx false false • 1) (σx false true • 1) (σx true false • 1) (σx true true • 1) := by
    simp [σx]
  rw [cpiNot_one, h, liftAnc_block_const, pauliX]

/-- CIRC-1. The ancilla Hadamard `hadA = H ⊗ I` is the Hadamard on the leading qubit. -/
theorem liftAnc_hadA : liftAnc (hadA : L (Anc (Qubits n))) = hadamard 0 := by
  set Hm : Matrix Bool Bool ℂ := Matrix.of fun b c => if b && c then -1 else 1 with hHm
  have h : block (1 : L (Qubits n)) 1 1 (-1) =
      block (Hm false false • 1) (Hm false true • 1) (Hm true false • 1) (Hm true true • 1) := by
    simp [hHm]
  rw [hadA, liftAnc_smul, h, liftAnc_block_const, hadamard, hadamardMat, applyAt_smul]

/-- CIRC-1 / CIRC-3. The ancilla phase `ancPhase φ = e^{iφ Z} ⊗ I` is `rz 0 φ`. -/
theorem liftAnc_ancPhase (φ : ℝ) : liftAnc (ancPhase φ : L (Anc (Qubits n))) = rz 0 φ := by
  have h : blockDiag (Complex.exp (Complex.I * φ) • (1 : L (Qubits n)))
      (Complex.exp (-(Complex.I * φ)) • 1) =
      block (rzMat φ false false • 1) (rzMat φ false true • 1) (rzMat φ true false • 1)
        (rzMat φ true true • 1) := by
    simp [blockDiag, rzMat]
  rw [ancPhase, h, liftAnc_block_const, rz]

/-! ### Diagonal projectors and the multi-controlled NOT (CIRC-5) -/

/-- CIRC-5. The projector onto the computational basis vectors `|b⟩` with `d b = true`
(diagonal in the computational basis). -/
noncomputable def diagProj (d : (Fin n → Bool) → Bool) : L (Qubits n) :=
  toOp (Matrix.diagonal fun b => if d b then 1 else 0)

theorem diagProj_apply_coe (d : (Fin n → Bool) → Bool) (w : Qubits n) (b : Fin n → Bool) :
    diagProj d w b = if d b then w b else 0 := by
  rw [diagProj, toOp_apply]
  change Matrix.mulVec (Matrix.diagonal _) (WithLp.ofLp w) b = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem diagProj_ket (d : (Fin n → Bool) → Bool) (b : Fin n → Bool) :
    diagProj d (ket b) = if d b then ket b else 0 := by
  split_ifs with h
  · exact ext_qubits fun c => by
      rw [diagProj_apply_coe, ket_apply]
      split_ifs <;> simp_all
  · exact ext_qubits fun c => by
      rw [diagProj_apply_coe, ket_apply]
      split_ifs <;> simp_all

@[simp] theorem diagProj_mul_self (d : (Fin n → Bool) → Bool) :
    diagProj d * diagProj d = diagProj d := by
  rw [diagProj, ← toOp_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext b
  split_ifs <;> simp

@[simp] theorem diagProj_adjoint (d : (Fin n → Bool) → Bool) : (diagProj d)† = diagProj d := by
  rw [diagProj, toOp_adjoint, Matrix.diagonal_conjTranspose]
  congr 2
  funext b
  rw [Pi.star_apply]
  split_ifs <;> simp

/-- CIRC-5. `diagProj d` is an orthogonal projection. -/
theorem diagProj_isProjective (d : (Fin n → Bool) → Bool) : IsProjective (diagProj d) :=
  isProjective_iff_isStarProjection.mpr ⟨diagProj_mul_self d, diagProj_adjoint d⟩

@[simp] theorem diagProj_true : diagProj (fun _ : Fin n → Bool => true) = 1 := by
  simp [diagProj]

/-- CIRC-5. The projector `|x⟩⟨x|` on qubit `i` (identity on the others). -/
noncomputable def bitProj (i : Fin n) (x : Bool) : L (Qubits n) :=
  diagProj fun b => decide (b i = x)

/-- CIRC-5. `bitProj i x` is an orthogonal projection. -/
theorem bitProj_isProjective (i : Fin n) (x : Bool) : IsProjective (bitProj i x) :=
  diagProj_isProjective _

/-- CIRC-5. The projector `Π = |0…0⟩⟨0…0| ⊗ I` onto the strings whose first `a` bits vanish. -/
noncomputable def zeroProj (a : ℕ) : L (Qubits n) :=
  diagProj fun b => decide (∀ i : Fin n, i.val < a → b i = false)

theorem zeroProj_isProjective (a : ℕ) : IsProjective (zeroProj a : L (Qubits n)) :=
  diagProj_isProjective _

/-- CIRC-1 / CIRC-5. The ancilla projector `anc0 = |0⟩⟨0| ⊗ I` is the projector onto leading bit
`false`. -/
theorem liftAnc_anc0 : liftAnc (anc0 : L (Anc (Qubits n))) = bitProj 0 false := by
  set G : Matrix Bool Bool ℂ := Matrix.diagonal fun x : Bool => if x then 0 else 1 with hG
  have h : (anc0 : L (Anc (Qubits n))) =
      block (G false false • 1) (G false true • 1) (G true false • 1) (G true true • 1) := by
    simp [anc0, blockDiag, hG]
  have h' : gateMat 0 G =
      Matrix.diagonal fun b : Fin (n + 1) → Bool => if decide (b 0 = false) then 1 else 0 := by
    ext b c
    simp only [gateMat_apply, hG, Matrix.diagonal_apply, eq_iff_agreeOff 0, ite_and]
    split_ifs <;> simp_all
  rw [h, liftAnc_block_const, bitProj, diagProj, applyAt, h']

/-- CIRC-5. The controlled bit flip on strings of length `n + 1`: flip the leading bit iff the
tail satisfies `d`. -/
def flipIf (d : (Fin n → Bool) → Bool) (c : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  Function.update c 0 (xor (c 0) (d (Fin.tail c)))

theorem flipIf_zero (d : (Fin n → Bool) → Bool) (c : Fin (n + 1) → Bool) :
    flipIf d c 0 = xor (c 0) (d (Fin.tail c)) := Function.update_self _ _ _

theorem tail_flipIf (d : (Fin n → Bool) → Bool) (c : Fin (n + 1) → Bool) :
    Fin.tail (flipIf d c) = Fin.tail c := Fin.tail_update_zero _ _

theorem flipIf_involutive (d : (Fin n → Bool) → Bool) : Function.Involutive (flipIf d) := by
  intro c
  simp only [flipIf, Function.update_self, Fin.tail_update_zero, Function.update_idem,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Function.update_eq_self]

/-- CIRC-5. The multi-controlled NOT: flips the leading qubit exactly on the tail strings
satisfying `d` (the permutation matrix of `flipIf d`). -/
noncomputable def ctrlX (d : (Fin n → Bool) → Bool) : L (Qubits (n + 1)) :=
  toOp (Matrix.of fun b c => if b = flipIf d c then 1 else 0)

theorem ctrlX_apply_coe (d : (Fin n → Bool) → Bool) (w : Qubits (n + 1)) (b : Fin (n + 1) → Bool) :
    ctrlX d w b = w (flipIf d b) := by
  rw [ctrlX, toOp_apply_coe]
  have h : ∀ c, (b = flipIf d c) ↔ (flipIf d b = c) := fun c => by
    rw [eq_comm, (flipIf_involutive d).eq_iff, eq_comm]
  simp only [Matrix.of_apply, h, ite_zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- CIRC-5. `ctrlX d` permutes the computational basis: `|c⟩ ↦ |flipIf d c⟩`. -/
theorem ctrlX_ket (d : (Fin n → Bool) → Bool) (c : Fin (n + 1) → Bool) :
    ctrlX d (ket c) = ket (flipIf d c) :=
  ext_qubits fun b => by
    rw [ctrlX_apply_coe, ket_apply, ket_apply]
    simp only [(flipIf_involutive d).eq_iff]

/-- CIRC-5. `C_Π NOT` for a diagonal projector `Π = diagProj d` is the multi-controlled NOT
`ctrlX d`. -/
theorem liftAnc_cpiNot_diagProj (d : (Fin n → Bool) → Bool) :
    liftAnc (cpiNot (diagProj d)) = ctrlX d := by
  rw [liftAnc_eq_iff]
  intro v
  refine ext_qubits fun b => ?_
  simp only [ctrlX_apply_coe, ancEquiv_apply, flipIf_zero, tail_flipIf, cpiNot, fst_block,
    snd_block, PiLp.add_apply, LinearMap.sub_apply, Module.End.one_apply, PiLp.sub_apply,
    diagProj_apply_coe]
  cases b 0 <;> cases d (Fin.tail b) <;> simp

/-- CIRC-5. `C_Π NOT` for `Π = |x⟩⟨x|` on qubit `i` of the register is the CNOT controlled on
qubit `i + 1` (value `x`) with target the leading qubit. -/
theorem liftAnc_cpiNot_bitProj (i : Fin n) (x : Bool) :
    liftAnc (cpiNot (bitProj i x)) = ctrlX fun b => decide (b i = x) :=
  liftAnc_cpiNot_diagProj _

/-- CIRC-5. `C_Π NOT` for `Π = |0…0⟩⟨0…0| ⊗ I` is the multi-controlled NOT anti-controlled on
the first `a` register qubits. -/
theorem liftAnc_cpiNot_zeroProj (a : ℕ) :
    liftAnc (cpiNot (zeroProj a : L (Qubits n))) =
      ctrlX fun b => decide (∀ i : Fin n, i.val < a → b i = false) :=
  liftAnc_cpiNot_diagProj _

/-- CIRC-5. The trivially controlled NOT is Pauli `X` on the leading qubit. -/
theorem ctrlX_true : ctrlX (fun _ : Fin n → Bool => true) = pauliX 0 := by
  rw [← liftAnc_cpiNot_diagProj, diagProj_true, liftAnc_cpiNot_one]

/-- CIRC-5. `ctrlX d` is unitary. -/
theorem ctrlX_mem_unitary (d : (Fin n → Bool) → Bool) : ctrlX d ∈ unitary (L (Qubits (n + 1))) := by
  rw [← liftAnc_cpiNot_diagProj]
  exact liftAnc_mem_unitary (cpiNot_mem_unitary (diagProj_isProjective d))

@[simp] theorem ctrlX_mul_ctrlX (d : (Fin n → Bool) → Bool) : ctrlX d * ctrlX d = 1 := by
  rw [← liftAnc_cpiNot_diagProj, ← liftAnc_mul, cpiNot_mul_cpiNot (diagProj_isProjective d),
    liftAnc_one]

/-- CIRC-3 / CIRC-5 (GSLW Lemma 19, Fig. 1b, in the qubit model). The gadget for a diagonal
projector is `C_Π NOT · (1 ⊗ e^{−iφ Z}) · C_Π NOT = ctrlX d * rz 0 (−φ) * ctrlX d`. -/
theorem liftAnc_gadget_diagProj (d : (Fin n → Bool) → Bool) (φ : ℝ) :
    liftAnc (gadget (diagProj d) φ) = ctrlX d * rz 0 (-φ) * ctrlX d := by
  rw [gadget, liftAnc_mul, liftAnc_mul, liftAnc_cpiNot_diagProj, liftAnc_ancPhase]

end QSVT.Qubit
