/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Bridge
import QSVT.Pipeline.ChebLCU

/-!
# The `2^k`-dimensional ancilla register as `k` more qubits (formal-spec CIRC-1, CIRC-5; plan D8)

`QSVT.Qubit.Bridge` identifies the one-ancilla model `Anc (Qubits n) = Qubits n ⊕ Qubits n` with
`Qubits (n + 1)`, the ancilla being the *leading* qubit. This module does the same for the
`m`-dimensional register `Reg m (Qubits n)` of `QSVT.Encoding.Register` when `m = 2 ^ k`: the
register is `Qubits (n + k)`, the ancilla occupying the *first* `k` qubits and the system the
last `n`. The `j`-th summand of the direct sum is the set of bit strings whose first `k` bits
spell `j` in binary (`bitsToFin`, little-endian: bit `i` has weight `2 ^ i`, so index `0` is the
all-`false` string, consistent with `ancEquiv` for `k = 1`).

The identification is a linear isometric equivalence `regEquiv n k`, defined directly on
coordinates: `v : Reg (2 ^ k) (Qubits n)` becomes the function
`b ↦ v (bitsToFin (ancBits b)) (sysBits b)` on bit strings of length `n + k`. Operators are
transported along it (`liftReg`), and the two building blocks of the register layer become the
standard multi-qubit circuit elements:

| register model (`Reg (2 ^ k) (Qubits n)`) | qubit model (`Qubits (n + k)`)              |
|--------------------------------------------|---------------------------------------------|
| `selectOp W = ∑ⱼ |j⟩⟨j| ⊗ Wⱼ`             | `ctrlSelect W` (multiplexed gate)           |
| `selectOp (fun _ => T) = 1 ⊗ T`           | `tensorIdK T` (`T` on the system qubits)    |
| `matOp V = V ⊗ 1`                          | `ancGate V` (`V` on the ancilla qubits)     |
| `reg0 = |0⟩⟨0| ⊗ 1`                       | `zeroProj k` (ancilla bits all `false`)     |
| `lcu V W = matOp Vᴴ * selectOp W * matOp V` | `ancGate Vᴴ * ctrlSelect W * ancGate V`    |

The last line (`liftReg_lcu`) is the circuit form of the `m`-term LCU of ENC-3 (GSLW Lemma 52):
state preparation on the ancilla qubits, the select oracle as a multiplexed gate, and the
inverse state preparation. For the Route A circuit `chebLCU E c` of CERT-A this is
`liftReg_chebLCU`.

## Contents

* `bitsToFin k : (Fin k → Bool) ≃ Fin (2 ^ k)` with `bitsToFin_val`, `bitsToFin_false`,
  `bitsToFin_eq_zero_iff`.
* The split of a string of length `n + k` into ancilla and system bits: `ancBits`, `sysBits`,
  `joinBits`, the equivalence `splitBits n k`, `ancBits_joinBits`, `sysBits_joinBits`,
  `joinBits_ancBits_sysBits`, `eq_joinBits_iff`, and the sum reindexings `sum_joinBits`,
  `sum_bitsToFin`.
* `sysSlice a : Qubits (n + k) →ₗ[ℂ] Qubits n` (the component with ancilla pattern `a`),
  `joinReg`, `norm_joinReg`, and `regEquiv n k : Reg (2 ^ k) (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + k)`
  with `regEquiv_apply`, `regEquiv_apply_joinBits`, `sysSlice_regEquiv`, `regEquiv_inj_ket`,
  `regEquiv_symm_apply`.
* `liftReg T = regEquiv ∘ T ∘ regEquiv⁻¹` with `liftReg_apply`, `liftReg_eq_iff`, `liftReg_mul`,
  `liftReg_one`, `liftReg_add`, `liftReg_smul`, `liftReg_sub`, `liftReg_zero`, `liftReg_adjoint`,
  `liftReg_mem_unitary`, `liftReg_isProjective`, `liftReg_injective`.
* `ctrlSelect W` with `ctrlSelect_apply_coe`, `liftReg_selectOp`, `ctrlSelect_mul`,
  `ctrlSelect_one`, `ctrlSelect_adjoint`, `ctrlSelect_mem_unitary`; `tensorIdK T` with
  `liftReg_selectOp_const`, `tensorIdK_mul`, `tensorIdK_one`, `tensorIdK_adjoint`,
  `tensorIdK_mem_unitary`.
* `ancGate V` with `ancGate_apply_coe`, `liftReg_matOp`, `ancGate_eq_toOp` (its matrix, the
  Kronecker product `V ⊗ₖ 1` in bit-string indices), `ancGate_mul`, `ancGate_one`,
  `ancGate_adjoint`, `ancGate_mem_unitary_of_mem_unitaryGroup`.
* `liftReg_reg0 : liftReg reg0 = zeroProj k`, `liftReg_lcu`, `liftReg_chebLCU`.
* The case `k = 1`: `bitsToFin_one`, `regEquiv_one_apply` (relation to `ancEquiv`),
  `tensorIdK_one_eq_tensorId`.

## Padding (TODO)

The Route A examples of this project use `m = 22, 11, 12, 30` Chebyshev terms, none of which is
a power of two. Padding the coefficient vector with zeros to `m' = 2 ^ k ≥ m` is semantically
harmless: `lcu V' W'` with `V'` preparing the padded weight vector has the same top-left block,
since the extra branches have weight `0` (the normalised coefficient `cNorm c' j = 0` for the
padded indices, so they contribute `0 • W'ⱼ` in `regTopLeft_lcu`). The lemma
`regTopLeft (chebLCU E (pad c)) = regTopLeft (chebLCU E c)` is left as a TODO; this module states
`liftReg_chebLCU` for coefficient vectors `c : Fin (2 ^ k) → ℂ` directly.

## Mathlib API used

`finFunctionFinEquiv` (`Mathlib.Algebra.BigOperators.Fin`), `finTwoEquiv`, `Equiv.arrowCongr`,
`finCongr`, `Fin.appendEquiv`, `Fin.append`, `Fin.castAdd`, `Fin.natAdd`, `Fin.cast`
(`Mathlib.Logic.Equiv.Fin.Basic`, `Mathlib.Data.Fin.Tuple.Basic`); `Equiv.sum_comp`,
`Fintype.sum_prod_type`, `Finset.sum_ite_eq` for the reindexings; `PiLp.norm_sq_eq_of_L2` for
`norm_joinReg`; `LinearEquiv.conj` (`conj_comp`, `conj_id`) and
`LinearIsometryEquiv.inner_map_map` for `liftReg`; `NeZero.pow` for `(0 : Fin (2 ^ k))`.
-/

namespace QSVT.Qubit

open QuantumState QSVT.Encoding QSVT.Pipeline
open scoped Matrix

variable {n k : ℕ}

/-! ### Bit strings as register indices -/

/-- CIRC-1. Little-endian binary encoding of a bit string of length `k` as an index of the
register `Fin (2 ^ k)`: bit `i` has weight `2 ^ i` (`bitsToFin_val`), so the all-`false` string
is `0` (`bitsToFin_false`). -/
def bitsToFin (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- CIRC-1. `bitsToFin a = ∑ᵢ aᵢ 2^i`. -/
theorem bitsToFin_val (a : Fin k → Bool) :
    (bitsToFin k a : ℕ) = ∑ i : Fin k, cond (a i) 1 0 * 2 ^ (i : ℕ) := by
  simp only [bitsToFin, Equiv.trans_apply, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> rfl

@[simp] theorem bitsToFin_false : bitsToFin k (fun _ => false) = 0 := by
  ext
  simp [bitsToFin_val]

theorem bitsToFin_eq_zero_iff (a : Fin k → Bool) : bitsToFin k a = 0 ↔ a = fun _ => false := by
  rw [← bitsToFin_false, Equiv.apply_eq_iff_eq]

/-! ### Splitting a bit string into ancilla and system bits -/

/-- CIRC-1. The ancilla bits of a string of length `n + k`: its first `k` positions. -/
def ancBits (b : Fin (n + k) → Bool) : Fin k → Bool :=
  fun i => b (Fin.cast (Nat.add_comm k n) (Fin.castAdd n i))

/-- CIRC-1. The system bits of a string of length `n + k`: its last `n` positions. -/
def sysBits (b : Fin (n + k) → Bool) : Fin n → Bool :=
  fun j => b (Fin.cast (Nat.add_comm k n) (Fin.natAdd k j))

/-- CIRC-1. Concatenation of an ancilla pattern (first `k` bits) and a system string (last `n`
bits). -/
def joinBits (a : Fin k → Bool) (s : Fin n → Bool) : Fin (n + k) → Bool :=
  Fin.append a s ∘ Fin.cast (Nat.add_comm n k)

/-- The split `b ↦ (ancBits b, sysBits b)` is a bijection with inverse `joinBits`. -/
def splitBits (n k : ℕ) : (Fin (n + k) → Bool) ≃ (Fin k → Bool) × (Fin n → Bool) :=
  (Equiv.arrowCongr (finCongr (Nat.add_comm n k)) (Equiv.refl Bool)).trans
    (Fin.appendEquiv k n).symm

theorem splitBits_apply (b : Fin (n + k) → Bool) : splitBits n k b = (ancBits b, sysBits b) := rfl

theorem splitBits_symm_apply (a : Fin k → Bool) (s : Fin n → Bool) :
    (splitBits n k).symm (a, s) = joinBits a s := rfl

@[simp] theorem ancBits_joinBits (a : Fin k → Bool) (s : Fin n → Bool) :
    ancBits (joinBits a s) = a :=
  congrArg Prod.fst ((splitBits n k).apply_symm_apply (a, s))

@[simp] theorem sysBits_joinBits (a : Fin k → Bool) (s : Fin n → Bool) :
    sysBits (joinBits a s) = s :=
  congrArg Prod.snd ((splitBits n k).apply_symm_apply (a, s))

@[simp] theorem joinBits_ancBits_sysBits (b : Fin (n + k) → Bool) :
    joinBits (ancBits b) (sysBits b) = b :=
  (splitBits n k).symm_apply_apply b

theorem eq_joinBits_iff {b : Fin (n + k) → Bool} {a : Fin k → Bool} {s : Fin n → Bool} :
    b = joinBits a s ↔ ancBits b = a ∧ sysBits b = s := by
  rw [← splitBits_symm_apply, Equiv.eq_symm_apply, splitBits_apply, Prod.mk.injEq]

/-- The ancilla bits vanish iff the first `k` bits of the string vanish (the predicate of
`zeroProj k`). -/
theorem ancBits_eq_false_iff (b : Fin (n + k) → Bool) :
    ancBits b = (fun _ => false) ↔ ∀ i : Fin (n + k), i.val < k → b i = false := by
  constructor
  · intro h i hi
    have := congrFun h ⟨i.val, hi⟩
    simpa only [ancBits, Fin.cast, Fin.castAdd, Fin.castLE] using this
  · intro h
    funext i
    exact h _ i.isLt

/-- Reindexing: a sum over strings of length `n + k` is a double sum over ancilla patterns and
system strings. -/
theorem sum_joinBits {M : Type*} [AddCommMonoid M] (f : (Fin (n + k) → Bool) → M) :
    ∑ b, f b = ∑ a : Fin k → Bool, ∑ s : Fin n → Bool, f (joinBits a s) := by
  rw [← Equiv.sum_comp (splitBits n k).symm f, Fintype.sum_prod_type]
  rfl

/-- Reindexing: a sum over register indices is a sum over ancilla patterns. -/
theorem sum_bitsToFin {M : Type*} [AddCommMonoid M] (g : Fin (2 ^ k) → M) :
    ∑ a : Fin k → Bool, g (bitsToFin k a) = ∑ j, g j :=
  Equiv.sum_comp (bitsToFin k) g

/-! ### The register as `k` more qubits -/

/-- The component of `w : Qubits (n + k)` with ancilla pattern `a`, as a vector on the system
qubits: `sysSlice a w = (s ↦ w (joinBits a s))`. -/
noncomputable def sysSlice (a : Fin k → Bool) : Qubits (n + k) →ₗ[ℂ] Qubits n where
  toFun w := WithLp.toLp 2 fun s => w (joinBits a s)
  map_add' _ _ := PiLp.ext fun _ => rfl
  map_smul' _ _ := PiLp.ext fun _ => rfl

theorem sysSlice_apply (a : Fin k → Bool) (w : Qubits (n + k)) (s : Fin n → Bool) :
    sysSlice a w s = w (joinBits a s) := rfl

/-- The underlying map of `regEquiv`: `v ↦ (b ↦ v (bitsToFin (ancBits b)) (sysBits b))`. -/
noncomputable def joinReg (v : Reg (2 ^ k) (Qubits n)) : Qubits (n + k) :=
  WithLp.toLp 2 fun b => v (bitsToFin k (ancBits b)) (sysBits b)

theorem joinReg_apply (v : Reg (2 ^ k) (Qubits n)) (b : Fin (n + k) → Bool) :
    joinReg v b = v (bitsToFin k (ancBits b)) (sysBits b) := rfl

theorem joinReg_joinBits (v : Reg (2 ^ k) (Qubits n)) (a : Fin k → Bool) (s : Fin n → Bool) :
    joinReg v (joinBits a s) = v (bitsToFin k a) s := by
  rw [joinReg_apply, ancBits_joinBits, sysBits_joinBits]

/-- `joinReg` is an isometry: `‖v‖² = ∑ⱼ ‖vⱼ‖²` is the sum over bit strings split by their
ancilla bits. -/
theorem norm_joinReg (v : Reg (2 ^ k) (Qubits n)) : ‖joinReg v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have h1 : ‖joinReg v‖ ^ 2 = ∑ b, ‖joinReg v b‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have h2 : ‖v‖ ^ 2 = ∑ j, ∑ s, ‖v j s‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun j _ => PiLp.norm_sq_eq_of_L2 _ _
  rw [h1, h2, sum_joinBits, ← sum_bitsToFin]
  simp only [joinReg_joinBits]

/-- CIRC-1 (plan D8). The `2^k`-dimensional register model is the qubit model with the ancilla
as the first `k` qubits: `Reg (2 ^ k) (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + k)`,
`(xⱼ)ⱼ ↦ ∑ⱼ |bits j⟩ ⊗ xⱼ`. -/
noncomputable def regEquiv (n k : ℕ) : Reg (2 ^ k) (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + k) where
  toFun := joinReg
  invFun w := WithLp.toLp 2 fun j => sysSlice ((bitsToFin k).symm j) w
  map_add' v w := PiLp.ext fun b => by
    simp only [joinReg_apply, PiLp.add_apply]
  map_smul' c v := PiLp.ext fun b => by
    simp only [joinReg_apply, PiLp.smul_apply, RingHom.id_apply]
  left_inv v := PiLp.ext fun j => PiLp.ext fun s => by
    change joinReg v (joinBits ((bitsToFin k).symm j) s) = v j s
    rw [joinReg_joinBits, Equiv.apply_symm_apply]
  right_inv w := PiLp.ext fun b => by
    change w (joinBits ((bitsToFin k).symm (bitsToFin k (ancBits b))) (sysBits b)) = w b
    rw [Equiv.symm_apply_apply, joinBits_ancBits_sysBits]
  norm_map' := norm_joinReg

theorem regEquiv_apply (v : Reg (2 ^ k) (Qubits n)) (b : Fin (n + k) → Bool) :
    regEquiv n k v b = v (bitsToFin k (ancBits b)) (sysBits b) := rfl

theorem regEquiv_apply_joinBits (v : Reg (2 ^ k) (Qubits n)) (a : Fin k → Bool)
    (s : Fin n → Bool) : regEquiv n k v (joinBits a s) = v (bitsToFin k a) s :=
  joinReg_joinBits v a s

theorem regEquiv_symm_apply (w : Qubits (n + k)) (j : Fin (2 ^ k)) :
    (regEquiv n k).symm w j = sysSlice ((bitsToFin k).symm j) w := rfl

/-- `sysSlice a (regEquiv v)` is the summand `bitsToFin a` of `v`. -/
theorem sysSlice_regEquiv (a : Fin k → Bool) (v : Reg (2 ^ k) (Qubits n)) :
    sysSlice a (regEquiv n k v) = v (bitsToFin k a) :=
  PiLp.ext fun s => regEquiv_apply_joinBits v a s

/-- CIRC-1. The summand "ancilla `= |j⟩`" is the set of strings with ancilla bits `bits j`:
`inj j |s⟩ ↦ |bits j, s⟩`. -/
theorem regEquiv_inj_ket (j : Fin (2 ^ k)) (s : Fin n → Bool) :
    regEquiv n k (inj j (ket s)) = ket (joinBits ((bitsToFin k).symm j) s) := by
  refine ext_qubits fun b => ?_
  rw [regEquiv_apply, ket_apply, ← proj_apply, proj_inj]
  by_cases h1 : ancBits b = (bitsToFin k).symm j
  · simp [h1, ket_apply, eq_joinBits_iff]
  · have h : bitsToFin k (ancBits b) ≠ j := fun h => h1 (by rw [← h, Equiv.symm_apply_apply])
    simp [h, h1, eq_joinBits_iff]

/-! ### Transport of operators -/

/-- CIRC-1. Transport of an operator on the register model to the qubit model:
`liftReg T = regEquiv ∘ T ∘ regEquiv⁻¹`. -/
noncomputable def liftReg (T : L (Reg (2 ^ k) (Qubits n))) : L (Qubits (n + k)) :=
  (regEquiv n k).toLinearEquiv.conj T

theorem liftReg_apply (T : L (Reg (2 ^ k) (Qubits n))) (w : Qubits (n + k)) :
    liftReg T w = regEquiv n k (T ((regEquiv n k).symm w)) := rfl

theorem liftReg_apply_regEquiv (T : L (Reg (2 ^ k) (Qubits n))) (v : Reg (2 ^ k) (Qubits n)) :
    liftReg T (regEquiv n k v) = regEquiv n k (T v) := by
  rw [liftReg_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The characteristic property of the transport: `liftReg T = S` iff `S` intertwines with `T`
along `regEquiv`. -/
theorem liftReg_eq_iff {T : L (Reg (2 ^ k) (Qubits n))} {S : L (Qubits (n + k))} :
    liftReg T = S ↔ ∀ v, regEquiv n k (T v) = S (regEquiv n k v) := by
  constructor
  · rintro rfl v
    exact (liftReg_apply_regEquiv T v).symm
  · intro h
    refine LinearMap.ext fun w => ?_
    rw [liftReg_apply, h, LinearIsometryEquiv.apply_symm_apply]

theorem liftReg_injective :
    Function.Injective (liftReg : L (Reg (2 ^ k) (Qubits n)) → L (Qubits (n + k))) :=
  (regEquiv n k).toLinearEquiv.conj.injective

theorem liftReg_inj {S T : L (Reg (2 ^ k) (Qubits n))} : liftReg S = liftReg T ↔ S = T :=
  liftReg_injective.eq_iff

/-- CIRC-1. `liftReg` is multiplicative. -/
theorem liftReg_mul (S T : L (Reg (2 ^ k) (Qubits n))) :
    liftReg (S * T) = liftReg S * liftReg T :=
  LinearEquiv.conj_comp _ T S

@[simp] theorem liftReg_one : liftReg (1 : L (Reg (2 ^ k) (Qubits n))) = 1 :=
  LinearEquiv.conj_id _

theorem liftReg_add (S T : L (Reg (2 ^ k) (Qubits n))) :
    liftReg (S + T) = liftReg S + liftReg T :=
  map_add (regEquiv n k).toLinearEquiv.conj S T

theorem liftReg_smul (c : ℂ) (T : L (Reg (2 ^ k) (Qubits n))) :
    liftReg (c • T) = c • liftReg T :=
  map_smul (regEquiv n k).toLinearEquiv.conj c T

theorem liftReg_sub (S T : L (Reg (2 ^ k) (Qubits n))) :
    liftReg (S - T) = liftReg S - liftReg T :=
  map_sub (regEquiv n k).toLinearEquiv.conj S T

@[simp] theorem liftReg_zero : liftReg (0 : L (Reg (2 ^ k) (Qubits n))) = 0 :=
  map_zero (regEquiv n k).toLinearEquiv.conj

/-- CIRC-1. Transport commutes with adjoints (`regEquiv` is an isometry). -/
theorem liftReg_adjoint (T : L (Reg (2 ^ k) (Qubits n))) : liftReg (T†) = (liftReg T)† := by
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  calc inner ℂ (liftReg (T†) x) y
      = inner ℂ (regEquiv n k ((T†) ((regEquiv n k).symm x)))
          (regEquiv n k ((regEquiv n k).symm y)) := by
        rw [liftReg_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ ((T†) ((regEquiv n k).symm x)) ((regEquiv n k).symm y) :=
        (regEquiv n k).inner_map_map _ _
    _ = inner ℂ ((regEquiv n k).symm x) (T ((regEquiv n k).symm y)) :=
        LinearMap.adjoint_inner_left T _ _
    _ = inner ℂ (regEquiv n k ((regEquiv n k).symm x))
          (regEquiv n k (T ((regEquiv n k).symm y))) :=
        ((regEquiv n k).inner_map_map _ _).symm
    _ = inner ℂ x (liftReg T y) := by
        rw [LinearIsometryEquiv.apply_symm_apply, liftReg_apply]

/-- CIRC-1. Transport preserves unitarity. -/
theorem liftReg_mem_unitary {T : L (Reg (2 ^ k) (Qubits n))}
    (hT : T ∈ unitary (L (Reg (2 ^ k) (Qubits n)))) :
    liftReg T ∈ unitary (L (Qubits (n + k))) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, ← liftReg_adjoint, ← liftReg_mul, ← liftReg_mul,
    ← LinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hT, Unitary.mul_star_self_of_mem hT,
    liftReg_one]
  exact ⟨rfl, rfl⟩

/-- Transport preserves projections. -/
theorem liftReg_isProjective {P : L (Reg (2 ^ k) (Qubits n))} (hP : IsProjective P) :
    IsProjective (liftReg P) :=
  isProjective_iff_isStarProjection.mpr
    ⟨show liftReg P * liftReg P = liftReg P by rw [← liftReg_mul, hP.mul_self],
      show star (liftReg P) = liftReg P by
        rw [LinearMap.star_eq_adjoint, ← liftReg_adjoint, hP.adjoint_eq]⟩

/-! ### The select oracle as a multiplexed gate -/

/-- CIRC-5. The multiplexed (uniformly controlled) gate `∑ⱼ |bits j⟩⟨bits j| ⊗ Wⱼ` on
`Qubits (n + k)`: on the component with ancilla pattern `a` it applies `W (bitsToFin a)` to the
system qubits. This is the "select" oracle of the LCU circuit. -/
noncomputable def ctrlSelect (W : Fin (2 ^ k) → L (Qubits n)) : L (Qubits (n + k)) where
  toFun w := WithLp.toLp 2 fun b =>
    W (bitsToFin k (ancBits b)) (sysSlice (ancBits b) w) (sysBits b)
  map_add' w w' := PiLp.ext fun b => by
    simp only [map_add, PiLp.add_apply]
  map_smul' c w := PiLp.ext fun b => by
    simp only [map_smul, PiLp.smul_apply, RingHom.id_apply]

theorem ctrlSelect_apply_coe (W : Fin (2 ^ k) → L (Qubits n)) (w : Qubits (n + k))
    (b : Fin (n + k) → Bool) :
    ctrlSelect W w b = W (bitsToFin k (ancBits b)) (sysSlice (ancBits b) w) (sysBits b) := rfl

/-- CIRC-5. The select operator `∑ⱼ |j⟩⟨j| ⊗ Wⱼ` of the register model is the multiplexed gate
`ctrlSelect W`. -/
theorem liftReg_selectOp (W : Fin (2 ^ k) → L (Qubits n)) :
    liftReg (selectOp W) = ctrlSelect W := by
  rw [liftReg_eq_iff]
  intro v
  refine ext_qubits fun b => ?_
  rw [ctrlSelect_apply_coe, sysSlice_regEquiv, regEquiv_apply]
  rfl

theorem ctrlSelect_mul (W W' : Fin (2 ^ k) → L (Qubits n)) :
    ctrlSelect W * ctrlSelect W' = ctrlSelect fun j => W j * W' j := by
  rw [← liftReg_selectOp, ← liftReg_selectOp, ← liftReg_selectOp, ← liftReg_mul, selectOp_mul]

@[simp] theorem ctrlSelect_one : ctrlSelect (fun _ : Fin (2 ^ k) => (1 : L (Qubits n))) = 1 := by
  rw [← liftReg_selectOp, selectOp_one, liftReg_one]

theorem ctrlSelect_adjoint (W : Fin (2 ^ k) → L (Qubits n)) :
    (ctrlSelect W)† = ctrlSelect fun j => (W j)† := by
  rw [← liftReg_selectOp, ← liftReg_selectOp, ← liftReg_adjoint, selectOp_adjoint]

/-- CIRC-5. The multiplexed gate of unitaries is unitary. -/
theorem ctrlSelect_mem_unitary {W : Fin (2 ^ k) → L (Qubits n)}
    (hW : ∀ j, W j ∈ unitary (L (Qubits n))) :
    ctrlSelect W ∈ unitary (L (Qubits (n + k))) := by
  rw [← liftReg_selectOp]
  exact liftReg_mem_unitary (selectOp_mem_unitary W hW)

/-- CIRC-1. The operator `1 ⊗ T` on `Qubits (n + k)`: `T` acting on the system qubits, the `k`
ancilla qubits untouched. -/
noncomputable def tensorIdK (T : L (Qubits n)) : L (Qubits (n + k)) :=
  ctrlSelect fun _ => T

theorem tensorIdK_apply_coe (T : L (Qubits n)) (w : Qubits (n + k)) (b : Fin (n + k) → Bool) :
    tensorIdK T w b = T (sysSlice (ancBits b) w) (sysBits b) := rfl

/-- CIRC-1. `∑ⱼ |j⟩⟨j| ⊗ T = 1 ⊗ T`. -/
theorem liftReg_selectOp_const (T : L (Qubits n)) :
    liftReg (selectOp fun _ : Fin (2 ^ k) => T) = tensorIdK T :=
  liftReg_selectOp _

theorem tensorIdK_mul (S T : L (Qubits n)) :
    tensorIdK (S * T) = (tensorIdK S * tensorIdK T : L (Qubits (n + k))) := by
  rw [tensorIdK, tensorIdK, tensorIdK, ctrlSelect_mul]

@[simp] theorem tensorIdK_one : tensorIdK (1 : L (Qubits n)) = (1 : L (Qubits (n + k))) :=
  ctrlSelect_one

theorem tensorIdK_adjoint (T : L (Qubits n)) :
    (tensorIdK T : L (Qubits (n + k)))† = tensorIdK (T†) := by
  rw [tensorIdK, tensorIdK, ctrlSelect_adjoint]

/-- CIRC-1. `1 ⊗ U` is unitary when `U` is. -/
theorem tensorIdK_mem_unitary {U : L (Qubits n)} (hU : U ∈ unitary (L (Qubits n))) :
    (tensorIdK U : L (Qubits (n + k))) ∈ unitary (L (Qubits (n + k))) :=
  ctrlSelect_mem_unitary fun _ => hU

/-! ### Ancilla gates -/

/-- CIRC-1. The `k`-qubit gate `V ⊗ 1` on `Qubits (n + k)`: the matrix `V` acting on the ancilla
qubits, the system qubits untouched:
`(V ⊗ 1) w = (b ↦ ∑ⱼ V (bitsToFin (ancBits b)) j · w (joinBits (bits j) (sysBits b)))`. -/
noncomputable def ancGate (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : L (Qubits (n + k)) where
  toFun w := WithLp.toLp 2 fun b =>
    ∑ j, V (bitsToFin k (ancBits b)) j * w (joinBits ((bitsToFin k).symm j) (sysBits b))
  map_add' w w' := PiLp.ext fun b => by
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c w := PiLp.ext fun b => by
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem ancGate_apply_coe (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (w : Qubits (n + k))
    (b : Fin (n + k) → Bool) :
    ancGate V w b =
      ∑ j, V (bitsToFin k (ancBits b)) j * w (joinBits ((bitsToFin k).symm j) (sysBits b)) := rfl

/-- CIRC-1. The ancilla gate `V ⊗ 1` of the register model is the `k`-qubit gate `ancGate V`. -/
theorem liftReg_matOp (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    liftReg (matOp V : L (Reg (2 ^ k) (Qubits n))) = ancGate V := by
  rw [liftReg_eq_iff]
  intro v
  refine ext_qubits fun b => ?_
  rw [ancGate_apply_coe, regEquiv_apply]
  simp only [regEquiv_apply_joinBits, Equiv.apply_symm_apply]
  change (∑ j, V (bitsToFin k (ancBits b)) j • v j) (sysBits b) = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- CIRC-1. The matrix of `V ⊗ 1` is the Kronecker product `V ⊗ₖ 1` in bit-string indices:
`V (bitsToFin (ancBits b)) (bitsToFin (ancBits c))` if `sysBits b = sysBits c`, and `0`
otherwise. -/
theorem ancGate_eq_toOp (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    (ancGate V : L (Qubits (n + k))) =
      toOp (Matrix.of fun b c =>
        if sysBits b = sysBits c then V (bitsToFin k (ancBits b)) (bitsToFin k (ancBits c))
        else 0) := by
  refine LinearMap.ext fun w => ext_qubits fun b => ?_
  rw [ancGate_apply_coe, toOp_apply_coe, sum_joinBits, ← sum_bitsToFin]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.of_apply, ancBits_joinBits, sysBits_joinBits, Equiv.symm_apply_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem ancGate_mul (V W : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    (ancGate V * ancGate W : L (Qubits (n + k))) = ancGate (V * W) := by
  rw [← liftReg_matOp, ← liftReg_matOp, ← liftReg_matOp, ← liftReg_mul, matOp_mul]

@[simp] theorem ancGate_one :
    (ancGate (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : L (Qubits (n + k))) = 1 := by
  rw [← liftReg_matOp, matOp_one, liftReg_one]

/-- CIRC-1. `(V ⊗ 1)† = Vᴴ ⊗ 1`. -/
theorem ancGate_adjoint (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    (ancGate V : L (Qubits (n + k)))† = ancGate Vᴴ := by
  rw [← liftReg_matOp, ← liftReg_matOp, ← liftReg_adjoint, matOp_adjoint]

/-- CIRC-1. A unitary `k`-qubit gate on the ancilla qubits is unitary. -/
theorem ancGate_mem_unitary_of_mem_unitaryGroup {V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin (2 ^ k)) ℂ) :
    (ancGate V : L (Qubits (n + k))) ∈ unitary (L (Qubits (n + k))) := by
  rw [← liftReg_matOp]
  exact liftReg_mem_unitary (matOp_mem_unitary V hV)

/-! ### The ancilla projector and the LCU circuit -/

/-- CIRC-5. The ancilla projector `reg0 = |0⟩⟨0| ⊗ 1` is the projector onto the strings whose
first `k` bits vanish. -/
theorem liftReg_reg0 : liftReg (reg0 : L (Reg (2 ^ k) (Qubits n))) = zeroProj k := by
  rw [reg0, liftReg_selectOp]
  refine LinearMap.ext fun w => ext_qubits fun b => ?_
  rw [ctrlSelect_apply_coe, zeroProj, diagProj_apply_coe]
  by_cases h : ∀ i : Fin (n + k), i.val < k → b i = false
  · have h0 : bitsToFin k (ancBits b) = 0 := by
      rw [bitsToFin_eq_zero_iff, ancBits_eq_false_iff]; exact h
    simp only [h0, decide_eq_true h, ite_true, Module.End.one_apply, sysSlice_apply,
      joinBits_ancBits_sysBits]
  · have h0 : bitsToFin k (ancBits b) ≠ 0 := by
      rw [Ne, bitsToFin_eq_zero_iff, ancBits_eq_false_iff]; exact h
    simp only [h0, decide_eq_false h, ite_false, Bool.false_eq_true, LinearMap.zero_apply,
      PiLp.zero_apply]

/-- CIRC-5 / ENC-3 (GSLW Lemma 52 in the qubit model). The `2^k`-term LCU circuit is: state
preparation `V` on the ancilla qubits, the multiplexed select gate, and `Vᴴ` on the ancilla
qubits. -/
theorem liftReg_lcu (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (W : Fin (2 ^ k) → L (Qubits n)) :
    liftReg (lcu V W) = ancGate Vᴴ * ctrlSelect W * ancGate V := by
  rw [lcu, liftReg_mul, liftReg_mul, liftReg_matOp, liftReg_matOp, liftReg_selectOp]

/-- CIRC-5 / CERT-A. The Route A circuit `chebLCU E c` for `2^k` Chebyshev coefficients, in the
qubit model: Householder state preparation on the `k` ancilla qubits, the multiplexed
Chebyshev unitaries `phase (cₖ) • U_{chebPhases k}`, and the inverse state preparation.
(For a number of terms that is not a power of two, pad `c` with zeros; see the module
docstring.) -/
theorem liftReg_chebLCU (E : HermitianEncoding (Qubits n)) (c : Fin (2 ^ k) → ℂ) :
    liftReg (chebLCU E c) =
      ancGate (householder fun j => ((Real.sqrt ‖cNorm c j‖ : ℝ) : ℂ))ᴴ *
        ctrlSelect (fun j => phase (cNorm c j) • chebUnitary E j) *
        ancGate (householder fun j => ((Real.sqrt ‖cNorm c j‖ : ℝ) : ℂ)) := by
  rw [chebLCU, liftReg_lcu]

-- TODO (padding): for `c : Fin m → ℂ` with `m ≤ 2 ^ k`, extend `c` by zeros to
-- `pad c : Fin (2 ^ k) → ℂ` and show that `regTopLeft (regP E * chebLCU E (pad c) * regP E)` equals
-- `regTopLeft (regP E * chebLCU E c * regP E)` (the padded branches have weight `0` in
-- `regTopLeft_lcu`); then `liftReg_chebLCU` applies to the examples with `m = 22, 11, 12, 30`.

/-! ### The case `k = 1`: consistency with `ancEquiv` and `tensorId` -/

/-- For one ancilla bit, `bitsToFin 1 a = if a 0 then 1 else 0`. -/
theorem bitsToFin_one (a : Fin 1 → Bool) : bitsToFin 1 a = if a 0 then 1 else 0 := by
  ext
  rw [bitsToFin_val, Fin.sum_univ_one]
  cases a 0 <;> simp

theorem ancBits_one (b : Fin (n + 1) → Bool) : ancBits b 0 = b 0 := rfl

/-- For one ancilla bit the system bits are the tail of the string. -/
theorem sysBits_one (b : Fin (n + 1) → Bool) : sysBits b = Fin.tail b :=
  funext fun _ => congrArg b (Fin.ext (Nat.add_comm _ _))

/-- For one ancilla bit `joinBits a s = Fin.cons (a 0) s`. -/
theorem joinBits_one (a : Fin 1 → Bool) (s : Fin n → Bool) : joinBits a s = Fin.cons (a 0) s := by
  funext i
  change Fin.append a s (Fin.cast _ i) = (Fin.cons (a 0) s : Fin (n + 1) → Bool) i
  rw [Fin.append_left_eq_cons]
  rfl

theorem sysSlice_one (a : Fin 1 → Bool) (w : Qubits (n + 1)) : sysSlice a w = slice (a 0) w :=
  PiLp.ext fun s => by rw [sysSlice_apply, slice_apply, joinBits_one]

/-- CIRC-1. For `k = 1`, `regEquiv` is `ancEquiv` composed with `Reg 2 ℋ ≅ Anc ℋ`,
`v ↦ (v 0, v 1)`. -/
theorem regEquiv_one_apply (v : Reg (2 ^ 1) (Qubits n)) :
    regEquiv n 1 v = ancEquiv n (WithLp.toLp 2 (v 0, v 1)) := by
  refine ext_qubits fun b => ?_
  rw [regEquiv_apply, ancEquiv_apply, bitsToFin_one, ancBits_one, sysBits_one]
  cases b 0 <;> rfl

/-- CIRC-1. For `k = 1`, `tensorIdK` is the `tensorId` of `QSVT.Qubit.Bridge`. -/
theorem tensorIdK_one_eq_tensorId (T : L (Qubits n)) :
    (tensorIdK T : L (Qubits (n + 1))) = tensorId T := by
  refine LinearMap.ext fun w => ext_qubits fun b => ?_
  rw [tensorIdK_apply_coe, tensorId_apply_coe, sysBits_one, sysSlice_one, ancBits_one]

end QSVT.Qubit
