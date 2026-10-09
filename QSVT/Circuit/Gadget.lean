/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.RealPoly

/-!
# The ancilla gadget for projector-controlled phases (formal-spec CIRC-3, GSLW Lemma 19)

GSLW Fig. 1b implements the phase operator `e^{iφ(2Π−I)}` with one ancilla qubit, two
`C_Π NOT` gates and a single-qubit phase on the ancilla:

`C_Π NOT · (e^{−iφ Z} ⊗ I) · C_Π NOT = |0⟩⟨0| ⊗ e^{iφ(2Π−I)} + |1⟩⟨1| ⊗ e^{−iφ(2Π−I)}`.

## The direct-sum model

As in `QSVT.Encoding.Ancilla`, the ancilla qubit is modelled by the direct sum
`Anc ℋ = ℋ ⊕ ℋ` (first summand = ancilla `|0⟩`), so that every operator on `Anc ℋ` is a 2×2
block operator with entries in `L ℋ`. In this model

* `C_Π NOT = X ⊗ Π + I ⊗ (I − Π)` is the block operator `cpiNot P = block (1−P) P P (1−P)`;
  in particular `cpiNot 1 = block 0 1 1 0` is the plain `X` on the ancilla (`cpiNot_one`);
* `I ⊗ U` is `liftU U = blockDiag U U`;
* `e^{−iφ Z} ⊗ I` is `ancPhase (−φ)` of `QSVT.Encoding.Ancilla`.

The qubit / tensor-product picture (mapping `Anc`/`Reg` to tensor products of qubits and
`cpiNot` to multi-controlled NOTs, CIRC-5) is deferred to the qubit circuit layer.

## Contents

* `cpiNot P` with `cpiNot_mul_cpiNot`, `cpiNot_adjoint`, `cpiNot_mem_unitary`, `cpiNot_one`.
* `liftU U = I ⊗ U` with `liftU_mul`, `liftU_adjoint`, `liftU_one`, `liftU_mem_unitary`.
* `gadget P φ = cpiNot P * ancPhase (−φ) * cpiNot P` and the identity of GSLW Fig. 1b,
  `gadget_eq : gadget P φ = blockDiag (phaseOp P φ) (phaseOp P (−φ))`; its `(0,0)` block is
  `phaseOp P φ` (`topLeft_gadget`).
* `gadgetSeq E Φ`, the alternating sequence `altSeq E Φ` of SVT-1 driven through the gadgets
  with the oracle lifted to `I ⊗ U`, and `gadgetSeq_eq : gadgetSeq E Φ =
  blockDiag (altSeq E Φ) (altSeq E (−Φ))`: the ancilla simultaneously drives `U_Φ` and
  `U_{−Φ}`, which is exactly what GSLW Cor 18 needs.
* `qsvtReal_U_eq_gadget`: the unitary of SVT-8 (`HermitianEncoding.qsvtReal`) is
  `hadA * gadgetSeq E Φ * hadA`, a product of the primitives of CIRC-1
  (`QSVT.Circuit.Primitive` makes this a gate list with resource counts).
-/

namespace QSVT.Circuit

open QuantumState QSVT.Encoding QSVT.SVT

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The projector-controlled NOT -/

/-- CIRC-3 (GSLW Lemma 19). The projector-controlled NOT `C_Π NOT = X ⊗ Π + I ⊗ (I − Π)`:
it flips the ancilla on the range of `Π` (here `P`) and does nothing on its kernel. In the
direct-sum model this is the block operator `[[1 − P, P], [P, 1 − P]]`. -/
noncomputable def cpiNot (P : L ℋ) : L (Anc ℋ) := block (1 - P) P P (1 - P)

/-- `C_I NOT = X ⊗ I` is the plain `X` on the ancilla. -/
theorem cpiNot_one : cpiNot (1 : L ℋ) = block 0 1 1 0 := by
  rw [cpiNot, sub_self]

variable {P : L ℋ}

/-- CIRC-3. `C_Π NOT` is an involution. -/
theorem cpiNot_mul_cpiNot (hP : IsProjective P) : cpiNot P * cpiNot P = 1 := by
  rw [cpiNot, block_mul_block, hP.one_sub.mul_self, hP.mul_self, hP.one_sub_mul, hP.mul_one_sub,
    add_zero, sub_add_cancel, add_sub_cancel, block_one]

/-- CIRC-3. `C_Π NOT` is self-adjoint. -/
theorem cpiNot_adjoint (hP : IsProjective P) : (cpiNot P)† = cpiNot P := by
  rw [cpiNot, block_adjoint, hP.adjoint_eq, hP.one_sub.adjoint_eq]

/-- CIRC-3. `C_Π NOT` is unitary. -/
theorem cpiNot_mem_unitary (hP : IsProjective P) : cpiNot P ∈ unitary (L (Anc ℋ)) :=
  Unitary.mem_iff.mpr
    ⟨by rw [LinearMap.star_eq_adjoint, cpiNot_adjoint hP, cpiNot_mul_cpiNot hP],
      by rw [LinearMap.star_eq_adjoint, cpiNot_adjoint hP, cpiNot_mul_cpiNot hP]⟩

/-- The `(0,0)` block of `C_Π NOT` is `1 − P` (the ancilla stays in `|0⟩` exactly on the
kernel of `Π`). -/
@[simp] theorem topLeft_cpiNot : topLeft (cpiNot P) = 1 - P := topLeft_block _ _ _ _

/-! ### Lifting an operator to the ancilla system -/

/-- CIRC-3. The operator `I ⊗ U` on `Anc ℋ`: `U` acting on `ℋ` with the ancilla untouched. -/
noncomputable def liftU (U : L ℋ) : L (Anc ℋ) := blockDiag U U

theorem liftU_mul (U V : L ℋ) : liftU U * liftU V = liftU (U * V) := blockDiag_mul U U V V

theorem liftU_adjoint (U : L ℋ) : (liftU U)† = liftU (U†) := blockDiag_adjoint U U

@[simp] theorem liftU_one : liftU (1 : L ℋ) = 1 := blockDiag_one

@[simp] theorem topLeft_liftU (U : L ℋ) : topLeft (liftU U) = U := topLeft_blockDiag U U

/-- CIRC-3. `I ⊗ U` is unitary when `U` is. -/
theorem liftU_mem_unitary {U : L ℋ} (hU : U ∈ unitary (L ℋ)) :
    liftU U ∈ unitary (L (Anc ℋ)) :=
  blockDiag_mem_unitary hU hU

/-! ### The gadget of GSLW Fig. 1b -/

/-- CIRC-3 (GSLW Lemma 19, Fig. 1b). The three-gate gadget
`C_Π NOT · (e^{−iφ Z} ⊗ I) · C_Π NOT` on `Anc ℋ`. -/
noncomputable def gadget (P : L ℋ) (φ : ℝ) : L (Anc ℋ) :=
  cpiNot P * ancPhase (-φ) * cpiNot P

/-- CIRC-3 (GSLW Lemma 19, Fig. 1b). The gadget implements the phase operator controlled by
the ancilla: `gadget P φ = |0⟩⟨0| ⊗ e^{iφ(2Π−I)} + |1⟩⟨1| ⊗ e^{−iφ(2Π−I)}`. -/
theorem gadget_eq (hP : IsProjective P) (φ : ℝ) :
    gadget P φ = blockDiag (phaseOp P φ) (phaseOp P (-φ)) := by
  have e1 : Complex.I * ((-φ : ℝ) : ℂ) = -(Complex.I * φ) := by push_cast; ring
  rw [gadget, cpiNot, ancPhase, blockDiag, block_mul_block, block_mul_block]
  simp only [mul_zero, add_zero, zero_add, mul_smul_comm, mul_one, smul_mul_assoc, hP.mul_self,
    hP.one_sub.mul_self, hP.mul_one_sub, hP.one_sub_mul, smul_zero]
  rw [blockDiag, phaseOp, phaseOp, e1, neg_neg, add_comm (Complex.exp (-(Complex.I * φ)) • _)]

/-- CIRC-3. The `(0,0)` block of the gadget is `e^{iφ(2Π−I)}`: with the ancilla in `|0⟩`
the gadget acts as `phaseOp P φ` (the statement `phaseOp Π φ = C_Π NOT · Rz · C_Π NOT` of the
specification). -/
theorem topLeft_gadget (hP : IsProjective P) (φ : ℝ) : topLeft (gadget P φ) = phaseOp P φ := by
  rw [gadget_eq hP, topLeft_blockDiag]

/-- CIRC-3. The gadget is unitary. -/
theorem gadget_mem_unitary (hP : IsProjective P) (φ : ℝ) :
    gadget P φ ∈ unitary (L (Anc ℋ)) :=
  mul_mem (mul_mem (cpiNot_mem_unitary hP) (ancPhase_mem_unitary (-φ))) (cpiNot_mem_unitary hP)

/-! ### The alternating sequence through the gadgets -/

/-- CIRC-3. The alternating phase sequence `U_Φ` of SVT-1 realized on `Anc ℋ`: each phase
operator is replaced by its gadget and the oracle `U` (resp. `U†`) by `I ⊗ U` (resp. `I ⊗ U†`).
The recursion mirrors `altSeq`: `gadgetSeq E (φ :: Φ) = (gadget Π̃ φ · (I ⊗ U) or
gadget Π φ · (I ⊗ U†)) * gadgetSeq E Φ`, the first alternative when `Φ` has even length. -/
noncomputable def gadgetSeq (E : ProjUnitaryEncoding ℋ) : List ℝ → L (Anc ℋ)
  | [] => 1
  | φ :: Φ =>
    (if Even Φ.length then gadget E.P' φ * liftU E.U else gadget E.P φ * liftU (E.U†)) *
      gadgetSeq E Φ

variable (E : ProjUnitaryEncoding ℋ)

@[simp] theorem gadgetSeq_nil : gadgetSeq E [] = 1 := rfl

@[simp] theorem gadgetSeq_cons (φ : ℝ) (Φ : List ℝ) :
    gadgetSeq E (φ :: Φ) =
      (if Even Φ.length then gadget E.P' φ * liftU E.U else gadget E.P φ * liftU (E.U†)) *
        gadgetSeq E Φ := rfl

/-- CIRC-3 (GSLW Lemma 19 + Cor 18). Driving the alternating sequence through the gadgets
runs `U_Φ` on the ancilla-`|0⟩` branch and `U_{−Φ}` on the ancilla-`|1⟩` branch:
`gadgetSeq E Φ = |0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ}`. -/
theorem gadgetSeq_eq (Φ : List ℝ) :
    gadgetSeq E Φ = blockDiag (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) := by
  induction Φ with
  | nil => rw [gadgetSeq_nil, List.map_nil, altSeq_nil, blockDiag_one]
  | cons φ Φ ih =>
    rw [gadgetSeq_cons, ih, List.map_cons, altSeq_cons, altSeq_cons, List.length_map]
    split_ifs
    · rw [gadget_eq E.hP', liftU, blockDiag_mul, blockDiag_mul]
    · rw [gadget_eq E.hP, liftU, blockDiag_mul, blockDiag_mul]

/-- CIRC-3. The `(0,0)` block of `gadgetSeq E Φ` is `U_Φ`. -/
theorem topLeft_gadgetSeq (Φ : List ℝ) : topLeft (gadgetSeq E Φ) = altSeq E Φ := by
  rw [gadgetSeq_eq, topLeft_blockDiag]

/-- CIRC-3. `gadgetSeq E Φ` is unitary. -/
theorem gadgetSeq_mem_unitary (Φ : List ℝ) : gadgetSeq E Φ ∈ unitary (L (Anc ℋ)) := by
  rw [gadgetSeq_eq]
  exact blockDiag_mem_unitary (altSeq_mem_unitary E Φ) (altSeq_mem_unitary E _)

/-- CIRC-3 (GSLW Cor 18 as a circuit). The unitary of the real-polynomial QSVT encoding
`E.qsvtReal Φ` (SVT-8) is the Hadamard-conjugated gadget sequence
`(H ⊗ I) · gadgetSeq E Φ · (H ⊗ I)`, i.e. a product of the primitives of CIRC-1. -/
theorem qsvtReal_U_eq_gadget (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    (E.qsvtReal Φ).U = hadA * gadgetSeq E.toProjUnitaryEncoding Φ * hadA := by
  rw [qsvtReal_U, lcu2, gadgetSeq_eq]

end QSVT.Circuit
