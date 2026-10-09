/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.RegBridge

/-!
# QSVTTest.RegBridge

Regression tests for the register/qubit bridge (CIRC-1, CIRC-5, `QSVT.Qubit.RegBridge`): the
little-endian indexing `bitsToFin`, the placement of the ancilla bits first, the transport of
`selectOp`/`matOp`/`reg0`/`lcu` to multi-qubit gates, and axiom audits of the main lemmas. Each
check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.Qubit
open scoped Matrix

/-! ### Bit-string indexing (little-endian: bit `i` has weight `2^i`) -/

example : bitsToFin 2 ![false, false] = 0 := by decide

example : bitsToFin 2 ![true, false] = 1 := by decide

example : bitsToFin 2 ![false, true] = 2 := by decide

example : bitsToFin 2 ![true, true] = 3 := by decide

example : bitsToFin 1 ![true] = 1 := by decide

/-- The ancilla bits come first. -/
example : joinBits ![true] ![false] = ![true, false] := by
  funext i
  fin_cases i <;> rfl

example : ancBits (n := 1) ![true, false] = ![true] := by
  funext i
  fin_cases i
  rfl

example : sysBits (k := 1) ![true, false] = ![false] := by
  funext i
  fin_cases i
  rfl

/-! ### The isometry on basis vectors (`k = 1`, `n = 1`) -/

/-- `inj 1 |0⟩ ↦ |1 0⟩`: the ancilla bit is the leading bit. -/
example : regEquiv 1 1 (inj (bitsToFin 1 ![true]) (ket ![false])) = ket ![true, false] := by
  rw [regEquiv_inj_ket, Equiv.symm_apply_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `inj 0 |1⟩ ↦ |0 1⟩`. -/
example : regEquiv 1 1 (inj 0 (ket ![true])) = ket ![false, true] := by
  rw [regEquiv_inj_ket, ← bitsToFin_false, Equiv.symm_apply_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `regEquiv` preserves norms. -/
example (v : Reg (2 ^ 3) (Qubits 2)) : ‖regEquiv 2 3 v‖ = ‖v‖ := (regEquiv 2 3).norm_map v

/-! ### Transport of operators -/

/-- The ancilla projector keeps `|0 1⟩` ... -/
example :
    liftReg (reg0 : L (Reg (2 ^ 1) (Qubits 1))) (ket ![false, true]) = ket ![false, true] := by
  rw [liftReg_reg0, zeroProj, diagProj_ket]
  simp

/-- ... and kills `|1 1⟩`. -/
example : liftReg (reg0 : L (Reg (2 ^ 1) (Qubits 1))) (ket ![true, true]) = 0 := by
  rw [liftReg_reg0, zeroProj, diagProj_ket]
  simp

/-- `1 ⊗ T` on one ancilla qubit is the `tensorId` of the one-ancilla bridge. -/
example (T : L (Qubits 1)) : liftReg (selectOp fun _ : Fin (2 ^ 1) => T) = tensorId T := by
  rw [liftReg_selectOp_const, tensorIdK_one_eq_tensorId]

/-- The LCU circuit in the qubit model. -/
example (V : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) (W : Fin (2 ^ 1) → L (Qubits 1)) :
    liftReg (lcu V W) = ancGate Vᴴ * ctrlSelect W * ancGate V :=
  liftReg_lcu V W

/-- The multiplexed gate of unitaries is unitary (`k = 2`, `n = 3`). -/
example (W : Fin (2 ^ 2) → L (Qubits 3)) (hW : ∀ j, W j ∈ unitary (L (Qubits 3))) :
    ctrlSelect W ∈ unitary (L (Qubits (3 + 2))) :=
  ctrlSelect_mem_unitary hW

/-- A unitary two-qubit ancilla gate is unitary. -/
example (V : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ) :
    (ancGate V : L (Qubits (1 + 2))) ∈ unitary (L (Qubits (1 + 2))) :=
  ancGate_mem_unitary_of_mem_unitaryGroup hV

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Qubit.liftReg_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_mul

/-- info: 'QSVT.Qubit.liftReg_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_mem_unitary

/-- info: 'QSVT.Qubit.liftReg_selectOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_selectOp

/-- info: 'QSVT.Qubit.liftReg_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_matOp

/-- info: 'QSVT.Qubit.liftReg_reg0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_reg0

/-- info: 'QSVT.Qubit.liftReg_lcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_lcu

/-- info: 'QSVT.Qubit.liftReg_chebLCU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftReg_chebLCU
