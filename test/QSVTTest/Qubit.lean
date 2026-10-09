/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Space
import QSVT.Qubit.Gates
import QSVT.Qubit.Bridge

/-!
# QSVTTest.Qubit

Regression tests for the qubit layer (CIRC-1, CIRC-5): the dimension of `Qubits n`, the action
of the standard gates on computational basis vectors, the direct-sum/qubit bridge, and axiom
audits of the main bridge lemmas. Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.Circuit QSVT.Qubit

/-- Three qubits have dimension `8`. -/
example : Module.finrank ℂ (Qubits 3) = 8 := by rw [finrank_qubits]; norm_num

/-- `Qubits n` is a qudit. -/
noncomputable example (n : ℕ) : Qudit (Qubits n) := inferInstance

/-- `X |0⟩ = |1⟩` on one qubit. -/
example : pauliX 0 (ket ![false]) = ket ![true] := by
  rw [pauliX_ket]
  congr 1
  funext i
  fin_cases i
  rfl

/-- `X₁ |00⟩ = |01⟩` on two qubits (qubit `1` is the second bit). -/
example : pauliX 1 (ket ![false, false]) = ket ![false, true] := by
  rw [pauliX_ket]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `Z |1⟩ = −|1⟩`. -/
example : pauliZ 0 (ket ![true]) = -ket ![true] := by
  rw [pauliZ_ket]
  simp

/-- `Z |0⟩ = |0⟩`. -/
example : pauliZ 0 (ket ![false]) = ket ![false] := by
  rw [pauliZ_ket]
  simp

/-- `H² = 1` on two qubits. -/
example : hadamard 1 * hadamard 1 = (1 : L (Qubits 2)) := hadamard_mul_hadamard 1

/-- `Rz(φ) Rz(−φ) = 1`. -/
example (φ : ℝ) : rz 0 φ * rz 0 (-φ) = (1 : L (Qubits 2)) := by
  rw [rz_mul_rz, add_neg_cancel, rz_zero]

/-- `|0⟩ ⊗ |t⟩` is the bit string `0 t`. -/
example (t : Fin 2 → Bool) : ancEquiv 2 (inl (ket t)) = ket (Fin.cons false t) :=
  ancEquiv_inl_ket t

/-- CIRC-5 on a concrete state: `C_Π NOT` for `Π = |0⟩⟨0|` on register bit `0` flips the leading
qubit of `|1 0 1⟩`, giving `|0 0 1⟩`. -/
example : liftAnc (cpiNot (bitProj (0 : Fin 2) false)) (ket ![true, false, true]) =
    ket ![false, false, true] := by
  rw [liftAnc_cpiNot_bitProj, ctrlX_ket]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- CIRC-5 on a concrete state: the same gate leaves `|1 1 1⟩` alone. -/
example : liftAnc (cpiNot (bitProj (0 : Fin 2) false)) (ket ![true, true, true]) =
    ket ![true, true, true] := by
  rw [liftAnc_cpiNot_bitProj, ctrlX_ket]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The trivially controlled NOT is `X₀`. -/
example : ctrlX (fun _ : Fin 2 → Bool => true) = pauliX 0 := ctrlX_true

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Qubit.toOp_mem_unitary_of_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.toOp_mem_unitary_of_mem_unitaryGroup

/-- info: 'QSVT.Qubit.applyAt_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.applyAt_mem_unitary

/-- info: 'QSVT.Qubit.liftAnc_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_mul

/-- info: 'QSVT.Qubit.liftAnc_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_mem_unitary

/-- info: 'QSVT.Qubit.liftAnc_blockDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_blockDiag

/-- info: 'QSVT.Qubit.liftAnc_hadA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_hadA

/-- info: 'QSVT.Qubit.liftAnc_cpiNot_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_cpiNot_one

/-- info: 'QSVT.Qubit.liftAnc_cpiNot_diagProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_cpiNot_diagProj

/-- info: 'QSVT.Qubit.liftAnc_gadget_diagProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_gadget_diagProj

/-- info: 'QSVT.Qubit.bitProj_isProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.bitProj_isProjective
