/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Compile
import QSVT.Qubit.Qasm
import QSVT.Certificate.Sign21Phases

/-!
# QSVTTest.QubitCompile

Regression tests for the qubit-level compilation (CIRC-4, `QSVT.Qubit.Compile`) and the OpenQASM 3
emitter (CIRC-6, `QSVT.Qubit.Qasm`): axiom audits of the correctness theorems, the compiled gate
list of small circuits, the decimal printer, and the emitted programs of a two-qubit toy and of the
Route B sign example (`sign21Phases`, 86 gates). Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` / `#eval` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.Circuit QSVT.Qubit QSVT.Certificate

/-! ### Compilation (CIRC-4) -/

/-- The gate-by-gate translation on a small circuit. -/
example (Q : QubitEncoding 2) :
    compileQ Q [Prim.hadA, Prim.cpiNotP, Prim.ancPhase 1, Prim.cpiNotP', Prim.oracle,
      Prim.oracleAdj] =
      [QGate.h, QGate.ctrlX Q.d, QGate.rz 1, QGate.ctrlX Q.d', QGate.oracle, QGate.oracleAdj] :=
  rfl

/-- The Route B circuit of one phase on qubits: `h, ctrlX d, rz(−φ), ctrlX d, oracle, h`. -/
example (Q : QubitHermitianEncoding 2) (φ : ℝ) :
    compileQ Q.toQubit (compileQsvtReal [φ]) =
      [QGate.h, QGate.ctrlX Q.d, QGate.rz (-φ), QGate.ctrlX Q.d, QGate.oracle, QGate.h] := by
  simp [compileQsvtReal, compileAltSeq, compileGadget, compileQ, compilePrim]

/-- The compiled gadget denotes `ctrlX d * rz 0 (−φ) * ctrlX d` (CIRC-5 `liftAnc_gadget_diagProj`
through `liftAnc_denote`). -/
example (Q : QubitEncoding 2) (φ : ℝ) :
    QCircuit.denote Q (compileQ Q (compileGadget false φ)) = ctrlX Q.d * rz 0 (-φ) * ctrlX Q.d := by
  rw [← liftAnc_denote, denote_compileGadget_false, QubitEncoding.toProj_P, liftAnc_gadget_diagProj]

/-- Gate counts transport: `4 · 21 + 2 = 86` gates and `21` oracle calls for the sign example. -/
example (Q : QubitHermitianEncoding 3) :
    (compileQ Q.toQubit (compileQsvtReal (sign21Phases.map (↑)))).length = 86 := by
  rw [length_compileQ_qsvtReal, List.length_map, sign21Phases_length]

example (Q : QubitHermitianEncoding 3) :
    QCircuit.oracleCount (compileQ Q.toQubit (compileQsvtReal (sign21Phases.map (↑)))) = 21 := by
  rw [oracleCount_compileQ_qsvtReal, List.length_map, sign21Phases_length]

/-- `zeroProj 2` on three qubits is the diagonal projector of the two-anti-control pattern. -/
example : (zeroProj 2 : L (Qubits 3)) = diagProj (zeroPattern 2) := zeroProj_eq_diagProj 2

/-! ### Printable gates (CIRC-6) -/

/-- The control pattern of `[(0, false), (1, false)]` on `Fin 3` is `zeroPattern 2`. -/
example : pattern [((0 : Fin 3), false), ((1 : Fin 3), false)] = zeroPattern 2 := by
  funext b
  simp only [pattern, zeroPattern, List.forall_mem_cons, Fin.forall_fin_succ]
  decide +revert

/-- The all-`false` control pattern on the first two of three system qubits (`zeroPattern 2`). -/
def signCtrls : List (Fin 3 × Bool) := [((0 : Fin 3), false), ((1 : Fin 3), false)]

/-- The lines of the emitted program of the Route B sign circuit on a three-qubit system. -/
def signQasmLines : List String := toQasmLines 3 (compileQsvtRealQ sign21Phases signCtrls signCtrls)

-- The printable Route B circuit has `4 · 21 + 2 = 86` gates.
#guard (compileQsvtRealQ sign21Phases signCtrls signCtrls).length = 86

-- The decimal printer: rounding half away from zero, zero padding, sign.
#guard Rat.toDecimalString (1 / 3 : ℚ) 15 = "0.333333333333333"
#guard Rat.toDecimalString (-2 / 3 : ℚ) 15 = "-0.666666666666667"
#guard Rat.toDecimalString (5 : ℚ) 15 = "5.000000000000000"
#guard Rat.toDecimalString (-1 / 1000000 : ℚ) 15 = "-0.000001000000000"
#guard Rat.toDecimalString (2 / 3 : ℚ) 0 = "1"
#guard Rat.toDecimalString (-5 / 2 : ℚ) 1 = "-2.5"

-- Mixed control values: the `false`-controlled qubit is wrapped in `x` gates.
#guard QGateQ.toQasmLines 2 (QGateQ.ctrlX [((0 : Fin 2), true), ((1 : Fin 2), false)]) =
  ["x q[2];", "ctrl(2) @ x q[1], q[2], q[0];", "x q[2];"]

-- All-`true` controls use `ctrl`, the empty control list is a plain `x`.
#guard QGateQ.toQasmLines 2 (QGateQ.ctrlX [((1 : Fin 2), true)]) = ["ctrl(1) @ x q[2], q[0];"]
#guard QGateQ.toQasmLines 2 (QGateQ.ctrlX ([] : List (Fin 2 × Bool))) = ["x q[0];"]

-- `rz φ = e^{iφ Z}` is OpenQASM's `rz(−2φ)`.
#guard QGateQ.toQasmLines 2 (QGateQ.rz (1 / 4)) = ["rz(-0.500000000000000) q[0];"]

-- A two-system-qubit toy with one anti-control: phases `1/2, −1/3`. Statements are in time order
-- (`toQasmLines` reverses the product-ordered gate list): the oracle of the last phase comes first.
/--
info: OPENQASM 3.0;
include "stdgates.inc";
// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.
// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.
// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ.
gate U_oracle q1, q2 { }
qubit[3] q;
h q[0];
U_oracle q[1], q[2];
negctrl(1) @ x q[1], q[0];
rz(-0.666666666666667) q[0];
negctrl(1) @ x q[1], q[0];
inv @ U_oracle q[1], q[2];
negctrl(1) @ x q[1], q[0];
rz(1.000000000000000) q[0];
negctrl(1) @ x q[1], q[0];
h q[0];
-/
#guard_msgs in
#eval IO.println (toQasm 2 (compileQsvtRealQ [1 / 2, -1 / 3] [((0 : Fin 2), false)]
  [((0 : Fin 2), false)]))

/-! ### The Route B sign example on a three-qubit system (APP-1, `sign21Phases`) -/

-- The emitted program of the degree-21 sign circuit: `7` header lines and `86` gate lines
-- (`d = d'` the all-`false` pattern on the first two system qubits, `negctrl(2)`).
#guard signQasmLines.length = 7 + 86

-- The first `12` lines of the sign-example program (`rz(−2·(−φ₂₁))`, `φ₂₁ ≈ −1.547` the last
-- phase).
/--
info: OPENQASM 3.0;
include "stdgates.inc";
// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.
// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.
// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ.
gate U_oracle q1, q2, q3 { }
qubit[4] q;
h q[0];
U_oracle q[1], q[2], q[3];
negctrl(2) @ x q[1], q[2], q[0];
rz(-3.094003251621069) q[0];
negctrl(2) @ x q[1], q[2], q[0];
-/
#guard_msgs in
#eval IO.println ("\n".intercalate (signQasmLines.take 12))

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Qubit.liftAnc_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.liftAnc_denote

/-- info: 'QSVT.Qubit.compileQ_qsvtReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.compileQ_qsvtReal

/-- info: 'QSVT.Qubit.map_toQGate_compileQsvtRealQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.map_toQGate_compileQsvtRealQ

/-- info: 'QSVT.Qubit.denote_compileQsvtRealQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.denote_compileQsvtRealQ

/-- info: 'QSVT.Qubit.QCircuit.denote_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Qubit.QCircuit.denote_mem_unitary
