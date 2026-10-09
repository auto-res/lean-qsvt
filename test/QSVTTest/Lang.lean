/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.Info

/-!
# QSVTTest.Lang

Regression tests for the language layer (LANG-1, `QSVT.Lang.*`): the surface syntax, the
computable costs on the two reference programs (`qsvt[sign21Phases] U₀` of APP-1 Route B and
`poly[[0, -3, 0, 4]] U₀` of the IR demo), the translation to the IR, the `#qsvt_info` reports
(stable text, including the OpenQASM output) and the axiom audit. Each check is a compile-time
assertion.
-/

-- `#guard` / `#print axioms` / `#qsvt_info` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.IR QSVT.Lang QSVT.Certificate
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Costs of the reference programs -/

#guard queriesQ (qsvt[sign21Phases] U₀) = 21
#guard ancillaDimQ (qsvt[sign21Phases] U₀) = 2
#guard degreeBoundQ (qsvt[sign21Phases] U₀) = 21
#guard scaleQ (qsvt[sign21Phases] U₀) = 1
#guard wellScaledQ (qsvt[sign21Phases] U₀) = true

-- `4x³ − 3x = T₃`: Chebyshev coefficients `[0, 0, 0, 1]`, `0 + 1 + 2 + 3 = 6` queries
#guard chebOfMonomials [0, -3, 0, 4] = [0, 0, 0, 1]
#guard queriesQ (poly[[0, -3, 0, 4]] U₀) = 6
#guard ancillaDimQ (poly[[0, -3, 0, 4]] U₀) = 4
#guard degreeBoundQ (poly[[0, -3, 0, 4]] U₀) = 3
#guard scaleQ (poly[[0, -3, 0, 4]] U₀) = 1
#guard wellScaledQ (poly[[0, -3, 0, 4]] U₀) = true

-- the same step by Chebyshev coefficients
#guard queriesQ (cheb[[0, 0, 0, 1]] U₀) = 6
#guard scaleQ (cheb[[0, -3, 0, 4]] U₀) = 7

-- costs multiply along the program
#guard queriesQ (qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀) = 12
#guard ancillaDimQ (qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀) = 8
#guard degreeBoundQ (qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀) = 6

-- degenerate Chebyshev-LCU steps are not well scaled
#guard wellScaledQ (cheb[[]] U₀) = false
#guard wellScaledQ (poly[[0, 0]] U₀) = false
#guard wellScaledQ (qsvt[[1]] cheb[[0]] U₀) = false

-- printing
#guard toString (qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀) =
  "qsvt[[1/2, -1/3]] poly[[0, -3, 0, 4]] U₀"

/-! ### Translation to the IR -/

/-- `qsvt[sign21Phases] U₀` translates to the Route B program `signBExpr` of APP-1. -/
example : toExpr (qsvt[sign21Phases] U₀) = .qsvtReal (sign21Phases.map (↑)) .oracle := rfl

/-- `poly[[0, -3, 0, 4]] U₀` translates to the IR demo program `chebLCU 0 [0, 0, 1] oracle`. -/
example : toExpr (poly[[0, -3, 0, 4]] U₀) = .chebLCU 0 [0, 0, 1] .oracle := by
  rw [toExpr_poly, chebNode, show chebOfMonomials [0, -3, 0, 4] = [0, 0, 0, 1] by decide +kernel]
  rfl

/-- The empty Chebyshev list translates to the zero polynomial node. -/
example : toExpr (cheb[[]] U₀) = .chebLCU 0 [] .oracle := rfl

/-- The cost theorems instantiated: the IR query count of the Route B program is `21`. -/
example : queries (toExpr (qsvt[sign21Phases] U₀)) = 21 := by
  rw [queriesQ_eq]; decide

example : ancillaDim (toExpr (poly[[0, -3, 0, 4]] U₀)) = 4 := by
  rw [ancillaDimQ_eq]; decide +kernel

example : scale (toExpr (cheb[[0, -3, 0, 4]] U₀)) = 7 := by
  rw [scaleQ_eq]; norm_num [scaleQ, l1Q]

example : WellScaled (toExpr (poly[[0, -3, 0, 4]] U₀)) :=
  (wellScaled_toExpr_iff _).mpr (by decide +kernel)

/-- The degree bound instantiated: `deg (spec (poly[[0, -3, 0, 4]] U₀)) ≤ 3`. -/
example : (spec (toExpr (poly[[0, -3, 0, 4]] U₀))).natDegree ≤ 3 :=
  (natDegree_spec_toExpr_le _).trans_eq (by decide +kernel)

/-! ### The correctness theorem instantiated -/

/-- `baseQ_eq` on the demo program: the base block is `‖c‖₁⁻¹ • (T₃)(A₀) Π` with `‖c‖₁ = 1`. -/
example (E₀ : HermitianEncoding ℋ) :
    compress (toExpr (poly[[0, -3, 0, 4]] U₀)) (denoteQ E₀ (poly[[0, -3, 0, 4]] U₀)).encoded =
      ((scaleQ (poly[[0, -3, 0, 4]] U₀) : ℝ) : ℂ)⁻¹ •
        (aeval E₀.encoded (spec (toExpr (poly[[0, -3, 0, 4]] U₀))) * E₀.P) :=
  baseQ_eq E₀ (by decide +kernel)

/-- `baseQ_eq` on the Route B program: no subnormalisation (`scaleQ = 1`). -/
example (E₀ : HermitianEncoding ℋ) :
    compress (toExpr (qsvt[sign21Phases] U₀)) (denoteQ E₀ (qsvt[sign21Phases] U₀)).encoded =
      aeval E₀.encoded (spec (toExpr (qsvt[sign21Phases] U₀))) * E₀.P := by
  rw [baseQ_eq E₀ (e := qsvt[sign21Phases] U₀) rfl]
  simp [scaleQ]

/-! ### Reports -/

#guard (qasmOf (poly[[0, -3, 0, 4]] U₀)).isNone
#guard (qasmOf (qsvt[[1 / 2]] U₀)).isSome
#guard gateCounts [1 / 2, -1 / 3] = ⟨10, 2, 4, 2, 2⟩

/--
info: program      : qsvt[[1/2, -1/3]] U₀
  qsvt       : |Φ| = 2, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact
queries      : 2
ancilla      : dimension 2 (1 qubit)
degree bound : 2
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
gates        : 10 = 4·|Φ| + 2  [oracle U/U†: 2, C_Π NOT: 4, phase: 2, H: 2]  (GSLW Lemma 19)
OpenQASM 3   : 1 qubit + ancilla q[0], Π: q[1]=0  (untrusted output)
OPENQASM 3.0;
include "stdgates.inc";
// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.
// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.
// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ.
gate U_oracle q1 { }
qubit[2] q;
h q[0];
U_oracle q[1];
negctrl(1) @ x q[1], q[0];
rz(-0.666666666666667) q[0];
negctrl(1) @ x q[1], q[0];
inv @ U_oracle q[1];
negctrl(1) @ x q[1], q[0];
rz(1.000000000000000) q[0];
negctrl(1) @ x q[1], q[0];
h q[0];
-/
#guard_msgs in
#qsvt_info qsvt[[1 / 2, -1 / 3]] U₀

/--
info: program      : poly[[0, -3, 0, 4]] U₀
  poly       : monomial [0, -3, 0, 4] = Chebyshev [0, 0, 0, 1], ℓ¹ = 1, register of dimension 4
queries      : 6
ancilla      : dimension 4 (2 qubits)
degree bound : 3
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
circuit      : (gate-level compilation is reported for single-step programs qsvt[Φ] U₀ only)
-/
#guard_msgs in
#qsvt_info poly[[0, -3, 0, 4]] U₀

/--
info: program      : qsvt[[1/4]] U₀
  qsvt       : |Φ| = 1, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact
queries      : 1
ancilla      : dimension 2 (1 qubit)
degree bound : 1
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
gates        : 6 = 4·|Φ| + 2  [oracle U/U†: 1, C_Π NOT: 2, phase: 1, H: 2]  (GSLW Lemma 19)
OpenQASM 3   : 2 qubits + ancilla q[0], Π: q[2]=1  (untrusted output)
OPENQASM 3.0;
include "stdgates.inc";
// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.
// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.
// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ.
gate U_oracle q1, q2 { }
qubit[3] q;
h q[0];
U_oracle q[1], q[2];
ctrl(1) @ x q[2], q[0];
rz(0.500000000000000) q[0];
ctrl(1) @ x q[2], q[0];
h q[0];
-/
#guard_msgs in
#qsvt_info (n := 2) (cP := [(1, true)]) qsvt[[1 / 4]] U₀

-- a two-step program: 1 program line + 2 step lines + 5 cost lines + 1 circuit line
#guard (infoLines (qsvt[[1 / 2]] cheb[[0, -3, 0, 4]] U₀) 1 (zeroPattern 1)).length = 9

-- out-of-range control qubits are rejected
/-- error: #qsvt_info: a control qubit index in `cP` is not below n = 1 -/
#guard_msgs in
#qsvt_info (cP := [(1, true)]) qsvt[[1 / 4]] U₀

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Lang.queriesQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.queriesQ_eq

/-- info: 'QSVT.Lang.baseQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.baseQ_eq

/-- info: 'QSVT.Lang.scaleQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.scaleQ_eq

/-- info: 'QSVT.Lang.wellScaled_toExpr_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.wellScaled_toExpr_iff

/-- info: 'QSVT.Lang.natDegree_spec_toExpr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.natDegree_spec_toExpr_le
