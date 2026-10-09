/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Compile

/-!
# OpenQASM 3 emission for compiled QSVT circuits (formal-spec CIRC-6, untrusted output)

The qubit circuits of `QSVT.Qubit.Compile` carry real phases and control *predicates*, so they
cannot be printed. This module provides a printable mirror `QGateQ n` with rational phases and
explicit control lists, the compilation `compileQsvtRealQ` of a rational phase list into it
(mirroring `compileQsvtReal`, CIRC-3), the interpretation `QGateQ.toQGate` back into the verified
gate type with the exactness theorem `map_toQGate_compileQsvtRealQ`, and the OpenQASM 3 printer
`toQasm`.

## Trust boundary

Everything up to and including `QGateQ.toQGate` is inside the verified part: by
`map_toQGate_compileQsvtRealQ` and `compileQ_qsvtReal` the gate list `compileQsvtRealQ Φ cP cP'`,
read through `toQGate`, denotes `liftAnc (E.qsvtReal Φ).U` (`denote_compileQsvtRealQ`). The
string produced by `toQasm` is **untrusted**: nothing is proved about it, and it is meant to be
checked against the gate list by an external tool (Qiskit, CIRC-6).

## Conventions of the emitted program

* Register `qubit[n+1] q;` with `q[0]` the QSVT ancilla and `q[1], …, q[n]` the system register
  (system qubit `i : Fin n` is `q[i+1]`).
* Statements are in time order: the gate list (product order, leftmost gate applied last) is
  reversed on emission, so for `compileQsvtRealQ Φ` the first statements are `h q[0];` and the
  oracle call of the *last* phase of `Φ`.
* The oracle is the placeholder `gate U_oracle q1, …, qn { }` (an empty gate body is a legal
  OpenQASM 3 gate definition, acting as the identity); `oracle` is the call
  `U_oracle q[1], …, q[n];` and `oracleAdj` is `inv @ U_oracle q[1], …, q[n];`. The user replaces
  the body by the block-encoding circuit. (OpenQASM 3 has no `opaque` gates and `extern` only
  declares classical functions, hence the placeholder.)
* `QGate.rz φ` is `diag(e^{iφ}, e^{−iφ}) = e^{iφ Z}` (`QSVT.Qubit.rzMat`), while OpenQASM's
  `rz(θ) = diag(e^{−iθ/2}, e^{iθ/2})`; hence `rz φ` is emitted as `rz(-2φ) q[0];`.
* `ctrlX ctrls` with all control values `true` is `ctrl(k) @ x q[c₁+1], …, q[cₖ+1], q[0];`, with
  all values `false` it is `negctrl(k) @ x …;`; for mixed values the `false`-controlled qubits are
  wrapped in `x` gates around a `ctrl(k) @ x` (three lines). An empty control list is `x q[0];`.
* Phases are printed as decimals with `qasmDigits = 15` fractional digits (round half up, computed
  by integer arithmetic in `Rat.toDecimalString`); this rounding is the only lossy step.

## Contents

* `QGateQ n`, `pattern ctrls`, `QGateQ.toQGate`.
* `compileGadgetQ`, `compileAltSeqQ`, `compileQsvtRealQ`, with `map_toQGate_compileAltSeqQ`,
  `map_toQGate_compileQsvtRealQ`, `denote_compileQsvtRealQ`, `length_compileQsvtRealQ`.
* `Rat.toDecimalString`, `qasmHeaderLines`, `QGateQ.toQasmLines`, `toQasmLines`, `toQasm`.
-/

namespace QSVT.Qubit

open QuantumState QSVT.Encoding QSVT.Circuit

variable {n : ℕ}

/-! ### Printable gates -/

/-- CIRC-6. Printable qubit gates: rational phases and explicit control lists `(qubit, value)` on
the system register (`Fin n`); the ancilla is qubit `0` of the emitted program and system qubit
`i` is `q[i+1]`. -/
inductive QGateQ (n : ℕ)
  /-- The oracle `1 ⊗ U`. -/
  | oracle
  /-- The inverse oracle `1 ⊗ U†`. -/
  | oracleAdj
  /-- The multi-controlled `X` on the ancilla with the given controls. -/
  | ctrlX (ctrls : List (Fin n × Bool))
  /-- The phase `e^{iφ Z}` on the ancilla. -/
  | rz (φ : ℚ)
  /-- The Hadamard on the ancilla. -/
  | h
  deriving Repr, DecidableEq

/-- CIRC-6. The control predicate of a control list: `b` satisfies every `(i, x) ∈ ctrls`,
i.e. `b i = x`. -/
def pattern (ctrls : List (Fin n × Bool)) (b : Fin n → Bool) : Bool :=
  decide (∀ p ∈ ctrls, b p.1 = p.2)

/-- CIRC-6. The verified gate of a printable gate. -/
noncomputable def QGateQ.toQGate : QGateQ n → QGate n
  | .oracle => .oracle
  | .oracleAdj => .oracleAdj
  | .ctrlX ctrls => .ctrlX (pattern ctrls)
  | .rz φ => .rz (φ : ℝ)
  | .h => .h

/-! ### Compilation of rational phases -/

/-- CIRC-6. The printable gadget `ctrlX, rz(−φ), ctrlX` with controls `cP'` (`useP' = true`) or
`cP` (`useP' = false`), mirroring `compileGadget`. -/
def compileGadgetQ (cP cP' : List (Fin n × Bool)) (useP' : Bool) (φ : ℚ) : List (QGateQ n) :=
  [.ctrlX (if useP' then cP' else cP), .rz (-φ), .ctrlX (if useP' then cP' else cP)]

/-- CIRC-6. The printable alternating sequence, mirroring `compileAltSeq`. -/
def compileAltSeqQ (cP cP' : List (Fin n × Bool)) : List ℚ → List (QGateQ n)
  | [] => []
  | φ :: Φ =>
    (if Even Φ.length then compileGadgetQ cP cP' true φ ++ [.oracle]
      else compileGadgetQ cP cP' false φ ++ [.oracleAdj]) ++ compileAltSeqQ cP cP' Φ

/-- CIRC-6. The printable Route B circuit `h, compileAltSeqQ, h`, mirroring `compileQsvtReal`. -/
def compileQsvtRealQ (Φ : List ℚ) (cP cP' : List (Fin n × Bool)) : List (QGateQ n) :=
  [.h] ++ compileAltSeqQ cP cP' Φ ++ [.h]

section exact

variable (Q : QubitEncoding n) (cP cP' : List (Fin n × Bool))

theorem map_toQGate_compileGadgetQ (hd : Q.d = pattern cP) (hd' : Q.d' = pattern cP') (b : Bool)
    (φ : ℚ) :
    (compileGadgetQ cP cP' b φ).map QGateQ.toQGate = compileQ Q (compileGadget b (φ : ℝ)) := by
  cases b <;> simp [compileGadgetQ, compileGadget, compileQ, compilePrim, QGateQ.toQGate, hd, hd']

theorem map_toQGate_compileAltSeqQ (hd : Q.d = pattern cP) (hd' : Q.d' = pattern cP')
    (Φ : List ℚ) :
    (compileAltSeqQ cP cP' Φ).map QGateQ.toQGate = compileQ Q (compileAltSeq (Φ.map (↑))) := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeqQ, List.map_cons, compileAltSeq_cons, List.length_map, compileQ_append,
      List.map_append, ih]
    split_ifs <;>
      rw [List.map_append, compileQ_append, map_toQGate_compileGadgetQ Q cP cP' hd hd'] <;> rfl

/-- CIRC-6 (exactness of the printable circuit). Read through `toQGate`, the printable Route B
circuit for the rational phases `Φ` is the compiled verified circuit for the real phases `Φ`,
for any encoding whose control predicates are `pattern cP`, `pattern cP'`. -/
theorem map_toQGate_compileQsvtRealQ (hd : Q.d = pattern cP) (hd' : Q.d' = pattern cP')
    (Φ : List ℚ) :
    (compileQsvtRealQ Φ cP cP').map QGateQ.toQGate = compileQ Q (compileQsvtReal (Φ.map (↑))) := by
  rw [compileQsvtRealQ, compileQsvtReal, List.map_append, List.map_append, compileQ_append,
    compileQ_append, map_toQGate_compileAltSeqQ Q cP cP' hd hd']
  rfl

/-- CIRC-6 / CIRC-4. The printable Route B circuit denotes `liftAnc (E.qsvtReal Φ).U` for a
Hermitian qubit encoding with control predicate `pattern cP`. -/
theorem denote_compileQsvtRealQ (Q : QubitHermitianEncoding n) (cP : List (Fin n × Bool))
    (hd : Q.d = pattern cP) (Φ : List ℚ) :
    QCircuit.denote Q.toQubit ((compileQsvtRealQ Φ cP cP).map QGateQ.toQGate) =
      liftAnc (Q.toHermitian.qsvtReal (Φ.map (↑))).U := by
  rw [map_toQGate_compileQsvtRealQ Q.toQubit cP cP hd hd, compileQ_qsvtReal]

/-- CIRC-6 / IR-2. The printable Route B circuit has `4 * Φ.length + 2` gates. -/
theorem length_compileQsvtRealQ (Φ : List ℚ) :
    (compileQsvtRealQ Φ cP cP').length = 4 * Φ.length + 2 := by
  have h := congrArg List.length (map_toQGate_compileQsvtRealQ ⟨1, one_mem _, pattern cP,
    pattern cP'⟩ cP cP' rfl rfl Φ)
  rwa [List.length_map, length_compileQ, length_compileQsvtReal, List.length_map] at h

end exact

/-! ### Decimal printing of rationals -/

/-- CIRC-6. `Rat.toDecimalString q k` prints `q` as a decimal with exactly `k` fractional digits,
rounded half away from zero, using integer arithmetic only: `round(|q| · 10^k)` split into integer
and fractional part, with the fractional part zero-padded to `k` digits. -/
def _root_.Rat.toDecimalString (q : ℚ) (digits : ℕ) : String :=
  let scale : ℕ := 10 ^ digits
  let r : ℕ := (q.num.natAbs * scale + q.den / 2) / q.den
  let intPart := toString (r / scale)
  let frac := toString (r % scale)
  let fracPadded := String.ofList (List.replicate (digits - frac.length) '0') ++ frac
  let sign := if q.num < 0 then "-" else ""
  if digits = 0 then sign ++ intPart else sign ++ intPart ++ "." ++ fracPadded

/-- CIRC-6. Number of fractional digits of printed phases (about double precision). -/
def qasmDigits : ℕ := 15

/-! ### OpenQASM 3 emission -/

/-- CIRC-6. `q[i+1]`, the program qubit of system qubit `i`. -/
def sysQubit (i : Fin n) : String := s!"q[{i.val + 1}]"

/-- CIRC-6. `q[1], …, q[n]`, the system register as an argument list. -/
def sysArgs (n : ℕ) : String :=
  ", ".intercalate ((List.finRange n).map sysQubit)

/-- CIRC-6. The header: version, standard gates, the oracle placeholder and the register. -/
def qasmHeaderLines (n : ℕ) : List String :=
  ["OPENQASM 3.0;",
   "include \"stdgates.inc\";",
   "// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.",
   "// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.",
   "// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ."]
  ++ (if n = 0 then [] else
      [s!"gate U_oracle {", ".intercalate ((List.finRange n).map fun i => s!"q{i.val + 1}")} \{ }"])
  ++ [s!"qubit[{n + 1}] q;"]

namespace QGateQ

/-- CIRC-6. The OpenQASM 3 line(s) of a printable gate. -/
def toQasmLines (n : ℕ) : QGateQ n → List String
  | .oracle => if n = 0 then ["// U_oracle (no system qubits)"] else [s!"U_oracle {sysArgs n};"]
  | .oracleAdj =>
    if n = 0 then ["// inv @ U_oracle (no system qubits)"] else [s!"inv @ U_oracle {sysArgs n};"]
  | .h => ["h q[0];"]
  | .rz φ => [s!"rz({Rat.toDecimalString (-2 * φ) qasmDigits}) q[0];"]
  | .ctrlX ctrls =>
    let k := ctrls.length
    let args := ", ".intercalate (ctrls.map fun p => sysQubit p.1) ++ ", q[0]"
    let negs := (ctrls.filter fun p => !p.2).map fun p => s!"x {sysQubit p.1};"
    if k = 0 then ["x q[0];"]
    else if ctrls.all (·.2) then [s!"ctrl({k}) @ x {args};"]
    else if ctrls.all (!·.2) then [s!"negctrl({k}) @ x {args};"]
    else negs ++ [s!"ctrl({k}) @ x {args};"] ++ negs

end QGateQ

/-- CIRC-6. The lines of the OpenQASM 3 program of a printable gate list on `n + 1` qubits. The
gate list is in *product* order (`QCircuit.denote`: leftmost gate = leftmost factor = the gate
applied last), while an OpenQASM program applies its statements in time order, so the list is
reversed on emission: the last gate of the list is the first statement. -/
def toQasmLines (n : ℕ) (gates : List (QGateQ n)) : List String :=
  qasmHeaderLines n ++ gates.reverse.flatMap (QGateQ.toQasmLines n)

/-- CIRC-6 (untrusted). The OpenQASM 3 program of a printable gate list on `n + 1` qubits, one
statement per line, terminated by a newline. -/
def toQasm (n : ℕ) (gates : List (QGateQ n)) : String :=
  "\n".intercalate (toQasmLines n gates) ++ "\n"

end QSVT.Qubit
