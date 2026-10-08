/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.Notation
import QSVT.Qubit.Qasm
import Mathlib.Data.Nat.Log

/-!
# Automatic cost and circuit reports for surface programs (LANG-1)

The user-facing command of the language layer:
```
#qsvt_info qsvt[[1/2, -1/3]] U₀
#qsvt_info (n := 2) (cP := [(0, false), (1, true)]) qsvt[sign21Phases] U₀
```
evaluates the program (a closed term of type `ExprQ`) and prints

* the program in surface syntax and its steps (for `poly` steps, the Chebyshev coefficients
  computed by POLY-6),
* `queries` (`queriesQ`, equal to the IR count by `queriesQ_eq`), the ancilla dimension
  (`ancillaDimQ`, `ancillaDimQ_eq`) with the number of qubits `⌈log₂ d⌉`, the degree bound
  (`degreeBoundQ`, `natDegree_spec_toExpr_le`), the subnormalisation `scale` (`scaleQ`,
  `scaleQ_eq`) as a fraction and a decimal, and `wellScaledQ` (the hypothesis of `baseQ_eq`);
* for a single-step program `qsvt[Φ] U₀`, the gate counts of the compiled circuit
  `compileQsvtReal Φ` (GSLW Lemma 19: `4|Φ| + 2` gates, `|Φ|` oracle calls, `2|Φ|` `C_Π NOT`,
  `|Φ|` ancilla phases, `2` Hadamards; `gateCounts_gates`, …) and its OpenQASM 3 program
  (CIRC-6 `compileQsvtRealQ`/`toQasm`, untrusted output) for `n` system qubits (default `1`)
  and the control pattern `cP` of `Π` (default: all `n` qubits controlled on `0`, i.e.
  `Π = |0…0⟩⟨0…0|`; qubits are numbered `0, …, n-1` in `cP` and printed as `q[1], …, q[n]`).

The same text is available as a string by `info e` (`#eval info e`), and the OpenQASM program
alone by `qasmOf e n`. Everything here is untrusted printing; the theorems quoted in the report
live in `QSVT.Lang.ExprQ` and `QSVT.Circuit.Primitive`.
-/

namespace QSVT.Lang

open QSVT.Circuit QSVT.Qubit

/-! ### Printing programs -/

/-- LANG-1. A rational list as `[q₀, q₁, …]` with rationals printed as fractions. -/
def listStr (l : List ℚ) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"

/-- LANG-1. A surface program in surface syntax (`qsvt[Φ] e`, `cheb[c] e`, `poly[l] e`, `U₀`). -/
def ExprQ.render : ExprQ → String
  | .oracle => "U₀"
  | .qsvt Φ e => s!"qsvt[{listStr Φ}] {render e}"
  | .cheb c e => s!"cheb[{listStr c}] {render e}"
  | .poly l e => s!"poly[{listStr l}] {render e}"

instance : ToString ExprQ := ⟨ExprQ.render⟩

/-! ### Single-step programs and their circuits -/

/-- LANG-1. The phases of a single-step program `qsvt[Φ] U₀`, if the program has that form. -/
def singleQsvt? : ExprQ → Option (List ℚ)
  | .qsvt Φ .oracle => some Φ
  | _ => none

/-- LANG-1. Gate counts of the compiled circuit `compileQsvtReal Φ` (CIRC-3). -/
structure GateCounts where
  /-- Total number of primitive gates. -/
  gates : ℕ
  /-- Oracle calls `U` or `U†`. -/
  oracleCalls : ℕ
  /-- Controlled NOTs `C_Π NOT`. -/
  cpiNots : ℕ
  /-- Ancilla phases `e^{iφ Z}`. -/
  phases : ℕ
  /-- Ancilla Hadamards. -/
  hadamards : ℕ
  deriving Repr, DecidableEq

/-- LANG-1 (GSLW Lemma 19). The gate counts of `compileQsvtReal Φ`: `4|Φ| + 2` gates, `|Φ|`
oracle calls, `2|Φ|` controlled NOTs, `|Φ|` phases, `2` Hadamards (`gateCounts_gates`, …). -/
def gateCounts (Φ : List ℚ) : GateCounts :=
  ⟨4 * Φ.length + 2, Φ.length, 2 * Φ.length, Φ.length, 2⟩

theorem gateCounts_gates (Φ : List ℚ) :
    (gateCounts Φ).gates = (compileQsvtReal (Φ.map (↑))).length := by
  rw [length_compileQsvtReal, List.length_map]; rfl

theorem gateCounts_oracleCalls (Φ : List ℚ) :
    (gateCounts Φ).oracleCalls = oracleCount (compileQsvtReal (Φ.map (↑))) := by
  rw [oracleCount_compileQsvtReal, List.length_map]; rfl

theorem gateCounts_cpiNots (Φ : List ℚ) :
    (gateCounts Φ).cpiNots = cpiNotCount (compileQsvtReal (Φ.map (↑))) := by
  rw [cpiNotCount_compileQsvtReal, List.length_map]; rfl

theorem gateCounts_phases (Φ : List ℚ) :
    (gateCounts Φ).phases = phaseCount (compileQsvtReal (Φ.map (↑))) := by
  rw [phaseCount_compileQsvtReal, List.length_map]; rfl

theorem gateCounts_hadamards (Φ : List ℚ) :
    (gateCounts Φ).hadamards = hadCount (compileQsvtReal (Φ.map (↑))) := by
  rw [hadCount_compileQsvtReal]; rfl

/-- LANG-1. The default control pattern on `n` system qubits: every qubit controlled on `0`,
i.e. `Π = |0…0⟩⟨0…0|`. -/
def zeroPattern (n : ℕ) : List (Fin n × Bool) := (List.finRange n).map fun i => (i, false)

/-- LANG-1. A control pattern given with `ℕ` qubit indices, checked against `n`. -/
def patternOfNat (n : ℕ) (l : List (ℕ × Bool)) : Option (List (Fin n × Bool)) :=
  l.mapM fun p => if h : p.1 < n then some (⟨p.1, h⟩, p.2) else none

/-- LANG-1. The OpenQASM 3 program (CIRC-6, untrusted) of a single-step program `qsvt[Φ] U₀` on
`n` system qubits with the control pattern `cP` of `Π` (Hermitian case, `Π̃ = Π`); `none` for
other programs. -/
def qasmOfWith (e : ExprQ) (n : ℕ) (cP : List (Fin n × Bool)) : Option String :=
  (singleQsvt? e).map fun Φ => toQasm n (compileQsvtRealQ Φ cP cP)

/-- LANG-1. `qasmOfWith` with the default pattern `Π = |0…0⟩⟨0…0|` on `n` system qubits. -/
def qasmOf (e : ExprQ) (n : ℕ := 1) : Option String := qasmOfWith e n (zeroPattern n)

/-! ### The report -/

/-- LANG-1. One line per step of the program, outermost (applied last) first. -/
def stepLines : ExprQ → List String
  | .oracle => []
  | .qsvt Φ e =>
    s!"  qsvt       : |Φ| = {Φ.length}, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact" ::
      stepLines e
  | .cheb c e =>
    s!"  cheb       : Chebyshev coefficients {listStr c}, ℓ¹ = {l1Q c}, \
      register of dimension {chebDim c}" :: stepLines e
  | .poly l e =>
    let c := chebOfMonomials l
    s!"  poly       : monomial {listStr l} = Chebyshev {listStr c}, ℓ¹ = {l1Q c}, \
      register of dimension {chebDim c}" :: stepLines e

/-- LANG-1. `"1 qubit"` / `"k qubits"`. -/
def qubitsStr (k : ℕ) : String := if k = 1 then "1 qubit" else s!"{k} qubits"

/-- LANG-1. A control pattern as `q[i+1]=b, …`. -/
def patternStr {n : ℕ} (cP : List (Fin n × Bool)) : String :=
  if cP.isEmpty then "(none: Π = 1)"
  else ", ".intercalate (cP.map fun p => s!"{sysQubit p.1}={if p.2 then 1 else 0}")

/-- LANG-1. The lines of the report of `#qsvt_info` for `n` system qubits and the control
pattern `cP` (see the module docstring). -/
def infoLines (e : ExprQ) (n : ℕ) (cP : List (Fin n × Bool)) : List String :=
  let d := ancillaDimQ e
  let s := scaleQ e
  let base :=
    [s!"program      : {e}"] ++ stepLines e ++
    [s!"queries      : {queriesQ e}",
     s!"ancilla      : dimension {d} ({qubitsStr (Nat.clog 2 d)})",
     s!"degree bound : {degreeBoundQ e}",
     s!"scale (ℓ¹)   : {s} ≈ {Rat.toDecimalString s 6}",
     s!"well scaled  : {wellScaledQ e}"]
  match singleQsvt? e with
  | none =>
    base ++ ["circuit      : (gate-level compilation is reported for single-step programs \
      qsvt[Φ] U₀ only)"]
  | some Φ =>
    let g := gateCounts Φ
    base ++
      [s!"gates        : {g.gates} = 4·|Φ| + 2  [oracle U/U†: {g.oracleCalls}, \
        C_Π NOT: {g.cpiNots}, phase: {g.phases}, H: {g.hadamards}]  (GSLW Lemma 19)",
       s!"OpenQASM 3   : {qubitsStr n} + ancilla q[0], Π: {patternStr cP}  (untrusted output)"]
      ++ toQasmLines n (compileQsvtRealQ Φ cP cP)

/-- LANG-1. The report of `#qsvt_info` as a string (`#eval info e`), with the default pattern
`Π = |0…0⟩⟨0…0|` on `n` system qubits. -/
def info (e : ExprQ) (n : ℕ := 1) : String :=
  "\n".intercalate (infoLines e n (zeroPattern n))

/-! ### The `#qsvt_info` command -/

section Command

open Lean Elab Command

/-- LANG-1. Evaluate a closed elaborated term of type `α` (given as the `Expr` `ty`) with the
compiler, in `CommandElabM` (safe wrapper around `Lean.Meta.evalExpr`). -/
unsafe def evalExprAsImpl (α : Type) [Inhabited α] (ty v : Lean.Expr) : CommandElabM α :=
  liftTermElabM (Meta.evalExpr α ty v)

@[implemented_by evalExprAsImpl]
opaque evalExprAs (α : Type) [Inhabited α] (ty v : Lean.Expr) : CommandElabM α

/-- LANG-1. Elaborate `stx` at the type `ty` and evaluate it as a value of `α`. -/
def elabAndEval (α : Type) [Inhabited α] (ty : Lean.Expr) (stx : Syntax) : CommandElabM α := do
  let v ← liftTermElabM (Term.elabTermAndSynthesize stx (some ty))
  evalExprAs α ty v

/-- LANG-1. `#qsvt_info e` prints the cost and circuit report of the surface program `e : ExprQ`
(see the module docstring). Options: `(n := k)` for `k` system qubits (default `1`), and
`(cP := [(i, b), …])` for the control pattern of `Π` with `ℕ` qubit indices `i < n` (default: all
qubits controlled on `0`). -/
syntax (name := qsvtInfoCmd) "#qsvt_info " Lean.Parser.Term.namedArgument* term : command

/-- LANG-1. The elaborator of `#qsvt_info`: the node is `"#qsvt_info " namedArgument* term`, and
each named argument is `"(" ident " := " term ")"`. -/
@[command_elab qsvtInfoCmd]
def elabQsvtInfo : CommandElab := fun stx => do
  let args := stx[1].getArgs
  let t := stx[2]
  let mut n : ℕ := 1
  let mut cPStx? : Option Syntax := none
  for arg in args do
    let key := arg[1].getId
    let val := arg[3]
    if key == `n then
      n ← elabAndEval ℕ (mkConst ``Nat) val
    else if key == `cP then
      cPStx? := some val
    else
      throwErrorAt arg "#qsvt_info: unknown option `{key}` (expected `n` or `cP`)"
  let cPNat : List (ℕ × Bool) ← match cPStx? with
    | none => pure ((List.range n).map fun i => (i, false))
    | some s =>
      let ty := mkApp (mkConst ``List [.zero])
        (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool))
      elabAndEval (List (ℕ × Bool)) ty s
  let some cP := patternOfNat n cPNat
    | throwError "#qsvt_info: a control qubit index in `cP` is not below n = {n}"
  let prog ← elabAndEval ExprQ (mkConst ``QSVT.Lang.ExprQ) t
  logInfo ("\n".intercalate (infoLines prog n cP))

end Command

end QSVT.Lang
