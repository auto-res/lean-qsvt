/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.Info
import QSVT.Examples.Loop

/-!
# QSVTTest.Loop

Regression tests for the loop combinators (LANG-2, `QSVT.Lang.Loop`) and the loop examples
(APP-5, `QSVT.Examples.Loop`): the costs of nested QSVT programs (`qsvtIter`, `signIter`), the
`#qsvt_info` report of a nested program, the sweep bookkeeping (`totalQueries`, `maxAncillaDim`,
`expectedQueries`), the classical bisection (`bisect`, `visited`) with the window programs, the
semantics theorems instantiated, and the axiom audit. Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` / `#qsvt_info` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.IR QSVT.Lang QSVT.Examples QSVT.Certificate
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Nested QSVT -/

#guard qsvtIter [1 / 2] 0 = U₀
#guard qsvtIter [1 / 2, -1 / 3] 2 = qsvt[[1 / 2, -1 / 3]] qsvt[[1 / 2, -1 / 3]] U₀
#guard iterate 3 (ExprQ.qsvt [1 / 2]) U₀ = qsvtIter [1 / 2] 3

-- `|Φ| ^ k` queries, `2 ^ k` ancilla dimension, no subnormalisation
#guard queriesQ (qsvtIter [1 / 2, -1 / 3] 3) = 8
#guard ancillaDimQ (qsvtIter [1 / 2, -1 / 3] 3) = 8
#guard degreeBoundQ (qsvtIter [1 / 2, -1 / 3] 3) = 8
#guard scaleQ (qsvtIter [1 / 2, -1 / 3] 3) = 1
#guard wellScaledQ (qsvtIter [1 / 2, -1 / 3] 3) = true

-- APP-5 (a): two iterations of the certified sign step
#guard queriesQ (signIter 2) = 441
#guard ancillaDimQ (signIter 2) = 4
#guard degreeBoundQ (signIter 2) = 441
#guard scaleQ (signIter 2) = 1
#guard wellScaledQ (signIter 2) = true
#guard queriesQ (signIter 3) = 9261

/-- The cost theorems agree with the computed values. -/
example : queriesQ (signIter 2) = 441 := queriesQ_signIter_two

example : ancillaDimQ (signIter 2) = 4 := ancillaDimQ_signIter_two

/-- The IR costs of the nested program, through `queriesQ_eq`/`ancillaDimQ_eq`. -/
example : queries (toExpr (signIter 2)) = 441 := by
  rw [queriesQ_eq, queriesQ_signIter_two]

example : ancillaDim (toExpr (signIter 2)) = 4 := by
  rw [ancillaDimQ_eq, ancillaDimQ_signIter_two]

/-- The semantics of the loop instantiated: `Re[P_Φ̃] ∘ Re[P_Φ̃]`. -/
example : spec (toExpr (signIter 2)) = (spec signBExpr).comp (spec signBExpr) :=
  spec_signIter_two

/-- The correctness theorem of the loop instantiated. -/
example (E₀ : HermitianEncoding ℋ) :
    compress (toExpr (signIter 2)) (denoteQ E₀ (signIter 2)).encoded =
      aeval E₀.encoded ((spec signBExpr).comp (spec signBExpr)) * E₀.P := by
  rw [base_signIter, compIter_succ, compIter_one]

/-- `compIter` evaluates to the iterated scalar map. -/
example (x : ℂ) :
    (spec (toExpr (signIter 2))).eval x = (spec signBExpr).eval ((spec signBExpr).eval x) := by
  rw [spec_signIter, eval_compIter]
  rfl

/--
info: program      : qsvt[[1/2, -1/3]] qsvt[[1/2, -1/3]] U₀
  qsvt       : |Φ| = 2, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact
  qsvt       : |Φ| = 2, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact
queries      : 4
ancilla      : dimension 4 (2 qubits)
degree bound : 4
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
circuit      : (gate-level compilation is reported for single-step programs qsvt[Φ] U₀ only)
-/
#guard_msgs in
#qsvt_info qsvtIter [1 / 2, -1 / 3] 2

/-! ### Sweeps and post-selection bookkeeping -/

#guard totalQueries [qsvtIter [1 / 2] 3, qsvtIter [1 / 2, 1 / 3] 2] = 5
#guard maxAncillaDim [qsvtIter [1 / 2] 3, qsvtIter [1 / 2, 1 / 3] 2] = 8
#guard totalQueries (List.replicate 7 (qsvtIter [1 / 2, 1 / 3] 2)) = 28
#guard expectedQueries (qsvtIter [1 / 2, 1 / 3] 2) (1 / 4) = 16

-- `sweepPrograms`: `T₃` (6 queries) and `x` (1 query)
#guard totalQueries (sweepPrograms [[0, -3, 0, 4], [0, 1]]) = 7
#guard maxAncillaDim (sweepPrograms [[0, -3, 0, 4], [0, 1]]) = 4

/-! ### APP-5 (b): the bisection and the window programs -/

-- searching for `1/3` in `[0, 1]`: midpoints `1/2, 1/4, 3/8`, final interval `[1/4, 3/8]`
#guard (bisect 3 0 1 fun t => decide ((1 : ℚ) / 3 ≤ t)) = 5 / 16
#guard (visited 3 0 1 fun t => decide ((1 : ℚ) / 3 ≤ t)) = [1 / 2, 1 / 4, 3 / 8]
#guard (visited 5 0 1 fun _ => true).length = 5
#guard (bisect 4 0 1 fun _ => false) = 31 / 32

-- every window program costs `21` queries and is well scaled
#guard queriesQ (windowProg (3 / 7)) = 21
#guard ancillaDimQ (windowProg (3 / 7)) = 4
#guard scaleQ (windowProg (-2)) = 1
#guard wellScaledQ (windowProg (-2)) = true
#guard groundEnergyQueries 4 0 1 (fun _ => false) windowProg = 84

/-- The result of the bisection stays in the initial interval. -/
example : (bisect 3 0 1 fun t => decide ((1 : ℚ) / 3 ≤ t)) ∈ Set.Icc (0 : ℚ) 1 :=
  bisect_mem_Icc 3 _ zero_le_one

/-- The cost bound of the search instantiated. -/
example (d : ℚ → Bool) : groundEnergyQueries 10 0 1 d windowProg ≤ 10 * 21 :=
  groundEnergyQueries_le 10 0 1 d windowProg 21 fun t => (queriesQ_windowProg t).le

/-- The window program's correctness theorem (`baseQ_eq` with `scaleQ = 1`). -/
example (E₀ : HermitianEncoding ℋ) (t : ℚ) :
    compress (toExpr (windowProg t)) (denoteQ E₀ (windowProg t)).encoded =
      aeval E₀.encoded (spec (toExpr (windowProg t))) * E₀.P := by
  rw [baseQ_eq E₀ (wellScaledQ_windowProg t)]
  simp [windowProg, scaleQ]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Lang.queriesQ_qsvtIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.queriesQ_qsvtIter

/-- info: 'QSVT.Lang.spec_toExpr_qsvtIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.spec_toExpr_qsvtIter

/-- info: 'QSVT.Lang.base_qsvtIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.base_qsvtIter

/-- info: 'QSVT.Lang.totalQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Lang.totalQueries_le

/-- info: 'QSVT.Examples.bisect_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Examples.bisect_mem_Icc

/-- info: 'QSVT.Examples.length_visited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Examples.length_visited

/-- info: 'QSVT.Examples.base_signIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Examples.base_signIter

/-- info: 'QSVT.Examples.spec_windowProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Examples.spec_windowProg
