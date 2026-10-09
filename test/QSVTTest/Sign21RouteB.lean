/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Sign21RouteB

/-!
# QSVTTest.Sign21RouteB

Regression tests for the Route B application example (APP-1, `QSVT.Examples.Sign21RouteB`) and
its certified phases (CERT-B part 2, `QSVT.Certificate.Sign21Phases`): the shape of the data
(`21` phases, `22` target coefficients, symmetric phases, `|φ| ≤ 2.31`), the identification of the
target with the Route A coefficient list, the headline theorems instantiated, the resource counts
(`21` queries, one ancilla qubit) and the axiom audit (kernel trust only).  Each check is a
compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The certified data -/

#guard sign21Phases.length = 21
#guard sign21Target.length = 22
#guard sign21Eps = 1 / 1000000000000

-- symmetric QSP phases: the last `20` are palindromic
#guard sign21Phases.tail = sign21Phases.tail.reverse

-- phase magnitudes `|φ| ≤ 2.31` (the reason for Taylor depth `30` in `sign21_checkRe`)
#guard sign21Phases.all fun φ => |φ| ≤ 2.31

-- the target is odd (even coefficients vanish) with alternating odd coefficients
#guard (List.range 11).all fun j => sign21Target.getD (2 * j) 0 == 0
#guard (List.range 11).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * sign21Target.getD (2 * j + 1) 0

-- the JSON target coincides with the Chebyshev coefficients computed by POLY-6 (Route A's list)
#guard sign21Target = signChebQ
#guard sign21Target = (ChebQC.ofMonomials (PolyQ.toPolyQC sign21)).map Prod.fst

example : sign21Phases.length = 21 := sign21Phases_length
example : sign21Target = signChebQ := sign21Target_eq_signChebQ

/-! ### The headline theorems instantiated -/

/-- CERT-B: the certified polynomial statement about the phases. -/
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)‖ ≤
      ((1 / 10 ^ 12 : ℚ) : ℝ) :=
  sign21_rePoly_bound

/-- APP-1 exact implementation: `(⟨0| ⊗ Π) (signB E).U (|0⟩ ⊗ Π) = Re[P_Φ̃](A) Π`. -/
example (E : HermitianEncoding ℋ) :
    topLeft (signB E).encoded =
      aeval E.encoded (rePoly (qspPoly (sign21Phases.map (↑))).1) * E.P :=
  signB_topLeft E

/-- The Route B unitary is the denotation of the compiled gate list. -/
example (E : HermitianEncoding ℋ) :
    (signB E).U =
      QSVT.Circuit.denote E.toProjUnitaryEncoding
        (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) :=
  signB_U_eq E

/-- APP-1 certified behaviour on the positive part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : 0.15 ≤ eigenValue E i) :
    ‖topLeft (signB E).encoded (eigenVec E i) - (sign21Scale : ℂ) • eigenVec E i‖ ≤
      sign21Eps + 0.0236 :=
  signB_apply_pos E i hi

/-- APP-1 certified behaviour on the negative part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : eigenValue E i ≤ -0.15) :
    ‖topLeft (signB E).encoded (eigenVec E i) - (-(sign21Scale : ℂ)) • eigenVec E i‖ ≤
      sign21Eps + 0.0236 :=
  signB_apply_neg E i hi

/-- APP-1 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖topLeft (signB E).encoded (eigenVec E i)‖ ≤ 1 + sign21Eps :=
  signB_apply_norm_le E i

/-- The error bound is below `0.024`. -/
example : (sign21Eps : ℝ) + 0.0236 ≤ 0.024 := by
  rw [sign21Eps]; norm_num

/-! ### Resources: `21` queries, one ancilla qubit -/

example : QSVT.Circuit.oracleCount (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 :=
  signB_oracleCount
example : QSVT.Circuit.cpiNotCount (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) = 42 :=
  signB_cpiNotCount
example : QSVT.Circuit.phaseCount (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 :=
  signB_phaseCount
example : QSVT.Circuit.hadCount (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) = 2 :=
  signB_hadCount
example : (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))).length = 86 := signB_length

-- the IR view: `21` queries and a `2`-dimensional ancilla, against `231` and `22` for Route A
example : QSVT.IR.queries signBExpr = 21 := queries_signBExpr
example : QSVT.IR.ancillaDim signBExpr = 2 := ancillaDim_signBExpr
example : QSVT.IR.queries signExpr = 11 * QSVT.IR.queries signBExpr := by
  rw [queries_signExpr, queries_signBExpr]
example : QSVT.IR.scale signBExpr = 1 := scale_signBExpr

/-- The IR base block is the Route B operator. -/
example (E₀ : HermitianEncoding ℋ) :
    QSVT.IR.base E₀ signBExpr =
      aeval E₀.encoded (rePoly (qspPoly (sign21Phases.map (↑))).1) * E₀.P :=
  base_signBExpr E₀

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.sign21_checkRe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_checkRe

/-- info: 'QSVT.Certificate.target_sign21_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_sign21_eq

/-- info: 'QSVT.Certificate.sign21_rePoly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_rePoly_bound

/-- info: 'QSVT.Examples.signB_U_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_U_eq

/-- info: 'QSVT.Examples.signB_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_topLeft

/-- info: 'QSVT.Examples.signB_apply_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_apply_pos

/-- info: 'QSVT.Examples.signB_apply_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_apply_neg

/-- info: 'QSVT.Examples.signB_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_apply_norm_le

/-- info: 'QSVT.Examples.signB_oracleCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signB_oracleCount

/-- info: 'QSVT.Examples.queries_signBExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_signBExpr

/-- info: 'QSVT.Examples.base_signBExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_signBExpr
