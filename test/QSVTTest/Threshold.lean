/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Threshold

/-!
# QSVTTest.Threshold

Regression tests for the threshold-projector example (APP-2, `QSVT.Certificate.RectExample` and
`QSVT.Examples.Threshold`): the even degree-32 approximation `rectPoly` of the rectangle
function with plateaus `|x| ≤ 0.4` and `|x| ≥ 0.6`, its Chebyshev coefficients computed by
`ChebQC.ofMonomials` (register dimension `33`, all coefficients real, exact `ℓ¹` norm
`1293999354903681376499635646837 / (8 · 10²⁹)`), the headline theorems instantiated, the query
count `528`, and the axiom audit (kernel trust only).  Each check is a compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly QSVT.Pipeline QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The polynomial `rectPoly` and the constants -/

-- degree `32`: thirty-three coefficients, the odd ones zero, the leading one nonzero
#guard rectPoly.length = 33
#guard (List.range 16).all fun j => rectPoly.getD (2 * j + 1) 0 == 0
#guard rectPoly.getD 32 0 ≠ 0

-- `t = 1/2`, `δ = 1/10`, `ε = 10⁻²`; the plateau boundaries are `t ∓ δ = 0.4, 0.6`
#guard rectThreshold = 1 / 2
#guard rectDelta = 1 / 10
#guard rectEps = 1 / 100
#guard rectThreshold - rectDelta = (0.4 : ℚ) ∧ rectThreshold + rectDelta = (0.6 : ℚ)

-- the values at `x = 0, 0.4` lie in `[1 − ε, 1]` with the `2.4 · 10⁻³` margin on both sides
-- (numerically `r(0) = 0.992401`, `r(0.4) = 0.992401`; `max r = 0.997599`)
#guard (0.9924 : ℚ) < rectPoly.foldr (fun a acc => a + 0 * acc) 0 ∧
  rectPoly.foldr (fun a acc => a + 0 * acc) 0 < 0.9925
#guard (0.9924 : ℚ) < rectPoly.foldr (fun a acc => a + 2 / 5 * acc) 0 ∧
  rectPoly.foldr (fun a acc => a + 2 / 5 * acc) 0 < 0.9925

-- the values at `x = 0.6, 1` lie in `[-ε, ε]` (numerically `r(0.6) = 0.0075994`,
-- `r(1) = 0.0075999`: the error alternates and touches `ε − μ = 0.0076`)
#guard (0.0075 : ℚ) < rectPoly.foldr (fun a acc => a + 3 / 5 * acc) 0 ∧
  rectPoly.foldr (fun a acc => a + 3 / 5 * acc) 0 < 0.0076
#guard (0.0075 : ℚ) < rectPoly.foldr (fun a acc => a + 1 * acc) 0 ∧
  rectPoly.foldr (fun a acc => a + 1 * acc) 0 < 0.0076

-- the midpoint of the transition band: `r(1/2) ≈ 0.5838` (unconstrained there)
#guard (0.58 : ℚ) < rectPoly.foldr (fun a acc => a + 1 / 2 * acc) 0 ∧
  rectPoly.foldr (fun a acc => a + 1 / 2 * acc) 0 < 0.59

/-! ### The computed Chebyshev coefficients of `rectPoly` -/

-- the register dimension `m = 33`, by the compiler and by the kernel
#guard rectCheb.length = 33

example : rectCheb.length = 33 := by decide +kernel

-- the exact Chebyshev coefficients (real parts; even degrees only): the 30-significant-digit
-- roundings of the LP fit of `tools/phases/rect_cheb.py --degree 32`
#guard rectChebQ =
  [84805196299192142639356006839 / 250000000000000000000000000000, 0,
   -552917456118918182461641208647 / 1000000000000000000000000000000, 0,
   260641220808875584413755177593 / 1000000000000000000000000000000, 0,
   18079941432036865898991262469 / 1250000000000000000000000000000, 0,
   -131884986060672976249108501179 / 1000000000000000000000000000000, 0,
   440815764072757382274758697349 / 5000000000000000000000000000000, 0,
   15856938523187802218827879841 / 1250000000000000000000000000000, 0,
   -321480915493332561339023811797 / 5000000000000000000000000000000, 0,
   413858476169982406056568891017 / 10000000000000000000000000000000, 0,
   25599527623751273247565407587 / 2500000000000000000000000000000, 0,
   -335450168227974243606581694621 / 10000000000000000000000000000000, 0,
   49965148622171480161102685713 / 2500000000000000000000000000000, 0,
   159890413188107545494620609361 / 20000000000000000000000000000000, 0,
   -75904679094322032029129587727 / 5000000000000000000000000000000, 0,
   53137566780890902948253362581 / 5000000000000000000000000000000, 0,
   142822248637845001378865461561 / 20000000000000000000000000000000, 0,
   -142501767249274061133412772051 / 20000000000000000000000000000000]

-- all imaginary parts vanish
#guard rectCheb.all fun z => z.2 == 0

-- the odd coefficients vanish (evenness); the leading coefficient `c₀ ≈ 0.3392` is nonzero
#guard (List.range 16).all fun j => (rectCheb.getD (2 * j + 1) 0).1 == 0
#guard (0.3392 : ℚ) < (rectCheb.getD 0 0).1 ∧ (rectCheb.getD 0 0).1 < 0.3393

-- the IR coefficient list is `c₀ :: tail`
#guard rectChebQ.tail.length = 32
#guard (rectChebQ.headD 0 :: rectChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = rectCheb

/-! ### The subnormalisation `‖c‖₁` -/

-- the exact rational value of the computable `ℓ¹` bound
#guard ChebQC.l1Bound rectCheb =
  1293999354903681376499635646837 / 800000000000000000000000000000

-- decimal bounds `1.6174 < ‖c‖₁ < 1.6175`
#guard (1.6174 : ℚ) < ChebQC.l1Bound rectCheb ∧ ChebQC.l1Bound rectCheb < 1.6175

-- the output of `#eval` (the `Repr ℚ` instance in this import closure prints `Rat.divInt n d`)
/-- info: Rat.divInt 1293999354903681376499635646837 800000000000000000000000000000 -/
#guard_msgs in
#eval ChebQC.l1Bound rectCheb

/-- `rectL1` is this value exactly. -/
example :
    rectL1 = ((1293999354903681376499635646837 / 800000000000000000000000000000 : ℚ) : ℝ) :=
  rectL1_eq

example : 0 < rectL1 := rectL1_pos

/-! ### The headline theorems instantiated -/

/-- APP-2 exact implementation: `(⟨0| ⊗ Π) rectCircuit E (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • rectPoly(A) Π`. -/
example (E : HermitianEncoding ℋ) :
    regTopLeft (regP E * rectCircuit E * regP E) =
      ((rectL1 : ℂ)⁻¹) • (aeval E.encoded rectPoly.toPoly * E.P) :=
  rectCircuit_topLeft E

/-- The circuit is unitary on the register `Reg 33 ℋ`. -/
example (E : HermitianEncoding ℋ) : rectCircuit E ∈ unitary (L (Reg rectCheb.length ℋ)) :=
  rectCircuit_mem_unitary E

/-- APP-2 certified behaviour inside the window `|λ| ≤ 0.4`. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : |eigenValue E i| ≤ 0.4) :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i) -
        ((1 / rectL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ rectEps / rectL1 :=
  rectCircuit_apply_inner E i hi

/-- APP-2 certified behaviour outside the window `|λ| ≥ 0.6`. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : 0.6 ≤ |eigenValue E i|) :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i)‖ ≤ rectEps / rectL1 :=
  rectCircuit_apply_outer E i hi

/-- APP-2 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / rectL1 :=
  rectCircuit_apply_norm_le E i

/-- The certified pointwise bounds on the complex polynomial. -/
example : ∀ x ∈ Set.Icc (-0.4 : ℝ) 0.4, ‖rectPoly.toPoly.eval (x : ℂ) - 1‖ ≤ rectEps :=
  norm_eval_rectPoly_sub_one_le

example : ∀ x ∈ Set.Icc (0.6 : ℝ) 1, ‖rectPoly.toPoly.eval (x : ℂ)‖ ≤ rectEps :=
  norm_eval_rectPoly_le

/-! ### Resources -/

-- `0 + 1 + ⋯ + 32 = 528` queries for `m = 33`
#guard routeA_queries 33 = 528

example : routeA_queries rectCheb.length = 528 := rectCircuit_queries

-- the IR view: `528` queries, a `33`-dimensional ancilla register
#guard QSVT.IR.queries rectExpr = 528
#guard QSVT.IR.ancillaDim rectExpr = 33

/-- The IR spec of `rectExpr` is `rectPoly` and its base block is the Route A operator. -/
example (E₀ : HermitianEncoding ℋ) :
    QSVT.IR.base E₀ rectExpr = ((rectL1 : ℂ)⁻¹) • (aeval E₀.encoded rectPoly.toPoly * E₀.P) :=
  base_rectExpr E₀

example : QSVT.IR.spec rectExpr = rectPoly.toPoly := spec_rectExpr

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.rectPoly_abs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectPoly_abs_bound

/-- info: 'QSVT.Certificate.rectPoly_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectPoly_inner_bound

/-- info: 'QSVT.Certificate.rectPoly_outer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectPoly_outer_bound

/-- info: 'QSVT.Certificate.norm_eval_rectPoly_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_rectPoly_sub_one_le

/-- info: 'QSVT.Certificate.norm_eval_rectPoly_le_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_rectPoly_le_of_abs

/-- info: 'QSVT.Certificate.supNorm_rectPoly_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_rectPoly_le_one

/-- info: 'QSVT.Examples.rectCircuit_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectCircuit_topLeft

/-- info: 'QSVT.Examples.rectCircuit_apply_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectCircuit_apply_inner

/-- info: 'QSVT.Examples.rectCircuit_apply_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectCircuit_apply_outer

/-- info: 'QSVT.Examples.rectCircuit_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectCircuit_apply_norm_le

/-- info: 'QSVT.Examples.rectCircuit_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectCircuit_queries

/-- info: 'QSVT.Examples.rectL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectL1_eq

/-- info: 'QSVT.Examples.spec_rectExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_rectExpr

/-- info: 'QSVT.Examples.base_rectExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_rectExpr

/-- info: 'QSVT.Examples.queries_rectExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_rectExpr
