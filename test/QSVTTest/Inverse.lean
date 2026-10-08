/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Inverse

/-!
# QSVTTest.Inverse

Regression tests for the matrix-inversion example (APP-3, `QSVT.Certificate.InvExample` and
`QSVT.Examples.Inverse`): the odd degree-29 approximation `invPoly` of `(3/4)/(4x)` on
`|x| ≥ 1/4`, its Chebyshev coefficients computed by `ChebQC.ofMonomials` (register dimension
`30`, all coefficients real, exact `ℓ¹` norm `1663547352803317028028563806518659 / 10³³`), the
headline theorems instantiated, the query count `435`, and the axiom audit (kernel trust only).
Each check is a compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly QSVT.Pipeline QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The polynomial `invPoly` and the constants -/

-- degree `29`: thirty coefficients, the even ones zero, the leading one nonzero
#guard invPoly.length = 30
#guard (List.range 15).all fun j => invPoly.getD (2 * j) 0 == 0
#guard invPoly.getD 29 0 ≠ 0

-- `κ = 4`, `c = 3/4`, `ε = 7.5 · 10⁻⁴ = 10⁻³ · c`
#guard invKappa = 4
#guard invScale = 3 / 4
#guard invEps = 3 / 4000
#guard invEps = invScale / 1000

-- the gap residual `4x · p(x) − 3/4` at the endpoints `x = 1/4` and `x = 1` is within `±ε`
-- (numerically `−7.05 · 10⁻⁴` and `+7.05 · 10⁻⁴`: the error alternates)
#guard -invEps < 4 * (1 / 4) * invPoly.foldr (fun a acc => a + 1 / 4 * acc) 0 - 3 / 4 ∧
  4 * (1 / 4) * invPoly.foldr (fun a acc => a + 1 / 4 * acc) 0 - 3 / 4 < -0.0007
#guard (0.0007 : ℚ) < 4 * 1 * invPoly.foldr (fun a acc => a + 1 * acc) 0 - 3 / 4 ∧
  4 * 1 * invPoly.foldr (fun a acc => a + 1 * acc) 0 - 3 / 4 < invEps

-- `p(1/4) ≈ 0.74929` (target `3/4`) and `p(1) ≈ 0.18768` (target `3/16`)
#guard (0.7492 : ℚ) < invPoly.foldr (fun a acc => a + 1 / 4 * acc) 0 ∧
  invPoly.foldr (fun a acc => a + 1 / 4 * acc) 0 < 0.7494
#guard (0.1876 : ℚ) < invPoly.foldr (fun a acc => a + 1 * acc) 0 ∧
  invPoly.foldr (fun a acc => a + 1 * acc) 0 < 0.1877

/-! ### The computed Chebyshev coefficients of `invPoly` -/

-- the register dimension `m = 30`, by the compiler and by the kernel
#guard invCheb.length = 30

example : invCheb.length = 30 := by decide +kernel

-- the exact Chebyshev coefficients (real parts; odd degrees only, alternating signs): the
-- 30-significant-digit roundings of the LP fit of `tools/phases/inv_cheb.py`
#guard invChebQ =
  [0, 349085763754547806492212203011 / 1000000000000000000000000000000,
   0, -297954220461240482098475013117 / 1000000000000000000000000000000,
   0, 6221614675468219862741747761 / 25000000000000000000000000000,
   0, -101510037221078611158198157227 / 500000000000000000000000000000,
   0, 80701916119045688513544689613 / 500000000000000000000000000000,
   0, -31180605639873345408252802713 / 250000000000000000000000000000,
   0, 466882231272102224406417292357 / 5000000000000000000000000000000,
   0, -84324149552642384264355968071 / 1250000000000000000000000000000,
   0, 233914286000641881424488843777 / 5000000000000000000000000000000,
   0, -309246944076159366310285747659 / 10000000000000000000000000000000,
   0, 96454418273511800113739766971 / 5000000000000000000000000000000,
   0, -3495453315594010705244509829 / 312500000000000000000000000000,
   0, 587902411645632207159994919721 / 100000000000000000000000000000000,
   0, -13346556953258363175524037203 / 5000000000000000000000000000000,
   0, 928465053068109756780057484349 / 1000000000000000000000000000000000]

-- all imaginary parts vanish
#guard invCheb.all fun z => z.2 == 0

-- the even coefficients vanish (oddness) and the odd ones alternate in sign, starting positive
#guard (List.range 15).all fun j => (invCheb.getD (2 * j) 0).1 == 0
#guard (List.range 15).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * (invCheb.getD (2 * j + 1) 0).1

-- the IR coefficient list is `0 :: tail`
#guard invChebQ.tail.length = 29
#guard (0 :: invChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = invCheb

/-! ### The subnormalisation `‖c‖₁` -/

-- the exact rational value of the computable `ℓ¹` bound
#guard ChebQC.l1Bound invCheb =
  1663547352803317028028563806518659 / 1000000000000000000000000000000000

-- decimal bounds `1.6635 < ‖c‖₁ < 1.6636`
#guard (1.6635 : ℚ) < ChebQC.l1Bound invCheb ∧ ChebQC.l1Bound invCheb < 1.6636

-- the output of `#eval` (the `Repr ℚ` instance in this import closure prints `Rat.divInt n d`)
/-- info: Rat.divInt 1663547352803317028028563806518659 1000000000000000000000000000000000 -/
#guard_msgs in
#eval ChebQC.l1Bound invCheb

/-- `invL1` is this value exactly. -/
example :
    invL1 = ((1663547352803317028028563806518659 / 1000000000000000000000000000000000 : ℚ) : ℝ) :=
  invL1_eq

example : 0 < invL1 := invL1_pos

/-! ### The headline theorems instantiated -/

/-- APP-3 exact implementation: `(⟨0| ⊗ Π) invCircuit E (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • invPoly(A) Π`. -/
example (E : HermitianEncoding ℋ) :
    regTopLeft (regP E * invCircuit E * regP E) =
      ((invL1 : ℂ)⁻¹) • (aeval E.encoded invPoly.toPoly * E.P) :=
  invCircuit_topLeft E

/-- The circuit is unitary on the register `Reg 30 ℋ`. -/
example (E : HermitianEncoding ℋ) : invCircuit E ∈ unitary (L (Reg invCheb.length ℋ)) :=
  invCircuit_mem_unitary E

/-- APP-3 certified behaviour on the positive part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : 1 / 4 ≤ eigenValue E i) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
        (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i‖ ≤
      invEps / invL1 :=
  invCircuit_apply_pos E i hi

/-- APP-3 certified behaviour on the negative part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : eigenValue E i ≤ -(1 / 4)) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
        (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i‖ ≤
      invEps / invL1 :=
  invCircuit_apply_neg E i hi

/-- APP-3 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / invL1 :=
  invCircuit_apply_norm_le E i

/-- The certified pointwise bound on the complex polynomial, on `[1/4, 1]`. -/
example : ∀ x ∈ Set.Icc (1 / 4 : ℝ) 1,
    ‖invPoly.toPoly.eval (x : ℂ) - (((invScale : ℝ) / (4 * x) : ℝ) : ℂ)‖ ≤ invEps :=
  norm_eval_invPoly_sub_inv_le

/-! ### Resources -/

-- `0 + 1 + ⋯ + 29 = 435` queries for `m = 30`
#guard routeA_queries 30 = 435

example : routeA_queries invCheb.length = 435 := invCircuit_queries

-- the IR view: `435` queries, a `30`-dimensional ancilla register
#guard QSVT.IR.queries invExpr = 435
#guard QSVT.IR.ancillaDim invExpr = 30

/-- The IR spec of `invExpr` is `invPoly` and its base block is the Route A operator. -/
example (E₀ : HermitianEncoding ℋ) :
    QSVT.IR.base E₀ invExpr = ((invL1 : ℂ)⁻¹) • (aeval E₀.encoded invPoly.toPoly * E₀.P) :=
  base_invExpr E₀

example : QSVT.IR.spec invExpr = invPoly.toPoly := spec_invExpr

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.invPoly_gap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invPoly_gap_bound

/-- info: 'QSVT.Certificate.invPoly_abs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invPoly_abs_bound

/-- info: 'QSVT.Certificate.norm_eval_invPoly_sub_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_invPoly_sub_inv_le

/-- info: 'QSVT.Certificate.norm_eval_invPoly_sub_inv_le_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_invPoly_sub_inv_le_neg

/-- info: 'QSVT.Certificate.supNorm_invPoly_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_invPoly_le_one

/-- info: 'QSVT.Examples.invCircuit_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invCircuit_topLeft

/-- info: 'QSVT.Examples.invCircuit_apply_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invCircuit_apply_pos

/-- info: 'QSVT.Examples.invCircuit_apply_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invCircuit_apply_neg

/-- info: 'QSVT.Examples.invCircuit_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invCircuit_apply_norm_le

/-- info: 'QSVT.Examples.invCircuit_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invCircuit_queries

/-- info: 'QSVT.Examples.invL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invL1_eq

/-- info: 'QSVT.Examples.spec_invExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_invExpr

/-- info: 'QSVT.Examples.base_invExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_invExpr

/-- info: 'QSVT.Examples.queries_invExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_invExpr
