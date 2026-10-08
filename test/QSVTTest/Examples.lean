/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Sign21

/-!
# QSVTTest.Examples

Regression tests for the first application example (APP-1 lite, `QSVT.Examples.Sign21`): the
Chebyshev coefficients of the certified degree-21 sign approximation `sign21` computed by
`ChebQC.ofMonomials` (register dimension `22`, all coefficients real, exact `ℓ¹` norm
`159582649048909303 / 72057594037927936 ≈ 2.2147`), the headline theorems instantiated, the query
count `231`, and the axiom audit (kernel trust only). Each check is a compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly QSVT.Pipeline QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The computed Chebyshev coefficients of `sign21` -/

-- the register dimension `m = 22`, by the compiler and by the kernel
#guard signCheb.length = 22

example : signCheb.length = 22 := by decide +kernel

-- the exact Chebyshev coefficients (real parts; odd degrees only, alternating signs)
#guard signChebQ =
  [0, 5104259128596299 / 4503599627370496, 0, -1667563197230541 / 4503599627370496,
   0, 7688981794739765 / 36028797018963968, 0, -5170919160542979 / 36028797018963968,
   0, 7422883927095795 / 72057594037927936, 0, -5493494299215661 / 72057594037927936,
   0, 1030359789386511 / 18014398509481984, 0, -3104546081626977 / 72057594037927936,
   0, 2334045259532281 / 72057594037927936, 0, -6978069399079591 / 288230376151711744,
   0, 5171055401310877 / 288230376151711744]

-- all imaginary parts vanish
#guard signCheb.all fun z => z.2 == 0

-- the even coefficients vanish (oddness) and the odd ones alternate in sign, starting positive
#guard (List.range 11).all fun j => (signCheb.getD (2 * j) 0).1 == 0
#guard (List.range 11).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * (signCheb.getD (2 * j + 1) 0).1

-- the IR coefficient list is `0 :: tail`
#guard signChebQ.tail.length = 21
#guard (0 :: signChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = signCheb

/-! ### The subnormalisation `‖c‖₁` -/

-- the exact rational value of the computable `ℓ¹` bound
#guard ChebQC.l1Bound signCheb = 159582649048909303 / 72057594037927936

-- decimal bounds `2.2146 < ‖c‖₁ < 2.2147`
#guard (2.2146 : ℚ) < ChebQC.l1Bound signCheb ∧ ChebQC.l1Bound signCheb < 2.2147

-- the output of `#eval`; the `Repr ℚ` instance selected in this import closure (which includes
-- LeanCert) prints `Rat.divInt n d`, the exact value is the `#guard` above
/-- info: Rat.divInt 159582649048909303 72057594037927936 -/
#guard_msgs in
#eval ChebQC.l1Bound signCheb

/-- `signL1` is this value exactly. -/
example : signL1 = ((159582649048909303 / 72057594037927936 : ℚ) : ℝ) := signL1_eq

example : 0 < signL1 := signL1_pos

/-! ### The headline theorems instantiated -/

/-- APP-1 exact implementation: `(⟨0| ⊗ Π) signCircuit E (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • sign21(A) Π`. -/
example (E : HermitianEncoding ℋ) :
    regTopLeft (regP E * signCircuit E * regP E) =
      ((signL1 : ℂ)⁻¹) • (aeval E.encoded sign21.toPoly * E.P) :=
  signCircuit_topLeft E

/-- The circuit is unitary on the register `Reg 22 ℋ`. -/
example (E : HermitianEncoding ℋ) : signCircuit E ∈ unitary (L (Reg signCheb.length ℋ)) :=
  signCircuit_mem_unitary E

/-- APP-1 certified behaviour on the positive part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : 0.15 ≤ eigenValue E i) :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
        (((sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.0236 / signL1 :=
  signCircuit_apply_pos E i hi

/-- APP-1 certified behaviour on the negative part of the gapped spectrum. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E)))
    (hi : eigenValue E i ≤ -0.15) :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
        ((-(sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.0236 / signL1 :=
  signCircuit_apply_neg E i hi

/-- APP-1 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / signL1 :=
  signCircuit_apply_norm_le E i

/-! ### Resources -/

-- `0 + 1 + ⋯ + 21 = 231` queries for `m = 22`
#guard routeA_queries 22 = 231

/-- `routeA_queries 22 = 22 · 21 / 2`. -/
example : routeA_queries 22 = 22 * 21 / 2 := routeA_queries_eq 22

example : routeA_queries signCheb.length = 231 := signCircuit_queries

-- the IR view: `231` queries, a `22`-dimensional ancilla register
#guard QSVT.IR.queries signExpr = 231
#guard QSVT.IR.ancillaDim signExpr = 22

/-- The IR spec of `signExpr` is `sign21` and its base block is the Route A operator. -/
example (E₀ : HermitianEncoding ℋ) :
    QSVT.IR.base E₀ signExpr = ((signL1 : ℂ)⁻¹) • (aeval E₀.encoded sign21.toPoly * E₀.P) :=
  base_signExpr E₀

example : QSVT.IR.spec signExpr = sign21.toPoly := spec_signExpr

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Examples.signCircuit_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signCircuit_topLeft

/-- info: 'QSVT.Examples.signCircuit_apply_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signCircuit_apply_pos

/-- info: 'QSVT.Examples.signCircuit_apply_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signCircuit_apply_neg

/-- info: 'QSVT.Examples.signCircuit_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signCircuit_apply_norm_le

/-- info: 'QSVT.Examples.signCircuit_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signCircuit_queries

/-- info: 'QSVT.Examples.signL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signL1_eq

/-- info: 'QSVT.Examples.spec_signExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_signExpr

/-- info: 'QSVT.Examples.base_signExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_signExpr

/-- info: 'QSVT.Examples.queries_signExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_signExpr
