/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.CosEvolution

/-!
# QSVTTest.CosExample

Regression tests for the second application example (APP-4 lite, `QSVT.Certificate.CosExample`
and `QSVT.Examples.CosEvolution`): the degree-10 approximation `cos2Poly` of `cos (2x)`, its
Chebyshev coefficients computed by `ChebQC.ofMonomials` (register dimension `11`, all
coefficients real, exact `ℓ¹` norm `= p(0) = 1 − 3.9 · 10⁻⁹`), the headline theorems
instantiated, the query count `55`, and the axiom audit (kernel trust only). Each check is a
compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly QSVT.Pipeline QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The polynomial `cos2Poly` -/

-- degree `10`: eleven coefficients, the odd ones zero
#guard cos2Poly.length = 11
#guard (List.range 5).all fun j => cos2Poly.getD (2 * j + 1) 0 == 0
#guard cos2Poly.getD 10 0 ≠ 0

-- the Taylor polynomial `T₁₆` has the coefficients `(-1)^j 2^(2j) / (2j)!`
#guard cosTaylor16.length = 17
#guard (List.range 9).all fun j =>
  cosTaylor16.getD (2 * j) 0 == (-1 : ℚ) ^ j * 2 ^ (2 * j) / (Nat.factorial (2 * j) : ℚ)

-- `p(0) = a₀ < 1` and `p(1) ≈ cos 2 = -0.4161…`
#guard cos2Poly.getD 0 0 < 1
#guard (-0.4162 : ℚ) < cos2Poly.foldr (fun a acc => a + 1 * acc) 0 ∧
  cos2Poly.foldr (fun a acc => a + 1 * acc) 0 < -0.4161

/-! ### The computed Chebyshev coefficients of `cos2Poly` -/

-- the register dimension `m = 11`, by the compiler and by the kernel
#guard cosCheb.length = 11

example : cosCheb.length = 11 := by decide +kernel

-- the exact Chebyshev coefficients (real parts; even degrees only, alternating signs):
-- `c₀ = J₀(2)`, `c_{2k} = 2 (-1)^k J_{2k}(2)` rounded to 30 significant digits
#guard cosChebQ =
  [4477815582824713361036549093 / 20000000000000000000000000000, 0,
   -352834028615637719150620787619 / 500000000000000000000000000000, 0,
   679914396151368682915184225771 / 10000000000000000000000000000000, 0,
   -120242897178999327545834963589 / 50000000000000000000000000000000, 0,
   27724440359907380109687221659 / 625000000000000000000000000000000, 0,
   -31442328533959208870439511719 / 62500000000000000000000000000000000]

-- all imaginary parts vanish
#guard cosCheb.all fun z => z.2 == 0

-- the odd coefficients vanish (evenness) and the even ones alternate in sign, starting positive
#guard (List.range 5).all fun j => (cosCheb.getD (2 * j + 1) 0).1 == 0
#guard (List.range 6).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * (cosCheb.getD (2 * j) 0).1

-- the IR coefficient list is `c₀ :: tail`
#guard cosChebQ.headD 0 = cosChebQ0
#guard cosChebQ.tail.length = 10
#guard (cosChebQ0 :: cosChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = cosCheb

/-! ### The subnormalisation `‖c‖₁` -/

-- the exact rational value of the computable `ℓ¹` bound: the constant coefficient `p(0)`
#guard ChebQC.l1Bound cosCheb =
  62499999757066272271938848645232619 / 62500000000000000000000000000000000
#guard ChebQC.l1Bound cosCheb = cos2Poly.getD 0 0

-- decimal bounds `0.9999999 < ‖c‖₁ < 1`
#guard (0.9999999 : ℚ) < ChebQC.l1Bound cosCheb ∧ ChebQC.l1Bound cosCheb < 1

/-- `cosL1` is this value exactly. -/
example :
    cosL1 = ((62499999757066272271938848645232619 / 62500000000000000000000000000000000 : ℚ) : ℝ) :=
  cosL1_eq

example : 0 < cosL1 := cosL1_pos

/-! ### The headline theorems instantiated -/

/-- CERT-B certificate: `|p(x) − cos (2x)| ≤ 10⁻⁶` on `[-1, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |cos2Poly.horner x - Real.cos (2 * x)| ≤ 0.000001 :=
  abs_le.mpr (cos2Poly_horner_bound x hx)

/-- APP-4 exact implementation: `(⟨0| ⊗ Π) cosCircuit E (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • cos2Poly(A) Π`. -/
example (E : HermitianEncoding ℋ) :
    regTopLeft (regP E * cosCircuit E * regP E) =
      ((cosL1 : ℂ)⁻¹) • (aeval E.encoded cos2Poly.toPoly * E.P) :=
  cosCircuit_topLeft E

/-- The circuit is unitary on the register `Reg 11 ℋ`. -/
example (E : HermitianEncoding ℋ) : cosCircuit E ∈ unitary (L (Reg cosCheb.length ℋ)) :=
  cosCircuit_mem_unitary E

/-- APP-4 certified behaviour on every eigenvector (no gap). -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i) -
        ((Real.cos (2 * eigenValue E i) / cosL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.000001 / cosL1 :=
  cosCircuit_apply E i

/-- APP-4 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / cosL1 :=
  cosCircuit_apply_norm_le E i

/-! ### Resources -/

-- `0 + 1 + ⋯ + 10 = 55` queries for `m = 11`
#guard routeA_queries 11 = 55

/-- `routeA_queries 11 = 11 · 10 / 2`. -/
example : routeA_queries 11 = 11 * 10 / 2 := routeA_queries_eq 11

example : routeA_queries cosCheb.length = 55 := cosCircuit_queries

-- the IR view: `55` queries, an `11`-dimensional ancilla register
#guard QSVT.IR.queries cosExpr = 55
#guard QSVT.IR.ancillaDim cosExpr = 11

/-- The IR spec of `cosExpr` is `cos2Poly` and its base block is the Route A operator. -/
example (E₀ : HermitianEncoding ℋ) :
    QSVT.IR.base E₀ cosExpr = ((cosL1 : ℂ)⁻¹) • (aeval E₀.encoded cos2Poly.toPoly * E₀.P) :=
  base_cosExpr E₀

example : QSVT.IR.spec cosExpr = cos2Poly.toPoly := spec_cosExpr

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.cos2Poly_sub_cosTaylor16_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos2Poly_sub_cosTaylor16_bound

/-- info: 'QSVT.Certificate.cos2Poly_abs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos2Poly_abs_bound

/-- info: 'QSVT.Certificate.abs_cos_sub_cosTaylor16_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_cos_sub_cosTaylor16_le

/-- info: 'QSVT.Certificate.cos2Poly_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos2Poly_horner_bound

/-- info: 'QSVT.Certificate.norm_eval_cos2Poly_sub_cos_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_cos2Poly_sub_cos_le

/-- info: 'QSVT.Certificate.supNorm_cos2Poly_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_cos2Poly_le_one

/-- info: 'QSVT.Examples.cosL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosL1_eq

/-- info: 'QSVT.Examples.cosCircuit_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosCircuit_topLeft

/-- info: 'QSVT.Examples.cosCircuit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosCircuit_apply

/-- info: 'QSVT.Examples.cosCircuit_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosCircuit_apply_norm_le

/-- info: 'QSVT.Examples.cosCircuit_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosCircuit_queries

/-- info: 'QSVT.Examples.spec_cosExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spec_cosExpr

/-- info: 'QSVT.Examples.base_cosExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_cosExpr

/-- info: 'QSVT.Examples.queries_cosExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_cosExpr
