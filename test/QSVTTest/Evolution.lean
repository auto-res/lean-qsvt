/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Evolution

/-!
# QSVTTest.Evolution

Regression tests for the Hamiltonian-simulation example (APP-4, `QSVT.Certificate.SinExample`
and `QSVT.Examples.Evolution`): the degree-11 odd approximation `sin2Poly` of `sin (2x)`, the
complex input `evoPoly = cos2Poly − i · sin2Poly`, its Chebyshev coefficients computed by
`ChebQC.ofMonomials` (register dimension `12`, coefficients on the coordinate axes, exact `ℓ¹`
norm), the headline theorems instantiated, the query count `66`, and the axiom audit (kernel
trust only). Each check is a compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.Poly QSVT.Pipeline QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The polynomial `sin2Poly` -/

-- degree `11`: twelve coefficients, the even ones zero
#guard sin2Poly.length = 12
#guard (List.range 6).all fun j => sin2Poly.getD (2 * j) 0 == 0
#guard sin2Poly.getD 11 0 ≠ 0

-- the Taylor polynomial `T₁₇` has the coefficients `(-1)^j 2^(2j+1) / (2j+1)!`
#guard sinTaylor17.length = 18
#guard (List.range 9).all fun j => sinTaylor17.getD (2 * j) 0 == 0
#guard (List.range 9).all fun j =>
  sinTaylor17.getD (2 * j + 1) 0 ==
    (-1 : ℚ) ^ j * 2 ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℚ)

-- `p(1) ≈ sin 2 = 0.9092974…` and `p'(0) = a₁ ≈ 2 (1 − 10⁻⁸)`
#guard (0.9092 : ℚ) < sin2Poly.foldr (fun a acc => a + 1 * acc) 0 ∧
  sin2Poly.foldr (fun a acc => a + 1 * acc) 0 < 0.9093
#guard (1.99999997 : ℚ) < sin2Poly.getD 1 0 ∧ sin2Poly.getD 1 0 < 2

/-! ### The complex input `evoPoly` -/

-- the pairs `(cₖ, −sₖ)`: real parts `cos2Poly` (padded), imaginary parts `−sin2Poly`
#guard evoPoly.length = 12
#guard evoPoly.map Prod.fst = cos2Poly ++ [0]
#guard evoPoly.map Prod.snd = sin2Poly.map Neg.neg

/-! ### The computed Chebyshev coefficients of `evoPoly` -/

-- the register dimension `m = 12`, by the compiler and by the kernel
#guard evoCheb.length = 12

example : evoCheb.length = 12 := by decide +kernel

-- the exact Chebyshev coefficients: `(c₂ₖ, 0)` with `c₂ₖ` the coefficients of `cos2Poly`
-- (`J₀(2)`, `2 (-1)^k J_{2k}(2)`) and `(0, −s₂ₖ₊₁)` with `s₂ₖ₊₁ = (1 − 10⁻⁸) 2 (-1)^k J_{2k+1}(2)`,
-- all rounded to 30 significant digits
#guard evoCheb =
  [(4477815582824713361036549093 / 20000000000000000000000000000, 0),
   (0, -115344960397925061926742874049 / 100000000000000000000000000000),
   (-352834028615637719150620787619 / 500000000000000000000000000000, 0),
   (0, 257886496369939112709545643963 / 1000000000000000000000000000000),
   (679914396151368682915184225771 / 10000000000000000000000000000000, 0),
   (0, -140792593709507758510533146849 / 10000000000000000000000000000000),
   (-120242897178999327545834963589 / 50000000000000000000000000000000, 0),
   (0, 87472036559416709911921972697 / 250000000000000000000000000000000),
   (27724440359907380109687221659 / 625000000000000000000000000000000, 0),
   (0, -498468682041925968816389240751 / 100000000000000000000000000000000000),
   (-31442328533959208870439511719 / 62500000000000000000000000000000000, 0),
   (0, 92171389412976153543390549637 / 2000000000000000000000000000000000000)]

-- the real parts are the Chebyshev coefficients of `cos2Poly` (padded), the imaginary parts
-- are minus those of `sin2Poly`
#guard evoCheb.map Prod.fst = cosChebQ ++ [0]
#guard evoCheb.map Prod.snd =
  (ChebQC.ofMonomials (PolyQ.toPolyQC sin2Poly)).map fun z => -z.1

-- every coefficient lies on a coordinate axis; even degrees real, odd degrees imaginary
#guard evoCheb.all fun z => z.1 == 0 || z.2 == 0
#guard (List.range 6).all fun j => (evoCheb.getD (2 * j) 0).2 == 0
#guard (List.range 6).all fun j => (evoCheb.getD (2 * j + 1) 0).1 == 0

/-! ### The subnormalisation `‖c‖₁` -/

-- the exact rational value of the computable `ℓ¹` bound, and its decomposition `cos + sin`
#guard ChebQC.l1Bound evoCheb =
  970308109900781462706584760376036893 / 400000000000000000000000000000000000
#guard ChebQC.l1Bound evoCheb =
  ChebQC.l1Bound cosCheb + ChebQC.l1Bound (ChebQC.ofMonomials (PolyQ.toPolyQC sin2Poly))

-- decimal bounds `2.4257 < ‖c‖₁ < 2.4258`
#guard (2.4257 : ℚ) < ChebQC.l1Bound evoCheb ∧ ChebQC.l1Bound evoCheb < 2.4258

/-- `evoL1` is this value exactly. -/
example :
    evoL1 =
      ((970308109900781462706584760376036893 / 400000000000000000000000000000000000 : ℚ) : ℝ) :=
  evoL1_eq

example : 0 < evoL1 := evoL1_pos

/-! ### The headline theorems instantiated -/

/-- CERT-B certificate: `|p(x) − sin (2x)| ≤ 10⁻⁶` on `[-1, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |sin2Poly.horner x - Real.sin (2 * x)| ≤ 0.000001 :=
  abs_le.mpr (sin2Poly_horner_bound x hx)

/-- CERT-B admissibility: `|sin2Poly(x)| ≤ 1` on `[-1, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |sin2Poly.horner x| ≤ 1 :=
  abs_le.mpr (sin2Poly_abs_bound x hx)

/-- APP-4 certified input: `‖p(x) − e^{-2ix}‖ ≤ 2 · 10⁻⁶` on `[-1, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(PolyQC.toPoly evoPoly).eval (x : ℂ) - Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ ≤
      2 * 0.000001 :=
  norm_eval_evoPoly_sub_exp_le x hx

/-- APP-4 exact implementation: `(⟨0| ⊗ Π) evoCircuit E (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • evoPoly(A) Π`. -/
example (E : HermitianEncoding ℋ) :
    regTopLeft (regP E * evoCircuit E * regP E) =
      ((evoL1 : ℂ)⁻¹) • (aeval E.encoded (PolyQC.toPoly evoPoly) * E.P) :=
  evoCircuit_topLeft E

/-- The circuit is unitary on the register `Reg 12 ℋ`. -/
example (E : HermitianEncoding ℋ) : evoCircuit E ∈ unitary (L (Reg evoCheb.length ℋ)) :=
  evoCircuit_mem_unitary E

/-- The circuit is the unitary of the projected unitary encoding `evoEncoding E`. -/
example (E : HermitianEncoding ℋ) : (evoEncoding E).U = evoCircuit E := evoEncoding_U E

/-- APP-4 certified behaviour on every eigenvector (no gap): `e^{-2iςᵢ} / ‖c‖₁`. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i) -
        ((evoL1 : ℂ)⁻¹ * Complex.exp (-(2 * (eigenValue E i : ℂ)) * Complex.I)) • eigenVec E i‖ ≤
      2 * 0.000001 / evoL1 :=
  evoCircuit_apply E i

/-- APP-4 global bound. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    ‖regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i)‖ ≤ (1 + 2 * 0.000001) / evoL1 :=
  evoCircuit_apply_norm_le E i

/-! ### Resources -/

-- `0 + 1 + ⋯ + 11 = 66` queries for `m = 12`
#guard routeA_queries 12 = 66

/-- `routeA_queries 12 = 12 · 11 / 2`. -/
example : routeA_queries 12 = 12 * 11 / 2 := routeA_queries_eq 12

example : routeA_queries evoCheb.length = 66 := evoCircuit_queries

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.sin2Poly_sub_sinTaylor17_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin2Poly_sub_sinTaylor17_bound

/-- info: 'QSVT.Certificate.sin2Poly_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin2Poly_le_one

/-- info: 'QSVT.Certificate.sin2Poly_abs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin2Poly_abs_bound

/-- info: 'QSVT.Certificate.abs_sin_sub_sinTaylor17_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sin_sub_sinTaylor17_le

/-- info: 'QSVT.Certificate.sin2Poly_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin2Poly_horner_bound

/-- info: 'QSVT.Certificate.norm_eval_sin2Poly_sub_sin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_sin2Poly_sub_sin_le

/-- info: 'QSVT.Certificate.supNorm_sin2Poly_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_sin2Poly_le_one

/-- info: 'QSVT.Examples.evoPoly_toPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoPoly_toPoly

/-- info: 'QSVT.Examples.norm_eval_evoPoly_sub_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_evoPoly_sub_exp_le

/-- info: 'QSVT.Examples.evoL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoL1_eq

/-- info: 'QSVT.Examples.evoCircuit_topLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoCircuit_topLeft

/-- info: 'QSVT.Examples.evoCircuit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoCircuit_apply

/-- info: 'QSVT.Examples.evoCircuit_apply_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoCircuit_apply_norm_le

/-- info: 'QSVT.Examples.evoCircuit_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoCircuit_queries
