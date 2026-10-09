/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Pipeline.ChebLCU

/-!
# QSVTTest.ChebLCU

Regression tests for Route A (CERT-A, `QSVT.Pipeline.ChebLCU`): the exact Chebyshev-LCU
implementation of a polynomial of a Hermitian block encoding. The demo input is
`4x³ − 3x = T₃`, whose Chebyshev coefficients are computed by `ChebQC.ofMonomials` (POLY-6) and
checked by `#guard`; the headline theorem `routeA` is then instantiated on it. Each check is a
compile-time assertion.
-/

-- `#guard` / `#eval` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.Poly QSVT.Pipeline
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The demo polynomial `4x³ − 3x = T₃` -/

/-- The demo polynomial `4x³ − 3x` in the monomial basis. -/
def demo : PolyQC := [(0, 0), (-3, 0), (0, 0), (4, 0)]

-- `4x³ − 3x = T₃`: a single Chebyshev coefficient
#guard ChebQC.ofMonomials demo = [(0, 0), (0, 0), (0, 0), (1, 0)]

-- the output of `#eval`
/-- info: [(0, 0), (0, 0), (0, 0), (1, 0)] -/
#guard_msgs in
#eval ChebQC.ofMonomials demo

-- the register dimension `m = 4`
#guard (ChebQC.ofMonomials demo).length = 4

/-- The register dimension of the demo is nonzero, reproved by the kernel (`Rat` arithmetic is
`@[irreducible]`, so plain `decide` does not unfold it). -/
instance demo_neZero : NeZero (ChebQC.ofMonomials demo).length := ⟨by decide +kernel⟩

/-! ### The exact theorems instantiated on the demo -/

/-- CERT-A on the demo: Route A block-encodes `‖c‖₁⁻¹ • (4x³ − 3x)(A) Π` exactly. -/
example (E : HermitianEncoding ℋ) (h : l1 (chebCoeffs demo) ≠ 0) :
    regTopLeft (regP E * chebLCU E (chebCoeffs demo) * regP E) =
      ((l1 (chebCoeffs demo) : ℂ)⁻¹) • (aeval E.encoded (PolyQC.toPoly demo) * E.P) :=
  routeA E demo h

/-- The Route A unitary of the demo is unitary. -/
example (E : HermitianEncoding ℋ) :
    chebLCU E (chebCoeffs demo) ∈ unitary (L (Reg (ChebQC.ofMonomials demo).length ℋ)) :=
  chebLCU_mem_unitary E _

/-- The demo has real coefficients, so Route A gives a *Hermitian* encoding on the register. -/
noncomputable example (E : HermitianEncoding ℋ) :
    HermitianEncoding (Reg (ChebQC.ofMonomials demo).length ℋ) :=
  chebHermitianEncoding E (chebCoeffs demo) fun k => by
    have h : ((ChebQC.ofMonomials demo).getD k 0).2 = 0 := by
      revert k
      decide +kernel
    have him : ∀ z : QC, (QC.toC z).im = (z.2 : ℝ) := fun z => by simp [QC.toC]
    change (QC.toC ((ChebQC.ofMonomials demo).getD k 0)).im = 0
    rw [him, h, Rat.cast_zero]

/-- The Chebyshev expansion of the demo is `PolyQC.toPoly demo` (POLY-6 correctness). -/
example :
    ∑ k : Fin (ChebQC.ofMonomials demo).length,
        C (chebCoeffs demo k) * Polynomial.Chebyshev.T ℂ (k : ℕ) =
      PolyQC.toPoly demo :=
  sum_C_chebCoeffs_mul_T demo

/-! ### Resource count -/

-- `0 + 1 + 2 + 3 = 6` queries for `m = 4`
#guard routeA_queries 4 = 6

/-- `routeA_queries 4 = 4 · 3 / 2`. -/
example : routeA_queries 4 = 4 * 3 / 2 := routeA_queries_eq 4

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Pipeline.regTopLeft_regP_chebLCU_regP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Pipeline.regTopLeft_regP_chebLCU_regP

/-- info: 'QSVT.Pipeline.routeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Pipeline.routeA

/-- info: 'QSVT.Pipeline.chebLCU_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Pipeline.chebLCU_mem_unitary

/-- info: 'QSVT.Pipeline.chebHermitianEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Pipeline.chebHermitianEncoding
