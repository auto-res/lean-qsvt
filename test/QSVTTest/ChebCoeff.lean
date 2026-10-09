/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Polynomial.ChebCoeff

/-!
# QSVTTest.ChebCoeff

Regression tests for the computable monomial → Chebyshev conversion (formal-spec POLY-6):
`#eval`/`#guard` checks of `ChebQC.ofMonomials` on small polynomials, the computable `ℓ¹`
bound, the Gaussian-rational arithmetic, and the axiom audit of the correctness theorems.
Polynomials are given as monomial coefficient lists (index = degree).
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.Poly

/-! ### Gaussian rationals -/

-- `i · i = -1`
#guard QC.mul (0, 1) (0, 1) = (-1, 0)

-- `(1 + 2i)(3 - i) = 5 + 5i`
#guard QC.mul (1, 2) (3, -1) = (5, 5)

#guard QC.smulQ (1 / 2) (3, -1) = (3 / 2, -1 / 2)

-- padding on either side
#guard QC.addList [(1, 0), (2, 0)] [(0, 1)] = [(1, 1), (2, 0)]

#guard QC.addList [(0, 1)] [(1, 0), (2, 0)] = [(1, 1), (2, 0)]

/-! ### `ofMonomials` on small polynomials -/

-- `x² = (T₀ + T₂) / 2`
#guard ChebQC.ofMonomials [(0, 0), (0, 0), (1, 0)] = [(1 / 2, 0), (0, 0), (1 / 2, 0)]

-- `4x³ - 3x = T₃`
#guard ChebQC.ofMonomials [(0, 0), (-3, 0), (0, 0), (4, 0)] = [(0, 0), (0, 0), (0, 0), (1, 0)]

-- `x³ = (3 T₁ + T₃) / 4`
#guard ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (1, 0)] =
  [(0, 0), (3 / 4, 0), (0, 0), (1 / 4, 0)]

-- `x⁴ = (3 T₀ + 4 T₂ + T₄) / 8`
#guard ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0)] =
  [(3 / 8, 0), (0, 0), (1 / 2, 0), (0, 0), (1 / 8, 0)]

-- constants and the linear term are unchanged; imaginary parts are carried along
#guard ChebQC.ofMonomials [(2, -1)] = [(2, -1)]

#guard ChebQC.ofMonomials [(0, 0), (0, 1)] = [(0, 0), (0, 1)]

-- `i x² = (i T₀ + i T₂) / 2`
#guard ChebQC.ofMonomials [(0, 0), (0, 0), (0, 1)] = [(0, 1 / 2), (0, 0), (0, 1 / 2)]

-- the empty polynomial
#guard ChebQC.ofMonomials [] = []

-- multiplication by `X` in the Chebyshev basis: `X T₁ = (T₀ + T₂) / 2`
#guard ChebQC.mulX [(0, 0), (1, 0)] = [(1 / 2, 0), (0, 0), (1 / 2, 0)]

-- `X (T₀ + T₁ + T₂) = T₁ + (T₀ + T₂) / 2 + (T₁ + T₃) / 2`
#guard ChebQC.mulX [(1, 0), (1, 0), (1, 0)] = [(1 / 2, 0), (3 / 2, 0), (1 / 2, 0), (1 / 2, 0)]

-- the output of `#eval`
/-- info: [(1 / 2, 0), (0, 0), (1 / 2, 0)] -/
#guard_msgs in
#eval ChebQC.ofMonomials [(0, 0), (0, 0), (1, 0)]

/-! ### The computable `ℓ¹` bound -/

-- `x⁴ = (3 T₀ + 4 T₂ + T₄) / 8` has `ℓ¹` norm `1` (all coefficients are positive)
#guard ChebQC.l1Bound (ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]) = 1

-- `|re| + |im|` is summed: `1 + i` contributes `2`
#guard ChebQC.l1Bound [(1, 1), (-1, 0)] = 3

-- length of the conversion
#guard (ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]).length = 5

/-! ### The exact theorems instantiated on a concrete input -/

/-- The correctness theorem on `x²`, with the `#guard`-checked coefficients reproved by the
kernel (`Rat` arithmetic is `@[irreducible]`, so plain `decide` does not unfold it). -/
example :
    ChebQC.toPoly [(1 / 2, 0), (0, 0), (1 / 2, 0)] = PolyQC.toPoly [(0, 0), (0, 0), (1, 0)] := by
  have h : ChebQC.ofMonomials [(0, 0), (0, 0), (1, 0)] = [(1 / 2, 0), (0, 0), (1 / 2, 0)] := by
    decide +kernel
  rw [← h]
  exact ChebQC.toPoly_ofMonomials _

/-- The sup-norm bound with a computable right-hand side. -/
example : supNorm (ChebQC.toPoly (ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0)])) ≤
    ((ChebQC.l1Bound (ChebQC.ofMonomials [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0)]) : ℚ) : ℝ) :=
  ChebQC.supNorm_toPoly_le_l1Bound _

/-- The `ChebSeries` of a concrete list has the expected coefficients. -/
example : (ChebQC.toSeries [(1 / 2, 0), (0, 0), (1 / 2, 0)]).coeff 2 = QC.toC (1 / 2, 0) :=
  ChebQC.coeff_toSeries _ 2

/-! ### Axiom audit -/

/-- info: 'QSVT.Poly.ChebQC.toPoly_ofMonomials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.ChebQC.toPoly_ofMonomials

/-- info: 'QSVT.Poly.ChebQC.toSeries_toPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.ChebQC.toSeries_toPoly

/-- info: 'QSVT.Poly.ChebQC.l1_le_l1Bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.ChebQC.l1_le_l1Bound

/-- info: 'QSVT.Poly.ChebQC.supNorm_toPoly_le_l1Bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.ChebQC.supNorm_toPoly_le_l1Bound
