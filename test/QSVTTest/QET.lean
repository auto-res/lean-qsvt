/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.QET

/-!
# QSVTTest.QET

Regression tests for the QET theorem of SVT-3 (`QSVT.SVT.QET`): statement-level instances of
`qet` for a single phase, the Chebyshev identity in low degree, and the axiom audit.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- QET for a single phase: `Π e^{iφ(2Π-I)} U Π = P_[φ](A) Π`. -/
example (E : HermitianEncoding ℋ) (φ : ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding [φ] * E.P =
      Polynomial.aeval E.encoded (qspPoly [φ]).1 * E.P :=
  qet E [φ]

/-- QET, vector form, for a single phase. -/
example (E : HermitianEncoding ℋ) (φ : ℝ) (x : ℋ) :
    E.P (altSeq E.toProjUnitaryEncoding [φ] (E.P x)) =
      Polynomial.aeval E.encoded (qspPoly [φ]).1 (E.P x) :=
  qet_apply E [φ] x

/-- The Chebyshev instance for `d = 0`: `Π Π = 1(A) Π = Π`. -/
example (E : HermitianEncoding ℋ) :
    E.P * altSeq E.toProjUnitaryEncoding (chebPhases 0) * E.P =
      Polynomial.aeval E.encoded (Polynomial.Chebyshev.T ℂ 0) * E.P :=
  qet_chebyshev E 0

/-- `P_{chebPhases 1} = T_1 = X`. -/
example : (qspPoly (chebPhases 1)).1 = Polynomial.X := by
  rw [qspPoly_chebPhases]
  simp

/-- `P_{chebPhases 2} = T_2 = 2X² - 1`. -/
example : (qspPoly (chebPhases 2)).1 = 2 * Polynomial.X ^ 2 - 1 := by
  rw [qspPoly_chebPhases]
  simp [Polynomial.Chebyshev.T_two]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.qet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qet

/-- info: 'QSVT.SVT.qet_chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qet_chebyshev

/-- info: 'QSVT.SVT.qspPoly_chebPhases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qspPoly_chebPhases
