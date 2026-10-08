/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT
import QSVTTest.Structure
import QSVTTest.Chebyshev
import QSVTTest.Encoding
import QSVTTest.EigenBasis
import QSVTTest.Polynomial
import QSVTTest.TwoVector
import QSVTTest.QET
import QSVTTest.SVTransform
import QSVTTest.LCU
import QSVTTest.RealPoly
import QSVTTest.ChebCoeff
import QSVTTest.LCUm
import QSVTTest.ChebLCU
import QSVTTest.Conversion
import QSVTTest.Circuit
import QSVTTest.Existence
import QSVTTest.IR
import QSVTTest.Certificate
import QSVTTest.Examples
import QSVTTest.PhaseCheck
import QSVTTest.CosExample
import QSVTTest.Sign21RouteB
import QSVTTest.Qubit
import QSVTTest.Evolution
import QSVTTest.QubitCompile
import QSVTTest.QSVT
import QSVTTest.FixedPointAA
import QSVTTest.Lang
import QSVTTest.Inverse

/-!
# QSVTTest

Regression tests for `lean-qsvt`. Run with `lake test`.
Each check is a compile-time assertion (`#guard` / `example`), so a failing test
breaks the build of this library.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.QSP in
/-- `seqR` on the empty phase list is the identity. -/
example (x : ℝ) : seqR [] x = 1 := seqR_nil x

open QSVT.QSP in
/-- `phaseZ 0` is the identity. -/
example : phaseZ 0 = 1 := phaseZ_zero

#guard (List.range 4).map (fun k => k % 2 == 0) = [true, false, true, false]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.QSP.seqR_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_mem_unitaryGroup

/-- info: 'QSVT.Poly.evenPart_add_oddPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Poly.evenPart_add_oddPart
