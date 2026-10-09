/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.EigenBasis

/-!
# QSVTTest.EigenBasis

Regression tests for the eigenbasis infrastructure of SVT-3 (`QSVT.SVT.EigenBasis`).
Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- The eigenvectors lie in `ran Π` and are fixed by `Π`. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    E.P (eigenVec E i) = eigenVec E i :=
  P_eigenVec E i

/-- `A ψᵢ = ςᵢ ψᵢ`. -/
example (E : HermitianEncoding ℋ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    E.encoded (eigenVec E i) = (eigenValue E i : ℂ) • eigenVec E i :=
  encoded_eigenVec E i

/-- `p(A)` on an eigenvector is scalar multiplication by `p(ςᵢ)`. -/
example (E : HermitianEncoding ℋ) (p : Polynomial ℂ) (i : Fin (Module.finrank ℂ (rangeP E))) :
    Polynomial.aeval E.encoded p (eigenVec E i) = p.eval (eigenValue E i : ℂ) • eigenVec E i :=
  aeval_eigenVec E p i

/-- The extensionality principle specialised to `T = S`: trivially consistent. -/
example (E : HermitianEncoding ℋ) (T : L ℋ) : T * E.P = T * E.P :=
  ext_mul_P_of_eigenVec E fun _ => rfl

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.aeval_eigenVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.aeval_eigenVec

/-- info: 'QSVT.SVT.ext_of_eigenVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.ext_of_eigenVec

/-- info: 'QSVT.SVT.eigenValue_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.eigenValue_mem_Icc

/-- info: 'QSVT.SVT.encoded_eigenVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.encoded_eigenVec
