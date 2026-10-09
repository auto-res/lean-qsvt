/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.FixedPointAA

/-!
# QSVTTest.FixedPointAA

Regression tests for the singular-pair two-frame lemma (SVT-7, `QSVT.SVT.SingularPair`), the
general Cor 18 (SVT-8, `QSVT.SVT.RealPolyGeneral`) and the fixed-point amplitude amplification
example (APP-1, `QSVT.Examples.FixedPointAA`): the headline statements instantiated, the resource
count (`21` queries, one ancilla qubit), the numerical margins, and the axiom audit (kernel trust
only). Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Certificate QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### SVT-7 on an arbitrary singular pair -/

/-- The basis vectors of SVT-6 are singular pairs, with the same left singular vectors. -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) : IsSingularPair E (rv E i) (σ E i) :=
  isSingularPair_rv E i
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) : lvOf E (rv E i) (σ E i) = lv E i :=
  lvOf_rv E i

/-- GSLW Thm 17 on one singular vector, odd case: `Π̃ U_Φ ψ = P_Φ(σ) ψ̃`. -/
example (E : ProjUnitaryEncoding ℋ) {ψ : ℋ} {σ : ℝ} (h : IsSingularPair E ψ σ) {Φ : List ℝ}
    (hodd : Odd Φ.length) :
    E.P' (altSeq E Φ ψ) = ((qspPoly Φ).1.eval (σ : ℂ)) • lvOf E ψ σ :=
  proj_altSeq_apply_singular_odd h hodd

/-- GSLW Thm 17 on one singular vector, even case: `Π U_Φ ψ = P_Φ(σ) ψ`. -/
example (E : ProjUnitaryEncoding ℋ) {ψ : ℋ} {σ : ℝ} (h : IsSingularPair E ψ σ) {Φ : List ℝ}
    (heven : Even Φ.length) :
    E.P (altSeq E Φ ψ) = ((qspPoly Φ).1.eval (σ : ℂ)) • ψ :=
  proj_altSeq_apply_singular_even h heven

/-- The defining relations of a singular pair. -/
example (E : ProjUnitaryEncoding ℋ) {ψ : ℋ} {σ : ℝ} (h : IsSingularPair E ψ σ) :
    E.encoded ψ = (σ : ℂ) • lvOf E ψ σ ∧ (E.encoded†) (lvOf E ψ σ) = (σ : ℂ) • ψ :=
  ⟨h.A_apply, h.A_adjoint_lvOf⟩

/-! ### SVT-8: the general Cor 18 -/

/-- `(|0⟩⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ Re[P_Φ]^{(SV)}(A)` for odd `Φ`. -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (hodd : Odd Φ.length) :
    blockDiag E.P' 0 * lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) * blockDiag E.P 0 =
      blockDiag (svTransform (rePoly (qspPoly Φ).1) E) 0 :=
  qsvt_real_odd E hodd

/-- The packaged encoding on `Anc ℋ` encodes `|0⟩⟨0| ⊗ Re[P_Φ]^{(SV)}(A)`. -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (hodd : Odd Φ.length) :
    (E.qsvtReal Φ).encoded = blockDiag (svTransform (rePoly (qspPoly Φ).1) E) 0 :=
  qsvtReal_encoded_odd E hodd

/-! ### APP-1: fixed-point amplitude amplification -/

section AA

variable {U : L ℋ} {G : L ℋ} {ψ₀ ψG : ℋ} {a : ℝ} (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G)
  (hψ₀ : ‖ψ₀‖ = 1) (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG)

/-- `(ψ₀, a)` is a singular pair of the amplitude-amplification encoding. -/
example : IsSingularPair (aaEncoding hU hG hψ₀) ψ₀ a := aa_isSingularPair hU hG hψ₀ hψG ha0 hGU

/-- Exact action: the output in the good subspace is `Re[P_Φ̃](a) ψ_G`. -/
example :
    topLeft (blockDiag G 0 * aaCircuit hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ =
      ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (a : ℂ)) • ψG :=
  fixedPointAA_apply hU hG hψ₀ hψG ha0 hGU

/-- Fixed-point property: amplitude `≈ 0.8924` for every `a ≥ 0.15`. -/
example (ha : 0.15 ≤ a) :
    ‖topLeft (blockDiag G 0 * aaCircuit hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ -
        (sign21Scale : ℂ) • ψG‖ ≤ sign21Eps + 0.0236 :=
  fixedPointAA_bound hU hG hψ₀ hψG ha0 hGU ha

/-- Success amplitude at least `0.869` after one run. -/
example (ha : 0.15 ≤ a) : 0.869 ≤ ‖blockDiag G 0 (aaCircuit hU hG hψ₀ (inl ψ₀))‖ :=
  fixedPointAA_amplitude hU hG hψ₀ hψG ha0 hGU ha

/-- The circuit is the compiled gate list. -/
example :
    aaCircuit hU hG hψ₀ =
      QSVT.Circuit.denote (aaEncoding hU hG hψ₀)
        (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) :=
  aaCircuit_eq_denote hU hG hψ₀

end AA

/-! ### Numerical margins -/

/-- The plateau value exceeds the certified lower bound by the ripple. -/
example : (0.869 : ℝ) + 0.0236 ≤ (sign21Scale : ℝ) + 0.0004 := by
  rw [sign21Scale]; norm_num

/-- The success probability bound `0.869² > 0.75`. -/
example : (0.75 : ℝ) < 0.869 ^ 2 := by norm_num

/-- Resources: `21` queries, `86` gates. -/
example : QSVT.Circuit.oracleCount (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 :=
  aaCircuit_oracleCount
example : (QSVT.Circuit.compileQsvtReal (sign21Phases.map (↑))).length = 86 := aaCircuit_length

/-! ### Axiom audit: kernel trust only -/

/-- info: 'QSVT.SVT.proj_altSeq_apply_singular_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proj_altSeq_apply_singular_odd

/-- info: 'QSVT.SVT.qsvt_real_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qsvt_real_odd

/-- info: 'QSVT.SVT.topLeft_qsvt_real_apply_singular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms topLeft_qsvt_real_apply_singular

/-- info: 'QSVT.Examples.fixedPointAA_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAA_apply

/-- info: 'QSVT.Examples.fixedPointAA_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAA_bound

/-- info: 'QSVT.Examples.fixedPointAA_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAA_amplitude

/-- info: 'QSVT.Examples.aaCircuit_eq_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aaCircuit_eq_denote
