/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.QSVT
import QSVT.SVT.QET
import QSVT.QSP.Endpoints

/-!
# QSVTTest.QSVT

Regression tests for SVT-6 (`QSVT.SVT.SVD`), the two-frame lemma (`QSVT.SVT.TwoFrame`) and
the QSVT theorem SVT-7 (`QSVT.SVT.QSVT`): statement-level instances of GSLW Thm 17 for a single
phase and for the empty phase list, the Hermitian specialisation against `qet`, the endpoint
behaviour `σ = 0` and `σ = 1`, and the axiom audit.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### SVT-6: singular vectors -/

/-- The defining relations of the singular pairs hold for every index. -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) :
    E.encoded (rv E i) = (σ E i : ℂ) • lv E i ∧ (E.encoded†) (lv E i) = (σ E i : ℂ) • rv E i :=
  ⟨A_rv E i, A_adjoint_lv E i⟩

/-- Singular values lie in `[0, 1]`. -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) : σ E i ∈ Set.Icc (0 : ℝ) 1 :=
  σ_mem_Icc E i

/-- `svTransform X E ψᵢ = σᵢ ψ̃ᵢ` (consistent with `svTransform_X : svTransform X E = A`). -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) :
    svTransform X E (rv E i) = (σ E i : ℂ) • lv E i := by
  have h := svTransform_apply_rv_of_isOdd E isOdd_X i
  rwa [eval_X] at h

/-- `svTransform 1 E ψᵢ = ψᵢ`. -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) : svTransform 1 E (rv E i) = rv E i := by
  have h := svTransform_apply_rv_of_isEven E isEven_one i
  rwa [eval_one, one_smul] at h

/-! ### SVT-7: the two-frame lemma at the endpoints -/

/-- `σ = 0`: the left singular vector is `0`, so `Π̃ U_Φ ψ = 0` for odd length. -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (hodd : Odd Φ.length) (i : svIndex E)
    (h : σ E i = 0) : E.P' (altSeq E Φ (rv E i)) = 0 := by
  rw [proj_altSeq_apply_rv_odd E hodd i, lv_of_σ_eq_zero E h, smul_zero]

/-- `σ = 0`, odd length: the scalar `(seqR Φ 0)₀₀ = P_Φ(0)` vanishes as well (QSP-5), so the
general formula `Π̃ U_Φ ψ = (seqR Φ σ)₀₀ ψ̃` is consistent with `ψ̃ = 0`. -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (hodd : Odd Φ.length) (i : svIndex E)
    (h : σ E i = 0) : (seqR Φ (σ E i)) 0 0 = 0 := by
  rw [h]
  exact seqR_zero_apply_of_odd hodd

/-- `σ = 0`, even length: `Π U_Φ ψ = e^{i alt Φ} ψ` (a pure phase, QSP-5). -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (heven : Even Φ.length) (i : svIndex E)
    (h : σ E i = 0) :
    E.P (altSeq E Φ (rv E i)) = Complex.exp (Complex.I * alt Φ) • rv E i := by
  rw [proj_altSeq_apply_rv_even E heven i, h, seqR_zero_apply_of_even heven]

/-- `σ = 1`: `U ψ = ψ̃` and `U† ψ̃ = ψ` exactly. -/
example (E : ProjUnitaryEncoding ℋ) (i : svIndex E) (h : σ E i = 1) :
    E.U (rv E i) = lv E i ∧ (E.U†) (lv E i) = rv E i :=
  ⟨U_rv_of_σ_eq_one E h, U_adjoint_lv_of_σ_eq_one E h⟩

/-- `σ = 1`, odd length: `Π̃ U_Φ ψ = (∏ e^{iφⱼ}) ψ̃` (QSP-5). -/
example (E : ProjUnitaryEncoding ℋ) {Φ : List ℝ} (hodd : Odd Φ.length) (i : svIndex E)
    (h : σ E i = 1) :
    E.P' (altSeq E Φ (rv E i)) =
      (Φ.map (fun φ => Complex.exp (Complex.I * φ))).prod • lv E i := by
  rw [proj_altSeq_apply_rv_odd E hodd i, h, seqR_one_apply]

/-! ### SVT-7: GSLW Thm 17 in small instances -/

/-- GSLW Thm 17 for a single phase, in `svTransform` form. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) :
    E.P' * altSeq E [φ] * E.P = svTransform (qspPoly [φ]).1 E :=
  qsvt_odd E odd_one

/-- GSLW Thm 17 for a single phase, evaluated: `Π̃ e^{iφ(2Π̃-I)} U Π = e^{iφ} A`. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) :
    E.P' * (phaseOp E.P' φ * E.U) * E.P = Complex.exp (Complex.I * φ) • E.encoded :=
  qsvt_single E φ

/-- The single-phase instance with `φ = 0`: `Π̃ U Π = A`. -/
example (E : ProjUnitaryEncoding ℋ) : E.P' * (phaseOp E.P' 0 * E.U) * E.P = E.encoded := by
  have h := qsvt_single E 0
  simpa using h

/-- GSLW Thm 17 for the empty phase list: `Π Π = svTransform 1 E = Π`. -/
example (E : ProjUnitaryEncoding ℋ) : E.P * altSeq E [] * E.P = E.P := by
  have h := qsvt_even E (Φ := []) ⟨0, rfl⟩
  rwa [qspPoly_nil, svTransform_one] at h

/-- The combined statement picks `Π̃` for odd length. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) :
    (if Even [φ].length then E.P else E.P') * altSeq E [φ] * E.P = svTransform (qspPoly [φ]).1 E :=
  qsvt E [φ]

/-- The trivial encoding of a unitary (`Π = Π̃ = 1`): `U_Φ = svTransform P_Φ (ofUnitary U)`. -/
example (U : L ℋ) (hU : U ∈ unitary (L ℋ)) {Φ : List ℝ} (hodd : Odd Φ.length) :
    altSeq (ProjUnitaryEncoding.ofUnitary U hU) Φ =
      svTransform (qspPoly Φ).1 (ProjUnitaryEncoding.ofUnitary U hU) := by
  have h := qsvt_odd (ProjUnitaryEncoding.ofUnitary U hU) hodd
  simpa [ProjUnitaryEncoding.ofUnitary] using h

/-! ### The Hermitian specialisation agrees with QET (SVT-3) -/

/-- For a Hermitian encoding, `qsvt_hermitian` followed by `svTransform_eq_aeval` proves exactly
the statement of `qet`. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding Φ * E.P =
      Polynomial.aeval E.encoded (qspPoly Φ).1 * E.P := by
  rw [qsvt_hermitian E Φ, svTransform_eq_aeval E]

/-- The same statement is `qet`; both proofs prove the same proposition. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding Φ * E.P =
      Polynomial.aeval E.encoded (qspPoly Φ).1 * E.P :=
  qet E Φ

/-- `qet_of_qsvt` and `qet` have the same type. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) : qet_of_qsvt E Φ = qet E Φ := rfl

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.qsvt_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qsvt_odd

/-- info: 'QSVT.SVT.qsvt_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qsvt_even

/-- info: 'QSVT.SVT.altSeq_apply_rv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.altSeq_apply_rv

/-- info: 'QSVT.SVT.qsvt_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qsvt_single

/-- info: 'QSVT.SVT.qet_of_qsvt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qet_of_qsvt

/-- info: 'QSVT.SVT.svTransform_apply_rv_of_isOdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.svTransform_apply_rv_of_isOdd
