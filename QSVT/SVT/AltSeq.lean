/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Projected
import QSVT.SVT.PhaseOp

/-!
# Alternating phase modulation sequences (formal-spec SVT-1)

GSLW Def 15: for a projected unitary encoding `(U, Π, Π̃)` and phases `Φ = (φ₁, …, φ_n)`,
```
U_Φ = e^{iφ₁(2Π̃−I)} U ∏_{j=1}^{(n−1)/2} ( e^{iφ_{2j}(2Π−I)} U† e^{iφ_{2j+1}(2Π̃−I)} U )   (n odd)
U_Φ = ∏_{j=1}^{n/2} ( e^{iφ_{2j−1}(2Π−I)} U† e^{iφ_{2j}(2Π̃−I)} U )                     (n even)
```
`altSeq E Φ` defines `U_Φ` by peeling phases off the front of the list: if the remaining list
has even length the next factor is `e^{iφ(2Π̃−I)} U`, otherwise `e^{iφ(2Π−I)} U†`. The
lemmas `altSeq_one`, `altSeq_two`, `altSeq_three` check the shapes of Def 15 for `n = 1, 2, 3`,
and `altSeq_mem_unitary` is the unitarity of `U_Φ`.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- SVT-1. The alternating phase modulation sequence `U_Φ` of GSLW Def 15, by recursion on
the phase list: `altSeq E (φ :: Φ) = (e^{iφ(2Π̃−I)} U or e^{iφ(2Π−I)} U†) * altSeq E Φ`, the
first alternative being taken when `Φ` has even length. -/
noncomputable def altSeq (E : ProjUnitaryEncoding ℋ) : List ℝ → L ℋ
  | [] => 1
  | φ :: Φ => (if Even Φ.length then phaseOp E.P' φ * E.U else phaseOp E.P φ * E.U†) * altSeq E Φ

variable (E : ProjUnitaryEncoding ℋ)

@[simp] theorem altSeq_nil : altSeq E [] = 1 := rfl

@[simp] theorem altSeq_cons (φ : ℝ) (Φ : List ℝ) :
    altSeq E (φ :: Φ) =
      (if Even Φ.length then phaseOp E.P' φ * E.U else phaseOp E.P φ * E.U†) * altSeq E Φ := rfl

theorem altSeq_cons_of_even (φ : ℝ) {Φ : List ℝ} (h : Even Φ.length) :
    altSeq E (φ :: Φ) = phaseOp E.P' φ * E.U * altSeq E Φ := by
  rw [altSeq_cons, ite_eq_left h]

theorem altSeq_cons_of_odd (φ : ℝ) {Φ : List ℝ} (h : ¬ Even Φ.length) :
    altSeq E (φ :: Φ) = phaseOp E.P φ * E.U† * altSeq E Φ := by
  rw [altSeq_cons, ite_eq_right h]

/-- SVT-1. `U_Φ` is unitary (`altSeq_unitary` in the specification). -/
theorem altSeq_mem_unitary (Φ : List ℝ) : altSeq E Φ ∈ unitary (L ℋ) := by
  induction Φ with
  | nil => exact one_mem _
  | cons φ Φ ih =>
    rw [altSeq_cons]
    refine mul_mem ?_ ih
    split_ifs
    · exact mul_mem (phaseOp_mem_unitary E.hP' φ) E.hU
    · exact mul_mem (phaseOp_mem_unitary E.hP φ) E.U_adjoint_mem_unitary

/-- GSLW Def 15 for `n = 1`: `U_Φ = e^{iφ₁(2Π̃−I)} U`. -/
theorem altSeq_one (a : ℝ) : altSeq E [a] = phaseOp E.P' a * E.U := by
  simp

/-- GSLW Def 15 for `n = 2`: `U_Φ = e^{iφ₁(2Π−I)} U† e^{iφ₂(2Π̃−I)} U`. -/
theorem altSeq_two (a b : ℝ) :
    altSeq E [a, b] = phaseOp E.P a * E.U† * (phaseOp E.P' b * E.U) := by
  simp

/-- GSLW Def 15 for `n = 3`: `U_Φ = e^{iφ₁(2Π̃−I)} U (e^{iφ₂(2Π−I)} U† e^{iφ₃(2Π̃−I)} U)`. -/
theorem altSeq_three (a b c : ℝ) :
    altSeq E [a, b, c] =
      phaseOp E.P' a * E.U * (phaseOp E.P b * E.U† * (phaseOp E.P' c * E.U)) := by
  simp

end QSVT.SVT
