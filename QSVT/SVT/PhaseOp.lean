/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic

/-!
# Projector-controlled phase operators (formal-spec SVT-2)

For an orthogonal projection `Π` and a phase `φ`, the operator
`e^{iφ(2Π − I)} = e^{iφ} Π + e^{−iφ} (1 − Π)` (GSLW Def 15, Lemma 12) is defined here
without any operator exponential, as `phaseOp Π φ`.

Main lemmas (all under `hP : IsProjective P`): `phaseOp_zero`, `phaseOp_mul_proj`,
`proj_mul_phaseOp`, `phaseOp_comm_proj`, the group law `phaseOp_mul_phaseOp`,
`phaseOp_adjoint` and unitarity `phaseOp_mem_unitary`.
-/

namespace QSVT.SVT

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- SVT-2. The phase operator `e^{iφ(2Π − I)} = e^{iφ} Π + e^{−iφ} (1 − Π)` controlled by the
projection `Π` (here `P`). -/
noncomputable def phaseOp (P : L ℋ) (φ : ℝ) : L ℋ :=
  Complex.exp (Complex.I * φ) • P + Complex.exp (-(Complex.I * φ)) • (1 - P)

/-- `e^{i·0(2Π − I)} = 1`. -/
@[simp] theorem phaseOp_zero (P : L ℋ) : phaseOp P 0 = 1 := by
  simp [phaseOp]

variable {P : L ℋ}

/-- `e^{iφ(2Π − I)} Π = e^{iφ} Π`. -/
theorem phaseOp_mul_proj (hP : IsProjective P) (φ : ℝ) :
    phaseOp P φ * P = Complex.exp (Complex.I * φ) • P := by
  simp only [phaseOp, add_mul, smul_mul_assoc, hP.mul_self, hP.one_sub_mul, smul_zero, add_zero]

/-- `Π e^{iφ(2Π − I)} = e^{iφ} Π`. -/
theorem proj_mul_phaseOp (hP : IsProjective P) (φ : ℝ) :
    P * phaseOp P φ = Complex.exp (Complex.I * φ) • P := by
  simp only [phaseOp, mul_add, mul_smul_comm, hP.mul_self, hP.mul_one_sub, smul_zero, add_zero]

/-- `e^{iφ(2Π − I)} (1 − Π) = e^{−iφ} (1 − Π)`. -/
theorem phaseOp_mul_one_sub_proj (hP : IsProjective P) (φ : ℝ) :
    phaseOp P φ * (1 - P) = Complex.exp (-(Complex.I * φ)) • (1 - P) := by
  simp only [phaseOp, add_mul, smul_mul_assoc, hP.mul_one_sub, hP.one_sub.mul_self, smul_zero,
    zero_add]

/-- `(1 − Π) e^{iφ(2Π − I)} = e^{−iφ} (1 − Π)`. -/
theorem one_sub_proj_mul_phaseOp (hP : IsProjective P) (φ : ℝ) :
    (1 - P) * phaseOp P φ = Complex.exp (-(Complex.I * φ)) • (1 - P) := by
  simp only [phaseOp, mul_add, mul_smul_comm, hP.one_sub_mul, hP.one_sub.mul_self, smul_zero,
    zero_add]

/-- `e^{iφ(2Π − I)}` commutes with `Π`. -/
theorem phaseOp_comm_proj (hP : IsProjective P) (φ : ℝ) :
    phaseOp P φ * P = P * phaseOp P φ := by
  rw [phaseOp_mul_proj hP, proj_mul_phaseOp hP]

/-- Group law: `e^{iφ(2Π − I)} e^{iψ(2Π − I)} = e^{i(φ+ψ)(2Π − I)}`. -/
theorem phaseOp_mul_phaseOp (hP : IsProjective P) (φ ψ : ℝ) :
    phaseOp P φ * phaseOp P ψ = phaseOp P (φ + ψ) := by
  have e1 : Complex.I * ((φ + ψ : ℝ) : ℂ) = Complex.I * φ + Complex.I * ψ := by
    push_cast; ring
  simp only [phaseOp, e1, neg_add, Complex.exp_add, add_mul, mul_add, smul_mul_smul_comm,
    hP.mul_self, hP.mul_one_sub, hP.one_sub_mul, hP.one_sub.mul_self, smul_zero, add_zero,
    zero_add]

/-- `(e^{iφ(2Π − I)})† = e^{−iφ(2Π − I)}`. -/
theorem phaseOp_adjoint (hP : IsProjective P) (φ : ℝ) : (phaseOp P φ)† = phaseOp P (-φ) := by
  have e1 : Complex.I * ((-φ : ℝ) : ℂ) = -(Complex.I * φ) := by push_cast; ring
  have hc : star (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul]
  have hc' : star (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I,
      Complex.conj_ofReal, neg_mul, neg_neg]
  rw [← LinearMap.star_eq_adjoint]
  simp only [phaseOp, star_add, star_smul, star_sub, star_one, hP.isSelfAdjoint.star_eq, hc, hc',
    e1, neg_neg]

/-- `(e^{iφ(2Π − I)})† e^{iφ(2Π − I)} = 1`. -/
theorem phaseOp_adjoint_mul_phaseOp (hP : IsProjective P) (φ : ℝ) :
    (phaseOp P φ)† * phaseOp P φ = 1 := by
  rw [phaseOp_adjoint hP, phaseOp_mul_phaseOp hP, neg_add_cancel, phaseOp_zero]

/-- `e^{iφ(2Π − I)} (e^{iφ(2Π − I)})† = 1`. -/
theorem phaseOp_mul_phaseOp_adjoint (hP : IsProjective P) (φ : ℝ) :
    phaseOp P φ * (phaseOp P φ)† = 1 := by
  rw [phaseOp_adjoint hP, phaseOp_mul_phaseOp hP, add_neg_cancel, phaseOp_zero]

/-- SVT-2. `e^{iφ(2Π − I)}` is unitary. -/
theorem phaseOp_mem_unitary (hP : IsProjective P) (φ : ℝ) : phaseOp P φ ∈ unitary (L ℋ) :=
  Unitary.mem_iff.mpr ⟨phaseOp_adjoint_mul_phaseOp hP φ, phaseOp_mul_phaseOp_adjoint hP φ⟩

end QSVT.SVT
