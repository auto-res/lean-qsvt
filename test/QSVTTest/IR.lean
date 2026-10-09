/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.IR.Sound
import QSVT.IR.Cost

/-!
# QSVTTest.IR

Regression tests for the abstract IR (IR-1 / IR-2, `QSVT.IR.*`): the spec of one QSVT step,
the soundness theorem instantiated on the demo program `chebLCU 0 [-3, 0, 4] oracle` (the
Chebyshev coefficients of `4x³ − 3x = −3 T₁ + 4 T₃`), the cost lemmas reducing to numerals, and
the axiom audit. Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.IR
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Specification polynomials -/

/-- One QSVT step on the oracle specifies `Re[P_Φ]` (GSLW Cor 18). -/
example (Φ : List ℝ) : spec (.qsvtReal Φ .oracle) = rePoly (qspPoly Φ).1 := by
  rw [spec_qsvtReal, normSpec_oracle, comp_X]

/-- The demo program: the Route A step with coefficients `(0, −3, 0, 4)`, i.e.
`−3 T₁ + 4 T₃ = 4x³ − 3x`, applied to the oracle. -/
def demoIR : Expr := .chebLCU 0 [-3, 0, 4] .oracle

/-- Its subnormalisation is `‖c‖₁ = 7`. -/
example : chebScale 0 [-3, 0, 4] = 7 := by
  norm_num [chebScale]

/-- The demo program is well scaled. -/
theorem demoIR_wellScaled : WellScaled demoIR := by
  refine ⟨?_, trivial⟩
  norm_num [chebScale]

/-- Its spec is `∑ₖ cₖ T_k` itself, since `spec oracle = X`. -/
example : spec demoIR = chebPoly 0 [-3, 0, 4] := by
  rw [demoIR, spec_chebLCU, normSpec_oracle, comp_X]

/-- The denotation of the demo lives on the register `Reg 4 ℋ`. -/
example : space ℋ demoIR = Reg 4 ℋ := rfl

/-! ### Soundness instantiated on the demo -/

/-- IR-1 on the demo: the base block is `‖c‖₁⁻¹ • (−3 T₁ + 4 T₃)(A₀) Π`. -/
example (E₀ : HermitianEncoding ℋ) :
    base E₀ demoIR =
      ((chebScale 0 [-3, 0, 4] : ℂ)⁻¹) • (aeval E₀.encoded (chebPoly 0 [-3, 0, 4]) * E₀.P) := by
  rw [base_eq_smul E₀ demoIR_wellScaled, demoIR, scale_chebLCU, spec_chebLCU, normSpec_oracle,
    comp_X]

/-- IR-1 on a two-step program: a QSVT step after the demo step composes the polynomials. -/
example (E₀ : HermitianEncoding ℋ) (Φ : List ℝ) :
    base E₀ (.qsvtReal Φ demoIR) =
      aeval E₀.encoded ((rePoly (qspPoly Φ).1).comp (normSpec demoIR)) * E₀.P := by
  rw [base_eq E₀ ((wellScaled_qsvtReal Φ demoIR).mpr demoIR_wellScaled), normSpec_qsvtReal]

/-- The projector of the denotation of the demo is `|0⟩⟨0| ⊗ Π`. -/
example (E₀ : HermitianEncoding ℋ) : (denote E₀ demoIR).P = atZero E₀.P :=
  denote_P E₀ demoIR

/-! ### Resource count (IR-2) -/

/-- Three phases: three queries. -/
example (a b c : ℝ) : queries (.qsvtReal [a, b, c] .oracle) = 3 := by simp

/-- The demo uses `0 + 1 + 2 + 3 = 6` queries. -/
example : queries demoIR = 6 := by simp [demoIR, Finset.sum_range_succ]

#guard queries demoIR = 6

/-- Costs multiply along the program. -/
example (a b : ℝ) : queries (.qsvtReal [a, b] demoIR) = 12 := by
  simp [demoIR, Finset.sum_range_succ]

/-- The closed form of the `chebLCU` factor on the demo: `4 · 3 / 2 = 6`. -/
example : queries demoIR = 4 * 3 / 2 * 1 := queries_chebLCU_eq 0 [-3, 0, 4] .oracle

/-- Ancilla dimensions: `4` for the demo register, `×2` per QSVT step. -/
example (Φ : List ℝ) : ancillaDim (.qsvtReal Φ demoIR) = 8 := by simp [demoIR]

#guard ancillaDim demoIR = 4

/-- The degree bound on the demo: `deg (spec demoIR) ≤ 6`. -/
example : (spec demoIR).natDegree ≤ 6 := by
  have h := natDegree_spec_le demoIR
  rwa [show queries demoIR = 6 by simp [demoIR, Finset.sum_range_succ]] at h

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.IR.compress_aeval_mul_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.compress_aeval_mul_P

/-- info: 'QSVT.IR.base_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.base_eq

/-- info: 'QSVT.IR.base_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.base_eq_smul

/-- info: 'QSVT.IR.denote_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.denote_P

/-- info: 'QSVT.IR.chebEnc0_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.chebEnc0_encoded

/-- info: 'QSVT.IR.natDegree_spec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.natDegree_spec_le

/-- info: 'QSVT.IR.finrank_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.finrank_space

/-- info: 'QSVT.IR.queries_chebLCU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.IR.queries_chebLCU
