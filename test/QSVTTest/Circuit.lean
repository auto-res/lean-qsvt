/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Circuit.Gadget
import QSVT.Circuit.Primitive

/-!
# QSVTTest.Circuit

Regression tests for the ancilla gadget of GSLW Lemma 19 (CIRC-3, `QSVT.Circuit.Gadget`) and
the primitive-gate circuit layer with its resource counts (CIRC-1/2, IR-2,
`QSVT.Circuit.Primitive`). Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT QSVT.Encoding QSVT.SVT QSVT.Circuit

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The gadget (CIRC-3) -/

/-- `C_I NOT` is the plain ancilla `X`. -/
example : cpiNot (1 : L ℋ) = block 0 1 1 0 := cpiNot_one

/-- The ancilla `X` squares to the identity. -/
example : cpiNot (1 : L ℋ) * cpiNot 1 = 1 := cpiNot_mul_cpiNot isProjective_one

/-- For the trivial projection the gadget is just the ancilla phase `e^{iφ Z} ⊗ I`. -/
example (φ : ℝ) : gadget (1 : L ℋ) φ = ancPhase φ := by
  rw [gadget_eq isProjective_one, ancPhase]
  simp [phaseOp]

/-- With the ancilla in `|0⟩` the gadget acts as `phaseOp P φ`. -/
example (P : L ℋ) (hP : IsProjective P) (φ : ℝ) : topLeft (gadget P φ) = phaseOp P φ :=
  topLeft_gadget hP φ

/-- The gadget sequence of a single phase. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) : gadgetSeq E [φ] = gadget E.P' φ * liftU E.U := by
  simp

/-- `gadgetSeq E [φ] = |0⟩⟨0| ⊗ e^{iφ(2Π̃−I)} U + |1⟩⟨1| ⊗ e^{−iφ(2Π̃−I)} U`. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) :
    gadgetSeq E [φ] = blockDiag (phaseOp E.P' φ * E.U) (phaseOp E.P' (-φ) * E.U) := by
  rw [gadgetSeq_eq]
  simp

/-- The SVT-8 unitary is a Hadamard-conjugated gadget sequence. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    (E.qsvtReal Φ).U = hadA * gadgetSeq E.toProjUnitaryEncoding Φ * hadA :=
  qsvtReal_U_eq_gadget E Φ

/-! ### Primitive circuits (CIRC-1/2) -/

/-- Concatenation is multiplication. -/
example (E : ProjUnitaryEncoding ℋ) (c₁ c₂ : Circuit) :
    denote E (c₁ ++ c₂) = denote E c₁ * denote E c₂ :=
  denote_append E c₁ c₂

/-- A compiled gadget denotes the gadget operator. -/
example (E : ProjUnitaryEncoding ℋ) (φ : ℝ) : denote E (compileGadget true φ) = gadget E.P' φ :=
  denote_compileGadget_true E φ

/-- The gate list of a single phase: `C_Π̃ NOT, e^{−iφ Z}, C_Π̃ NOT, U`. -/
example (φ : ℝ) :
    compileAltSeq [φ] = [Prim.cpiNotP', Prim.ancPhase (-φ), Prim.cpiNotP', Prim.oracle] := by
  simp [compileAltSeq, compileGadget]

/-- The gate list of two phases (GSLW Def 15, `n = 2`): the `Π`-gadget with `U†` first, then the
`Π̃`-gadget with `U`. -/
example (a b : ℝ) :
    compileAltSeq [a, b] =
      [Prim.cpiNotP, Prim.ancPhase (-a), Prim.cpiNotP, Prim.oracleAdj,
        Prim.cpiNotP', Prim.ancPhase (-b), Prim.cpiNotP', Prim.oracle] := by
  simp [compileAltSeq, compileGadget]

/-- CIRC-3 end-to-end: the compiled QSVT circuit denotes the SVT-8 unitary. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    denote E.toProjUnitaryEncoding (compileQsvtReal Φ) = (E.qsvtReal Φ).U :=
  denote_compileQsvtReal E Φ

/-! ### Resource counts (IR-2, GSLW Lemma 19) -/

example : (compileAltSeq [1, 2, 3]).length = 12 := length_compileAltSeq _

example : oracleCount (compileAltSeq [1, 2, 3]) = 3 := oracleCount_compileAltSeq _

example : cpiNotCount (compileAltSeq [1, 2, 3]) = 6 := cpiNotCount_compileAltSeq _

example : phaseCount (compileAltSeq [1, 2, 3]) = 3 := phaseCount_compileAltSeq _

example : (compileQsvtReal [1, 2, 3]).length = 14 := length_compileQsvtReal _

example : oracleCount (compileQsvtReal [1, 2, 3]) = 3 := oracleCount_compileQsvtReal _

example : hadCount (compileQsvtReal [1, 2, 3]) = 2 := hadCount_compileQsvtReal _

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.Circuit.gadget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.gadget_eq

/-- info: 'QSVT.Circuit.gadgetSeq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.gadgetSeq_eq

/-- info: 'QSVT.Circuit.qsvtReal_U_eq_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.qsvtReal_U_eq_gadget

/-- info: 'QSVT.Circuit.denote_compileQsvtReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.denote_compileQsvtReal

/-- info: 'QSVT.Circuit.denote_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.denote_mem_unitary

/-- info: 'QSVT.Circuit.oracleCount_compileAltSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.Circuit.oracleCount_compileAltSeq
