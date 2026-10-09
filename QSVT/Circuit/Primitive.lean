/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Circuit.Gadget

/-!
# Primitive gates, their denotation and resource counts (formal-spec CIRC-1, CIRC-2, IR-2)

This module gives the one-ancilla circuit layer in the direct-sum model of
`QSVT.Encoding.Ancilla`: a primitive gate (`Prim`) is one of the oracle `I ⊗ U`, its adjoint,
the controlled NOTs `C_Π NOT`, `C_Π̃ NOT` of `QSVT.Circuit.Gadget`, the ancilla phase
`e^{iφ Z} ⊗ I` and the ancilla Hadamard `H ⊗ I`; a circuit is a list of primitives
(`Circuit`), denoted by the product of the gates in list order (`Circuit.denote`, leftmost
gate = leftmost factor, i.e. the last gate applied to a state).

In the direct-sum model `cpiNot 1` is the plain ancilla `X`; mapping `Anc`/`Reg` to qubit tensor
products and `cpiNot` to multi-controlled NOTs (CIRC-5) is deferred to the qubit circuit layer.

## Contents

* `Prim`, `Circuit`, `Prim.denote`, `Circuit.denote` with `denote_nil`, `denote_cons`,
  `denote_append`, `denote_singleton`, and unitarity `Prim.denote_mem_unitary`,
  `Circuit.denote_mem_unitary` (CIRC-1, CIRC-2).
* Counters `oracleCount`, `cpiNotCount`, `phaseCount`, `hadCount` with their `_append` lemmas
  (IR-2).
* Compilation of SVT-1/SVT-8 into gate lists: `compileGadget`, `compileAltSeq`,
  `compileQsvtReal`, with correctness `denote_compileAltSeq : denote E (compileAltSeq Φ) =
  gadgetSeq E Φ` and `denote_compileQsvtReal : denote E (compileQsvtReal Φ) = (E.qsvtReal Φ).U`.
* GSLW Lemma 19 resource counts: `compileAltSeq Φ` uses `Φ.length` oracle calls,
  `2 * Φ.length` controlled NOTs, `Φ.length` ancilla phases, and `compileQsvtReal Φ` adds two
  Hadamards (`oracleCount_compileAltSeq`, `cpiNotCount_compileAltSeq`,
  `phaseCount_compileAltSeq`, `hadCount_compileQsvtReal`, `length_compileAltSeq`, ...).

## Design notes

`Prim` carries a real phase, so it has no computable `DecidableEq`/`Repr`; the counters are
therefore defined with `List.countP` and Boolean predicates on `Prim`. The type is declared as
`QSVT.Circuit` (type and namespace share the name, as `Polynomial` does in Mathlib) because the
Mathlib `dupNamespace` linter rejects `QSVT.Circuit.Circuit`.
-/

namespace QSVT.Circuit

open QuantumState QSVT.Encoding QSVT.SVT

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- CIRC-1. Primitive gates on `Anc ℋ` relative to an oracle encoding `E = (U, Π, Π̃)`. -/
inductive Prim
  /-- The oracle `I ⊗ U`. -/
  | oracle
  /-- The inverse oracle `I ⊗ U†`. -/
  | oracleAdj
  /-- The controlled NOT `C_Π NOT` for the input projection `Π` (`E.P`). -/
  | cpiNotP
  /-- The controlled NOT `C_Π̃ NOT` for the output projection `Π̃` (`E.P'`). -/
  | cpiNotP'
  /-- The ancilla phase `e^{iφ Z} ⊗ I`. -/
  | ancPhase (φ : ℝ)
  /-- The ancilla Hadamard `H ⊗ I`. -/
  | hadA

namespace Prim

/-- CIRC-1. Denotation of a primitive gate as an operator on `Anc ℋ`. -/
noncomputable def denote (E : ProjUnitaryEncoding ℋ) : Prim → L (Anc ℋ)
  | oracle => liftU E.U
  | oracleAdj => liftU (E.U†)
  | cpiNotP => cpiNot E.P
  | cpiNotP' => cpiNot E.P'
  | ancPhase φ => QSVT.Encoding.ancPhase φ
  | hadA => QSVT.Encoding.hadA

variable (E : ProjUnitaryEncoding ℋ)

@[simp] theorem denote_oracle : denote E oracle = liftU E.U := rfl

@[simp] theorem denote_oracleAdj : denote E oracleAdj = liftU (E.U†) := rfl

@[simp] theorem denote_cpiNotP : denote E cpiNotP = cpiNot E.P := rfl

/-- Denotation of the `C_Π̃ NOT` primitive. -/
@[simp] theorem denote_cpiNotP' : denote E cpiNotP' = cpiNot E.P' := rfl

@[simp] theorem denote_ancPhase (φ : ℝ) : denote E (ancPhase φ) = QSVT.Encoding.ancPhase φ := rfl

@[simp] theorem denote_hadA : denote E hadA = QSVT.Encoding.hadA := rfl

/-- CIRC-2. Every primitive gate is unitary. -/
theorem denote_mem_unitary (p : Prim) : denote E p ∈ unitary (L (Anc ℋ)) := by
  cases p with
  | oracle => exact liftU_mem_unitary E.hU
  | oracleAdj => exact liftU_mem_unitary E.U_adjoint_mem_unitary
  | cpiNotP => exact cpiNot_mem_unitary E.hP
  | cpiNotP' => exact cpiNot_mem_unitary E.hP'
  | ancPhase φ => exact ancPhase_mem_unitary φ
  | hadA => exact hadA_mem_unitary

/-! ### Boolean classifiers (for the resource counters of IR-2) -/

/-- IR-2. Is the gate an oracle call (`oracle` or `oracleAdj`)? -/
def isOracle : Prim → Bool
  | oracle => true
  | oracleAdj => true
  | cpiNotP => false
  | cpiNotP' => false
  | ancPhase _ => false
  | hadA => false

/-- IR-2. Is the gate a controlled NOT (`cpiNotP` or `cpiNotP'`)? -/
def isCpiNot : Prim → Bool
  | oracle => false
  | oracleAdj => false
  | cpiNotP => true
  | cpiNotP' => true
  | ancPhase _ => false
  | hadA => false

/-- IR-2. Is the gate an ancilla phase? -/
def isPhase : Prim → Bool
  | oracle => false
  | oracleAdj => false
  | cpiNotP => false
  | cpiNotP' => false
  | ancPhase _ => true
  | hadA => false

/-- IR-2. Is the gate the ancilla Hadamard? -/
def isHad : Prim → Bool
  | oracle => false
  | oracleAdj => false
  | cpiNotP => false
  | cpiNotP' => false
  | ancPhase _ => false
  | hadA => true

/-- CIRC-3. The controlled NOT for `Π̃` (`true`) or for `Π` (`false`). -/
def cpiNotOf : Bool → Prim
  | true => cpiNotP'
  | false => cpiNotP

@[simp] theorem cpiNotOf_true : cpiNotOf true = cpiNotP' := rfl

@[simp] theorem cpiNotOf_false : cpiNotOf false = cpiNotP := rfl

end Prim

end QSVT.Circuit

/-- CIRC-1. A circuit on `Anc ℋ` is a list of primitive gates, read as a product in list order:
the leftmost gate is the leftmost factor of `Circuit.denote` (the gate applied last). -/
abbrev QSVT.Circuit := List QSVT.Circuit.Prim

namespace QSVT.Circuit

open QuantumState QSVT.Encoding QSVT.SVT

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Denotation -/

/-- CIRC-2. Denotation of a circuit: the product of the denotations of its gates in list order
(leftmost gate = leftmost factor). -/
noncomputable def denote (E : ProjUnitaryEncoding ℋ) (c : Circuit) : L (Anc ℋ) :=
  (c.map (Prim.denote E)).prod

variable (E : ProjUnitaryEncoding ℋ)

@[simp] theorem denote_nil : denote E [] = 1 := rfl

@[simp] theorem denote_cons (p : Prim) (c : Circuit) :
    denote E (p :: c) = Prim.denote E p * denote E c := by
  rw [denote, denote, List.map_cons, List.prod_cons]

@[simp] theorem denote_singleton (p : Prim) : denote E [p] = Prim.denote E p := by
  rw [denote_cons, denote_nil, mul_one]

/-- CIRC-2. Concatenation of circuits is multiplication of their denotations. -/
theorem denote_append (c₁ c₂ : Circuit) : denote E (c₁ ++ c₂) = denote E c₁ * denote E c₂ := by
  simp only [denote, List.map_append, List.prod_append]

/-- CIRC-2. Every circuit denotes a unitary. -/
theorem denote_mem_unitary (c : Circuit) : denote E c ∈ unitary (L (Anc ℋ)) := by
  induction c with
  | nil => rw [denote_nil]; exact one_mem _
  | cons p c ih => rw [denote_cons]; exact mul_mem (Prim.denote_mem_unitary E p) ih

/-! ### Resource counters (IR-2) -/

/-- IR-2. Number of oracle calls (`oracle` and `oracleAdj`) in a circuit. -/
def oracleCount (c : Circuit) : ℕ := c.countP Prim.isOracle

/-- IR-2. Number of controlled NOTs (`cpiNotP` and `cpiNotP'`) in a circuit. -/
def cpiNotCount (c : Circuit) : ℕ := c.countP Prim.isCpiNot

/-- IR-2. Number of ancilla phase gates in a circuit. -/
def phaseCount (c : Circuit) : ℕ := c.countP Prim.isPhase

/-- IR-2. Number of ancilla Hadamards in a circuit. -/
def hadCount (c : Circuit) : ℕ := c.countP Prim.isHad

theorem oracleCount_append (c₁ c₂ : Circuit) :
    oracleCount (c₁ ++ c₂) = oracleCount c₁ + oracleCount c₂ := List.countP_append

theorem cpiNotCount_append (c₁ c₂ : Circuit) :
    cpiNotCount (c₁ ++ c₂) = cpiNotCount c₁ + cpiNotCount c₂ := List.countP_append

theorem phaseCount_append (c₁ c₂ : Circuit) :
    phaseCount (c₁ ++ c₂) = phaseCount c₁ + phaseCount c₂ := List.countP_append

theorem hadCount_append (c₁ c₂ : Circuit) :
    hadCount (c₁ ++ c₂) = hadCount c₁ + hadCount c₂ := List.countP_append

/-! ### Compilation of the alternating sequence (CIRC-3) -/

/-- CIRC-3 (GSLW Fig. 1b). The gate list of the gadget `gadget P φ`: `C_Π NOT`,
`e^{−iφ Z} ⊗ I`, `C_Π NOT`, with `Π = Π̃` when `useP' = true` and `Π = Π` otherwise. -/
def compileGadget (useP' : Bool) (φ : ℝ) : Circuit :=
  [Prim.cpiNotOf useP', Prim.ancPhase (-φ), Prim.cpiNotOf useP']

/-- CIRC-3. The gate list of `gadgetSeq E Φ`, mirroring `altSeq`/`gadgetSeq`: for `φ :: Φ`,
the gadget for `Π̃` followed by the oracle when `Φ` has even length, otherwise the gadget for
`Π` followed by the inverse oracle, then the compilation of `Φ`. -/
def compileAltSeq : List ℝ → Circuit
  | [] => []
  | φ :: Φ =>
    (if Even Φ.length then compileGadget true φ ++ [Prim.oracle]
      else compileGadget false φ ++ [Prim.oracleAdj]) ++ compileAltSeq Φ

/-- CIRC-3 (GSLW Cor 18). The gate list of the unitary of `E.qsvtReal Φ`:
`(H ⊗ I) · gadgetSeq E Φ · (H ⊗ I)`. -/
def compileQsvtReal (Φ : List ℝ) : Circuit := [Prim.hadA] ++ compileAltSeq Φ ++ [Prim.hadA]

@[simp] theorem compileAltSeq_nil : compileAltSeq [] = [] := rfl

@[simp] theorem compileAltSeq_cons (φ : ℝ) (Φ : List ℝ) :
    compileAltSeq (φ :: Φ) =
      (if Even Φ.length then compileGadget true φ ++ [Prim.oracle]
        else compileGadget false φ ++ [Prim.oracleAdj]) ++ compileAltSeq Φ := rfl

/-! ### Correctness of the compilation -/

theorem denote_compileGadget_true (φ : ℝ) : denote E (compileGadget true φ) = gadget E.P' φ := by
  simp only [compileGadget, Prim.cpiNotOf_true, denote_cons, denote_nil, mul_one,
    Prim.denote_cpiNotP', Prim.denote_ancPhase, gadget, mul_assoc]

theorem denote_compileGadget_false (φ : ℝ) :
    denote E (compileGadget false φ) = gadget E.P φ := by
  simp only [compileGadget, Prim.cpiNotOf_false, denote_cons, denote_nil, mul_one,
    Prim.denote_cpiNotP, Prim.denote_ancPhase, gadget, mul_assoc]

/-- CIRC-3. The compiled alternating sequence denotes `gadgetSeq E Φ`. -/
theorem denote_compileAltSeq (Φ : List ℝ) : denote E (compileAltSeq Φ) = gadgetSeq E Φ := by
  induction Φ with
  | nil => rw [compileAltSeq_nil, denote_nil, gadgetSeq_nil]
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, gadgetSeq_cons, denote_append, ih]
    split_ifs
    · rw [denote_append, denote_compileGadget_true, denote_singleton, Prim.denote_oracle]
    · rw [denote_append, denote_compileGadget_false, denote_singleton, Prim.denote_oracleAdj]

/-- CIRC-3. The compiled alternating sequence denotes `|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ}`. -/
theorem denote_compileAltSeq_eq_blockDiag (Φ : List ℝ) :
    denote E (compileAltSeq Φ) = blockDiag (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) := by
  rw [denote_compileAltSeq, gadgetSeq_eq]

/-- CIRC-3 (GSLW Cor 18 as a gate list). The compiled circuit denotes the unitary of
`E.qsvtReal Φ`. -/
theorem denote_compileQsvtReal (E : HermitianEncoding ℋ) (Φ : List ℝ) :
    denote E.toProjUnitaryEncoding (compileQsvtReal Φ) = (E.qsvtReal Φ).U := by
  rw [qsvtReal_U_eq_gadget, compileQsvtReal, denote_append, denote_append, denote_compileAltSeq,
    denote_singleton, Prim.denote_hadA]

/-! ### Resource counts (GSLW Lemma 19, IR-2) -/

@[simp] theorem oracleCount_oracle : oracleCount [Prim.oracle] = 1 := rfl
@[simp] theorem oracleCount_oracleAdj : oracleCount [Prim.oracleAdj] = 1 := rfl
@[simp] theorem oracleCount_hadA : oracleCount [Prim.hadA] = 0 := rfl
@[simp] theorem cpiNotCount_oracle : cpiNotCount [Prim.oracle] = 0 := rfl
@[simp] theorem cpiNotCount_oracleAdj : cpiNotCount [Prim.oracleAdj] = 0 := rfl
@[simp] theorem cpiNotCount_hadA : cpiNotCount [Prim.hadA] = 0 := rfl
@[simp] theorem phaseCount_oracle : phaseCount [Prim.oracle] = 0 := rfl
@[simp] theorem phaseCount_oracleAdj : phaseCount [Prim.oracleAdj] = 0 := rfl
@[simp] theorem phaseCount_hadA : phaseCount [Prim.hadA] = 0 := rfl
@[simp] theorem hadCount_oracle : hadCount [Prim.oracle] = 0 := rfl
@[simp] theorem hadCount_oracleAdj : hadCount [Prim.oracleAdj] = 0 := rfl
@[simp] theorem hadCount_hadA : hadCount [Prim.hadA] = 1 := rfl

@[simp] theorem length_compileGadget (b : Bool) (φ : ℝ) : (compileGadget b φ).length = 3 := rfl

@[simp] theorem oracleCount_compileGadget (b : Bool) (φ : ℝ) :
    oracleCount (compileGadget b φ) = 0 := by
  cases b <;> rfl

@[simp] theorem cpiNotCount_compileGadget (b : Bool) (φ : ℝ) :
    cpiNotCount (compileGadget b φ) = 2 := by
  cases b <;> rfl

@[simp] theorem phaseCount_compileGadget (b : Bool) (φ : ℝ) :
    phaseCount (compileGadget b φ) = 1 := by
  cases b <;> rfl

@[simp] theorem hadCount_compileGadget (b : Bool) (φ : ℝ) :
    hadCount (compileGadget b φ) = 0 := by
  cases b <;> rfl

/-- IR-2 (GSLW Lemma 19). `compileAltSeq Φ` has `4 * Φ.length` gates. -/
theorem length_compileAltSeq (Φ : List ℝ) : (compileAltSeq Φ).length = 4 * Φ.length := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, List.length_append, ih, List.length_cons]
    split_ifs <;> rw [List.length_append, length_compileGadget, List.length_singleton] <;> omega

/-- IR-2 (GSLW Lemma 19). `compileAltSeq Φ` makes `Φ.length` oracle calls (`U` or `U†`). -/
theorem oracleCount_compileAltSeq (Φ : List ℝ) : oracleCount (compileAltSeq Φ) = Φ.length := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, oracleCount_append, ih, List.length_cons]
    split_ifs
    · rw [oracleCount_append, oracleCount_compileGadget, oracleCount_oracle]; omega
    · rw [oracleCount_append, oracleCount_compileGadget, oracleCount_oracleAdj]; omega

/-- IR-2 (GSLW Lemma 19). `compileAltSeq Φ` uses `2 * Φ.length` controlled NOTs. -/
theorem cpiNotCount_compileAltSeq (Φ : List ℝ) :
    cpiNotCount (compileAltSeq Φ) = 2 * Φ.length := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, cpiNotCount_append, ih, List.length_cons]
    split_ifs
    · rw [cpiNotCount_append, cpiNotCount_compileGadget, cpiNotCount_oracle]; omega
    · rw [cpiNotCount_append, cpiNotCount_compileGadget, cpiNotCount_oracleAdj]; omega

/-- IR-2 (GSLW Lemma 19). `compileAltSeq Φ` uses `Φ.length` ancilla phase gates. -/
theorem phaseCount_compileAltSeq (Φ : List ℝ) : phaseCount (compileAltSeq Φ) = Φ.length := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, phaseCount_append, ih, List.length_cons]
    split_ifs
    · rw [phaseCount_append, phaseCount_compileGadget, phaseCount_oracle]; omega
    · rw [phaseCount_append, phaseCount_compileGadget, phaseCount_oracleAdj]; omega

/-- IR-2. `compileAltSeq Φ` uses no Hadamard. -/
theorem hadCount_compileAltSeq (Φ : List ℝ) : hadCount (compileAltSeq Φ) = 0 := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    rw [compileAltSeq_cons, hadCount_append, ih]
    split_ifs
    · rw [hadCount_append, hadCount_compileGadget, hadCount_oracle]
    · rw [hadCount_append, hadCount_compileGadget, hadCount_oracleAdj]

/-- IR-2 (GSLW Lemma 19). `compileQsvtReal Φ` has `4 * Φ.length + 2` gates. -/
theorem length_compileQsvtReal (Φ : List ℝ) :
    (compileQsvtReal Φ).length = 4 * Φ.length + 2 := by
  rw [compileQsvtReal, List.length_append, List.length_append, length_compileAltSeq,
    List.length_singleton]
  omega

/-- IR-2 (GSLW Lemma 19 / Cor 18). `compileQsvtReal Φ` makes `Φ.length` oracle calls. -/
theorem oracleCount_compileQsvtReal (Φ : List ℝ) :
    oracleCount (compileQsvtReal Φ) = Φ.length := by
  rw [compileQsvtReal, oracleCount_append, oracleCount_append, oracleCount_compileAltSeq,
    oracleCount_hadA]
  omega

/-- IR-2 (GSLW Lemma 19 / Cor 18). `compileQsvtReal Φ` uses `2 * Φ.length` controlled NOTs. -/
theorem cpiNotCount_compileQsvtReal (Φ : List ℝ) :
    cpiNotCount (compileQsvtReal Φ) = 2 * Φ.length := by
  rw [compileQsvtReal, cpiNotCount_append, cpiNotCount_append, cpiNotCount_compileAltSeq,
    cpiNotCount_hadA]
  omega

/-- IR-2 (GSLW Lemma 19 / Cor 18). `compileQsvtReal Φ` uses `Φ.length` ancilla phases. -/
theorem phaseCount_compileQsvtReal (Φ : List ℝ) :
    phaseCount (compileQsvtReal Φ) = Φ.length := by
  rw [compileQsvtReal, phaseCount_append, phaseCount_append, phaseCount_compileAltSeq,
    phaseCount_hadA]
  omega

/-- IR-2 (GSLW Cor 18). `compileQsvtReal Φ` uses exactly two ancilla Hadamards. -/
theorem hadCount_compileQsvtReal (Φ : List ℝ) : hadCount (compileQsvtReal Φ) = 2 := by
  rw [compileQsvtReal, hadCount_append, hadCount_append, hadCount_compileAltSeq, hadCount_hadA]

end QSVT.Circuit
