/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Qubit.Bridge
import QSVT.Circuit.Primitive

/-!
# Qubit-level compilation of QSVT circuits (formal-spec CIRC-4, CIRC-5)

The circuit layer `QSVT.Circuit.Primitive` describes a QSVT circuit as a list of primitive gates
on the direct-sum space `Anc ℋ` relative to an abstract oracle encoding `E = (U, Π, Π̃)`. When the
system is a qubit register `ℋ = Qubits n` and the projections are diagonal in the computational
basis (`Π = diagProj d`, `Π̃ = diagProj d'`), every primitive is a standard gate on the
`(n + 1)`-qubit register `Qubits (n + 1)` with the QSVT ancilla as qubit `0` (`QSVT.Qubit.Bridge`):

| primitive (`Prim`)  | qubit gate (`QGate n`)  | operator on `Qubits (n + 1)` |
|---------------------|-------------------------|------------------------------|
| `oracle`            | `oracle`                | `tensorId U = 1 ⊗ U`         |
| `oracleAdj`         | `oracleAdj`             | `tensorId (U†)`              |
| `cpiNotP`           | `ctrlX d`               | `ctrlX d` (multi-controlled `X` on qubit `0`) |
| `cpiNotP'`          | `ctrlX d'`              | `ctrlX d'`                   |
| `ancPhase φ`        | `rz φ`                  | `rz 0 φ = e^{iφ Z} ⊗ I`      |
| `hadA`              | `h`                     | `hadamard 0`                 |

`compileQ Q c` is this gate-by-gate translation (`List.map`), and its correctness is the
intertwining `liftAnc (Circuit.denote Q.toProj c) = QCircuit.denote Q (compileQ Q c)`
(`liftAnc_denote`): the qubit circuit is the direct-sum circuit transported along the canonical
isometry `ancEquiv n : Anc (Qubits n) ≃ₗᵢ[ℂ] Qubits (n + 1)`. Specialised to the Route B circuit
`compileQsvtReal Φ` of CIRC-3 this is `compileQ_qsvtReal`: the `(n + 1)`-qubit circuit implements
the unitary of `E.qsvtReal Φ` (SVT-8, GSLW Cor 18). The gate counts of IR-2 transport verbatim
(`length_compileQ`, `oracleCount_compileQ`, ...).

## Resource note (CIRC-5)

For the standard block-encoding projector `Π = |0…0⟩⟨0…0| ⊗ I = zeroProj a` the control predicate
is `zeroPattern a` (`b ↦ ∀ i < a, b i = false`), so `cpiNotP` compiles to one multi-controlled
`X` with `a` anti-controls (`ctrlX_zeroProj_eq`); its decomposition into `O(a)` Toffoli gates is
left to the OpenQASM back end (`QSVT.Qubit.Qasm`, untrusted) and is not formalised.

## Contents

* `QubitEncoding n` (`U`, `hU`, `d`, `d'`) with `QubitEncoding.toProj : ProjUnitaryEncoding
  (Qubits n)`, and `QubitHermitianEncoding n` with `toQubit`, `toHermitian :
  HermitianEncoding (Qubits n)`.
* `QGate n`, `QGate.denote`, `QGate.denote_mem_unitary`; `QCircuit n`, `QCircuit.denote` with
  `denote_nil`, `denote_cons`, `denote_singleton`, `denote_append`, `denote_mem_unitary`.
* `compilePrim`, `compileQ`, with `liftAnc_prim_denote`, `liftAnc_denote`, and the headline
  `compileQ_qsvtReal`.
* Counters `QCircuit.oracleCount`, `ctrlXCount`, `rzCount`, `hCount` with the transport lemmas
  `length_compileQ`, `oracleCount_compileQ`, `ctrlXCount_compileQ`, `rzCount_compileQ`,
  `hCount_compileQ`, and the Route B counts `oracleCount_compileQ_qsvtReal`,
  `length_compileQ_qsvtReal`.
* `zeroPattern a`, `zeroProj_eq_diagProj`, `ctrlX_zeroProj_eq` (CIRC-5).
-/

namespace QSVT.Qubit

open QuantumState QSVT.Encoding QSVT.Circuit

variable {n : ℕ}

/-! ### Qubit-level oracle encodings -/

/-- CIRC-4. A projected unitary encoding on an `n`-qubit register whose projections are diagonal
in the computational basis: `Π = diagProj d`, `Π̃ = diagProj d'`. -/
structure QubitEncoding (n : ℕ) where
  /-- The oracle unitary `U` on `Qubits n`. -/
  U : L (Qubits n)
  /-- `U` is unitary. -/
  hU : U ∈ unitary (L (Qubits n))
  /-- The input projection is `diagProj d`. -/
  d : (Fin n → Bool) → Bool
  /-- The output projection is `diagProj d'`. -/
  d' : (Fin n → Bool) → Bool

namespace QubitEncoding

/-- CIRC-4. The projected unitary encoding `(U, diagProj d, diagProj d')` of a qubit encoding. -/
noncomputable def toProj (Q : QubitEncoding n) : ProjUnitaryEncoding (Qubits n) where
  U := Q.U
  hU := Q.hU
  P := diagProj Q.d
  P' := diagProj Q.d'
  hP := diagProj_isProjective Q.d
  hP' := diagProj_isProjective Q.d'

variable (Q : QubitEncoding n)

@[simp] theorem toProj_U : Q.toProj.U = Q.U := rfl

@[simp] theorem toProj_P : Q.toProj.P = diagProj Q.d := rfl

/-- The output projection of `Q.toProj` is `diagProj Q.d'`. -/
@[simp] theorem toProj_P' : Q.toProj.P' = diagProj Q.d' := rfl

theorem U_adjoint_mem_unitary : Q.U† ∈ unitary (L (Qubits n)) := Unitary.star_mem Q.hU

end QubitEncoding

/-- CIRC-4. A Hermitian qubit encoding: `Π̃ = Π = diagProj d` and `Π U Π` self-adjoint (the
setting of SVT-8 / Route B). -/
structure QubitHermitianEncoding (n : ℕ) where
  /-- The oracle unitary `U` on `Qubits n`. -/
  U : L (Qubits n)
  /-- `U` is unitary. -/
  hU : U ∈ unitary (L (Qubits n))
  /-- Both projections are `diagProj d`. -/
  d : (Fin n → Bool) → Bool
  /-- The encoded operator `Π U Π` is self-adjoint. -/
  encoded_selfAdjoint : IsSelfAdjoint (diagProj d * U * diagProj d)

namespace QubitHermitianEncoding

/-- CIRC-4. The underlying qubit encoding (`d' = d`). -/
def toQubit (Q : QubitHermitianEncoding n) : QubitEncoding n :=
  ⟨Q.U, Q.hU, Q.d, Q.d⟩

/-- CIRC-4. The Hermitian encoding `(U, diagProj d, diagProj d)` on `Qubits n`. -/
noncomputable def toHermitian (Q : QubitHermitianEncoding n) : HermitianEncoding (Qubits n) where
  toProjUnitaryEncoding := Q.toQubit.toProj
  P'_eq := rfl
  encoded_selfAdjoint := Q.encoded_selfAdjoint

variable (Q : QubitHermitianEncoding n)

@[simp] theorem toQubit_U : Q.toQubit.U = Q.U := rfl

@[simp] theorem toQubit_d : Q.toQubit.d = Q.d := rfl

/-- The output predicate of `Q.toQubit` is `Q.d`. -/
@[simp] theorem toQubit_d' : Q.toQubit.d' = Q.d := rfl

/-- The projected unitary encoding underlying `Q.toHermitian` is `Q.toQubit.toProj`. -/
@[simp] theorem toHermitian_toProj : Q.toHermitian.toProjUnitaryEncoding = Q.toQubit.toProj := rfl

end QubitHermitianEncoding

/-! ### Qubit gates on the `(n + 1)`-qubit register -/

/-- CIRC-4. Gates on `Qubits (n + 1)` (qubit `0` = the QSVT ancilla, qubits `1..n` = the system
register) relative to a qubit encoding `Q`. -/
inductive QGate (n : ℕ)
  /-- The oracle `1 ⊗ U` on the system register. -/
  | oracle
  /-- The inverse oracle `1 ⊗ U†`. -/
  | oracleAdj
  /-- The multi-controlled `X` on qubit `0`, controlled on the system register satisfying `d`. -/
  | ctrlX (d : (Fin n → Bool) → Bool)
  /-- The phase `e^{iφ Z}` on qubit `0`. -/
  | rz (φ : ℝ)
  /-- The Hadamard on qubit `0`. -/
  | h

namespace QGate

/-- CIRC-4. Denotation of a qubit gate as an operator on `Qubits (n + 1)`. -/
noncomputable def denote (Q : QubitEncoding n) : QGate n → L (Qubits (n + 1))
  | oracle => tensorId Q.U
  | oracleAdj => tensorId (Q.U†)
  | ctrlX d => QSVT.Qubit.ctrlX d
  | rz φ => QSVT.Qubit.rz 0 φ
  | h => hadamard 0

variable (Q : QubitEncoding n)

@[simp] theorem denote_oracle : denote Q oracle = tensorId Q.U := rfl

@[simp] theorem denote_oracleAdj : denote Q oracleAdj = tensorId (Q.U†) := rfl

@[simp] theorem denote_ctrlX (d : (Fin n → Bool) → Bool) :
    denote Q (ctrlX d) = QSVT.Qubit.ctrlX d := rfl

@[simp] theorem denote_rz (φ : ℝ) : denote Q (rz φ) = QSVT.Qubit.rz 0 φ := rfl

@[simp] theorem denote_h : denote Q h = hadamard 0 := rfl

/-- CIRC-4. Every qubit gate is unitary. -/
theorem denote_mem_unitary (g : QGate n) : denote Q g ∈ unitary (L (Qubits (n + 1))) := by
  cases g with
  | oracle => exact tensorId_mem_unitary Q.hU
  | oracleAdj => exact tensorId_mem_unitary Q.U_adjoint_mem_unitary
  | ctrlX d => exact ctrlX_mem_unitary d
  | rz φ => exact rz_mem_unitary 0 φ
  | h => exact hadamard_mem_unitary 0

/-! ### Boolean classifiers (for the resource counters) -/

/-- Is the gate an oracle call (`oracle` or `oracleAdj`)? -/
def isOracle : QGate n → Bool
  | oracle => true
  | oracleAdj => true
  | ctrlX _ => false
  | rz _ => false
  | h => false

/-- Is the gate a multi-controlled `X`? -/
def isCtrlX : QGate n → Bool
  | oracle => false
  | oracleAdj => false
  | ctrlX _ => true
  | rz _ => false
  | h => false

/-- Is the gate an ancilla phase `rz`? -/
def isRz : QGate n → Bool
  | oracle => false
  | oracleAdj => false
  | ctrlX _ => false
  | rz _ => true
  | h => false

/-- Is the gate the ancilla Hadamard? -/
def isH : QGate n → Bool
  | oracle => false
  | oracleAdj => false
  | ctrlX _ => false
  | rz _ => false
  | h => true

end QGate

/-- CIRC-4. A qubit circuit on `Qubits (n + 1)`: a list of gates read as a product in list order
(leftmost gate = leftmost factor = the gate applied last), as for `QSVT.Circuit`. -/
abbrev QCircuit (n : ℕ) : Type := List (QGate n)

namespace QCircuit

/-- CIRC-4. Denotation of a qubit circuit: the product of its gates in list order. -/
noncomputable def denote (Q : QubitEncoding n) (c : QCircuit n) : L (Qubits (n + 1)) :=
  (c.map (QGate.denote Q)).prod

variable (Q : QubitEncoding n)

@[simp] theorem denote_nil : denote Q [] = 1 := rfl

@[simp] theorem denote_cons (g : QGate n) (c : QCircuit n) :
    denote Q (g :: c) = QGate.denote Q g * denote Q c := by
  rw [denote, denote, List.map_cons, List.prod_cons]

@[simp] theorem denote_singleton (g : QGate n) : denote Q [g] = QGate.denote Q g := by
  rw [denote_cons, denote_nil, mul_one]

/-- CIRC-4. Concatenation of qubit circuits is multiplication of their denotations. -/
theorem denote_append (c₁ c₂ : QCircuit n) :
    denote Q (c₁ ++ c₂) = denote Q c₁ * denote Q c₂ := by
  simp only [denote, List.map_append, List.prod_append]

/-- CIRC-4. Every qubit circuit denotes a unitary. -/
theorem denote_mem_unitary (c : QCircuit n) : denote Q c ∈ unitary (L (Qubits (n + 1))) := by
  induction c with
  | nil => rw [denote_nil]; exact one_mem _
  | cons g c ih => rw [denote_cons]; exact mul_mem (QGate.denote_mem_unitary Q g) ih

/-- Number of oracle calls (`oracle` and `oracleAdj`) in a qubit circuit. -/
def oracleCount (c : QCircuit n) : ℕ := c.countP QGate.isOracle

/-- Number of multi-controlled `X` gates in a qubit circuit. -/
def ctrlXCount (c : QCircuit n) : ℕ := c.countP QGate.isCtrlX

/-- Number of ancilla phases `rz` in a qubit circuit. -/
def rzCount (c : QCircuit n) : ℕ := c.countP QGate.isRz

/-- Number of ancilla Hadamards in a qubit circuit. -/
def hCount (c : QCircuit n) : ℕ := c.countP QGate.isH

end QCircuit

/-! ### Compilation -/

/-- CIRC-4. The qubit gate of a primitive: the oracle calls are kept, `C_Π NOT` and `C_Π̃ NOT`
become the multi-controlled `X` with control predicates `Q.d`, `Q.d'`, the ancilla phase becomes
`rz` and the ancilla Hadamard `h`. -/
def compilePrim (Q : QubitEncoding n) : Prim → QGate n
  | .oracle => .oracle
  | .oracleAdj => .oracleAdj
  | .cpiNotP => .ctrlX Q.d
  | .cpiNotP' => .ctrlX Q.d'
  | .ancPhase φ => .rz φ
  | .hadA => .h

/-- CIRC-4. Gate-by-gate compilation of a direct-sum circuit into a qubit circuit. -/
def compileQ (Q : QubitEncoding n) (c : QSVT.Circuit) : QCircuit n := c.map (compilePrim Q)

section compile

variable (Q : QubitEncoding n)

@[simp] theorem compileQ_nil : compileQ Q [] = [] := rfl

@[simp] theorem compileQ_cons (p : Prim) (c : QSVT.Circuit) :
    compileQ Q (p :: c) = compilePrim Q p :: compileQ Q c := rfl

theorem compileQ_append (c₁ c₂ : QSVT.Circuit) :
    compileQ Q (c₁ ++ c₂) = compileQ Q c₁ ++ compileQ Q c₂ := List.map_append

/-- CIRC-4 (gate level). Each primitive, transported along `ancEquiv`, is the denotation of its
compiled qubit gate. -/
theorem liftAnc_prim_denote (p : Prim) :
    liftAnc (Prim.denote Q.toProj p) = QGate.denote Q (compilePrim Q p) := by
  cases p with
  | oracle => exact liftAnc_liftU Q.U
  | oracleAdj => exact liftAnc_liftU (Q.U†)
  | cpiNotP => exact liftAnc_cpiNot_diagProj Q.d
  | cpiNotP' => exact liftAnc_cpiNot_diagProj Q.d'
  | ancPhase φ => exact liftAnc_ancPhase φ
  | hadA => exact liftAnc_hadA

/-- CIRC-4 (correctness of compilation). The denotation of a direct-sum circuit, transported
along the canonical isometry `ancEquiv n`, is the denotation of the compiled qubit circuit. -/
theorem liftAnc_denote (c : QSVT.Circuit) :
    liftAnc (Circuit.denote Q.toProj c) = QCircuit.denote Q (compileQ Q c) := by
  induction c with
  | nil => rw [Circuit.denote_nil, compileQ_nil, QCircuit.denote_nil, liftAnc_one]
  | cons p c ih =>
    rw [Circuit.denote_cons, compileQ_cons, QCircuit.denote_cons, liftAnc_mul, ih,
      liftAnc_prim_denote]

/-- CIRC-4. The compiled qubit circuit is the transported direct-sum circuit (the equivalent
`ancEquiv`-intertwining form of `liftAnc_denote`). -/
theorem denote_compileQ_apply (c : QSVT.Circuit) (v : Anc (Qubits n)) :
    QCircuit.denote Q (compileQ Q c) (ancEquiv n v) = ancEquiv n (Circuit.denote Q.toProj c v) := by
  rw [← liftAnc_denote, liftAnc_apply_ancEquiv]

/-- CIRC-4. Compilation preserves the gate count. -/
@[simp] theorem length_compileQ (c : QSVT.Circuit) : (compileQ Q c).length = c.length :=
  List.length_map _

theorem isOracle_compilePrim : QGate.isOracle ∘ compilePrim Q = Prim.isOracle := by
  funext p; cases p <;> rfl

theorem isCtrlX_compilePrim : QGate.isCtrlX ∘ compilePrim Q = Prim.isCpiNot := by
  funext p; cases p <;> rfl

theorem isRz_compilePrim : QGate.isRz ∘ compilePrim Q = Prim.isPhase := by
  funext p; cases p <;> rfl

theorem isH_compilePrim : QGate.isH ∘ compilePrim Q = Prim.isHad := by
  funext p; cases p <;> rfl

/-- CIRC-4 / IR-2. Compilation preserves the oracle count. -/
theorem oracleCount_compileQ (c : QSVT.Circuit) :
    QCircuit.oracleCount (compileQ Q c) = Circuit.oracleCount c := by
  rw [QCircuit.oracleCount, compileQ, List.countP_map, isOracle_compilePrim, Circuit.oracleCount]

/-- CIRC-4 / IR-2. The multi-controlled `X` count is the controlled-NOT count. -/
theorem ctrlXCount_compileQ (c : QSVT.Circuit) :
    QCircuit.ctrlXCount (compileQ Q c) = Circuit.cpiNotCount c := by
  rw [QCircuit.ctrlXCount, compileQ, List.countP_map, isCtrlX_compilePrim, Circuit.cpiNotCount]

/-- CIRC-4 / IR-2. The `rz` count is the ancilla phase count. -/
theorem rzCount_compileQ (c : QSVT.Circuit) :
    QCircuit.rzCount (compileQ Q c) = Circuit.phaseCount c := by
  rw [QCircuit.rzCount, compileQ, List.countP_map, isRz_compilePrim, Circuit.phaseCount]

/-- CIRC-4 / IR-2. The Hadamard count is preserved. -/
theorem hCount_compileQ (c : QSVT.Circuit) :
    QCircuit.hCount (compileQ Q c) = Circuit.hadCount c := by
  rw [QCircuit.hCount, compileQ, List.countP_map, isH_compilePrim, Circuit.hadCount]

end compile

/-! ### The Route B circuit on qubits (GSLW Cor 18) -/

section qsvtReal

variable (Q : QubitHermitianEncoding n)

/-- CIRC-4 (headline; GSLW Cor 18 on qubits). The `(n + 1)`-qubit circuit compiled from the
Route B gate list `compileQsvtReal Φ` implements the unitary of the Hermitian encoding
`E.qsvtReal Φ` (SVT-8), up to the canonical isometry `ancEquiv n`:
`QCircuit.denote Q (compileQ Q (compileQsvtReal Φ)) = liftAnc (E.qsvtReal Φ).U`. -/
theorem compileQ_qsvtReal (Φ : List ℝ) :
    QCircuit.denote Q.toQubit (compileQ Q.toQubit (compileQsvtReal Φ)) =
      liftAnc (Q.toHermitian.qsvtReal Φ).U := by
  rw [← liftAnc_denote, ← denote_compileQsvtReal Q.toHermitian Φ,
    QubitHermitianEncoding.toHermitian_toProj]

/-- CIRC-4 / IR-2 (GSLW Lemma 19). The qubit Route B circuit makes `Φ.length` oracle calls. -/
theorem oracleCount_compileQ_qsvtReal (Φ : List ℝ) :
    QCircuit.oracleCount (compileQ Q.toQubit (compileQsvtReal Φ)) = Φ.length := by
  rw [oracleCount_compileQ, oracleCount_compileQsvtReal]

/-- CIRC-4 / IR-2 (GSLW Lemma 19). The qubit Route B circuit has `4 * Φ.length + 2` gates. -/
theorem length_compileQ_qsvtReal (Φ : List ℝ) :
    (compileQ Q.toQubit (compileQsvtReal Φ)).length = 4 * Φ.length + 2 := by
  rw [length_compileQ, length_compileQsvtReal]

/-- CIRC-4 / IR-2. The qubit Route B circuit uses `2 * Φ.length` multi-controlled `X` gates. -/
theorem ctrlXCount_compileQ_qsvtReal (Φ : List ℝ) :
    QCircuit.ctrlXCount (compileQ Q.toQubit (compileQsvtReal Φ)) = 2 * Φ.length := by
  rw [ctrlXCount_compileQ, cpiNotCount_compileQsvtReal]

end qsvtReal

/-! ### The anti-control pattern of `zeroProj` (CIRC-5) -/

/-- CIRC-5. The control predicate of the block-encoding projector `|0…0⟩⟨0…0| ⊗ I`: the first `a`
register qubits are all `0` (`a` anti-controls). -/
def zeroPattern (a : ℕ) (b : Fin n → Bool) : Bool := decide (∀ i : Fin n, i.val < a → b i = false)

/-- CIRC-5. `zeroProj a` is the diagonal projector of `zeroPattern a`. -/
theorem zeroProj_eq_diagProj (a : ℕ) : (zeroProj a : L (Qubits n)) = diagProj (zeroPattern a) :=
  rfl

/-- CIRC-5. `C_Π NOT` for `Π = zeroProj a` is one multi-controlled `X` with `a` anti-controls:
the `cpiNotP` primitive of an encoding with `d = zeroPattern a` compiles to `ctrlX (zeroPattern a)`
(`compilePrim`), whose denotation is `liftAnc (cpiNot (zeroProj a))`. -/
theorem ctrlX_zeroProj_eq (a : ℕ) :
    liftAnc (cpiNot (zeroProj a : L (Qubits n))) = ctrlX (zeroPattern a) :=
  liftAnc_cpiNot_zeroProj a

end QSVT.Qubit
