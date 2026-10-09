/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Sign21Phases
import QSVT.Examples.Sign21
import QSVT.Circuit.Primitive

/-!
# APP-1: the certified sign-function transformation implemented by Route B (optimal queries)

The second end-to-end application of the library (formal-spec APP-1, GSLW Thm 26 "singular
vector transformation" in the Hermitian/eigenvector case), now with the *phase-based* QSVT
circuit of GSLW Cor 18 (Route B, SVT-8) instead of the Chebyshev LCU of Route A
(`QSVT.Examples.Sign21`).  Same certified polynomial, optimal query count.

* The polynomial is the degree-21 odd approximation `sign21` of `c · sign x`,
  `c = sign21Scale ≈ 0.8924` (CERT-B part 1: `‖p‖_∞ ≤ 1`, `|p(x) − c| ≤ 0.0236` on `[0.15, 1]`).
* The *only* numerics-dependent input is the phase list `sign21Phases` (QSPPACK output), whose
  correctness `‖Re[P_Φ̃] − sign21‖ ≤ 10⁻¹²` is checked by the Lean kernel in
  `sign21_checkRe`/`sign21_rePoly_bound` (CERT-B part 2, `QSVT.Certificate.Sign21Phases`); no
  phase is trusted.
* The circuit is `signB E = E.qsvtReal Φ̃` (SVT-8), the two-term LCU of `U_Φ̃` and `U_{−Φ̃}` on
  `Anc ℋ` with **one ancilla qubit**, whose unitary is the gate list `compileQsvtReal Φ̃` of
  CIRC-3 (`signB_U_eq`): `21` oracle calls, `42` controlled NOTs, `21` ancilla phases, `2`
  Hadamards, `86` primitive gates in all (`signB_oracleCount`, …).  Its `(0,0)` block is
  `Re[P_Φ̃](A) Π` exactly (`signB_topLeft`, GSLW Cor 18).
* On the eigenbasis of `A` (SVT-3) this gives the GSLW Thm 26-style statements
  `signB_apply_pos`/`signB_apply_neg`: every eigenvector `ψᵢ` with eigenvalue `|ςᵢ| ≥ 0.15` is
  mapped by the compressed circuit to `± sign21Scale · ψᵢ ≈ ± 0.8924 ψᵢ` up to an error of norm
  `≤ 10⁻¹² + 0.0236`, and every eigenvector to a vector of norm `≤ 1 + 10⁻¹²`
  (`signB_apply_norm_le`).  Unlike Route A there is no subnormalisation (`‖c‖₁ = 1`).
* The same program through the IR (IR-1/2): `signBExpr = qsvtReal Φ̃ oracle` has
  `spec signBExpr = Re[P_Φ̃]` (within `10⁻¹²` of `sign21`, `spec_signBExpr_bound`),
  `scale = 1`, `queries signBExpr = 21`, `ancillaDim signBExpr = 2`, and the soundness theorem
  gives `base_signBExpr`.

## Route A versus Route B (the same certified polynomial `sign21`)

|                | Route A (`signCircuit`, CERT-A)      | Route B (`signB`, CERT-B)             |
|----------------|--------------------------------------|---------------------------------------|
| oracle queries | `231 = ∑_{k<22} k`                   | `21 = deg p` (optimal)                |
| ancilla        | `22`-dimensional register (5 qubits) | one qubit (`Anc ℋ`, dimension `2`)    |
| operator       | `‖c‖₁⁻¹ · p(A) Π`, `‖c‖₁ ≈ 2.21`     | `Re[P_Φ̃](A) Π`, `10⁻¹²`-close to `p` |
| numerics       | none (closed-form Chebyshev phases)  | `21` phases, kernel-checked (45 s)    |

Route B uses `11×` fewer queries and one ancilla qubit instead of five, at the price of a
phase-finding step whose output is certified, not trusted.  Every theorem here depends only on
`propext`, `Classical.choice`, `Quot.sound` (audited in `test/QSVTTest/Sign21RouteB.lean`).
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: the certified phases and their polynomial -/

/-- APP-1. Both routes implement the same polynomial: the certified target of the phases is the
Chebyshev coefficient list `signChebQ` of Route A (kernel evaluation, `sign21Target_eq_map_fst`). -/
theorem sign21Target_eq_signChebQ : sign21Target = signChebQ := sign21Target_eq_map_fst

/-! ### The implementation: the Route B encoding and its circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-1. The Route B encoding `E.qsvtReal Φ̃` (GSLW Cor 18, SVT-8) with the certified phases
`Φ̃ = sign21Phases`: a Hermitian encoding on `Anc ℋ` (one ancilla qubit) of `Re[P_Φ̃](A)`, with
`Re[P_Φ̃]` within `10⁻¹²` of `sign21` on `[-1, 1]` (`sign21_rePoly_bound`). -/
noncomputable def signB : HermitianEncoding (Anc ℋ) := E.qsvtReal (sign21Phases.map (↑))

/-- APP-1. The projection of the Route B encoding is `|0⟩⟨0| ⊗ Π`. -/
@[simp] theorem signB_P : (signB E).P = blockDiag E.P 0 := rfl

/-- APP-1. The Route B unitary is unitary on `Anc ℋ`. -/
theorem signB_U_mem_unitary : (signB E).U ∈ unitary (L (Anc ℋ)) := (signB E).hU

/-- APP-1 (CIRC-3). The unitary of the Route B encoding is the denotation of the gate list
`compileQsvtReal Φ̃`: `86` primitive gates (`signB_length`), `21` of them oracle calls
(`signB_oracleCount`). -/
theorem signB_U_eq :
    (signB E).U =
      Circuit.denote E.toProjUnitaryEncoding (Circuit.compileQsvtReal (sign21Phases.map (↑))) :=
  (Circuit.denote_compileQsvtReal E _).symm

/-- APP-1 (exact implementation, GSLW Cor 18). The `(0,0)` block of the encoded operator is
`Re[P_Φ̃](A) Π` with zero circuit error:
```
(⟨0| ⊗ Π) (signB E).U (|0⟩ ⊗ Π) = Re[P_Φ̃](A) Π.
```
-/
theorem signB_topLeft :
    topLeft (signB E).encoded =
      aeval E.encoded (rePoly (qspPoly (sign21Phases.map (↑))).1) * E.P :=
  topLeft_qsvtReal_encoded E _

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-1. On an eigenvector `ψᵢ` of `A` with eigenvalue `ςᵢ`, the compressed circuit acts as the
scalar `Re[P_Φ̃](ςᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem signB_apply_eigenVec :
    topLeft (signB E).encoded (eigenVec E i) =
      (rePoly (qspPoly (sign21Phases.map (↑))).1).eval (eigenValue E i : ℂ) • eigenVec E i := by
  rw [signB_topLeft, Module.End.mul_apply, P_eigenVec, aeval_eigenVec]

/-- APP-1 (certified behaviour, positive spectrum; GSLW Thm 26 style). Every eigenvector `ψᵢ` of
`A` with eigenvalue `ςᵢ ≥ 0.15` is mapped by the compressed Route B circuit to
`sign21Scale · ψᵢ ≈ 0.8924 ψᵢ`, up to an error of norm at most `10⁻¹² + 0.0236`: the phase
certificate `sign21_checkRe` plus the plateau certificate of CERT-B part 1. -/
theorem signB_apply_pos (hi : 0.15 ≤ eigenValue E i) :
    ‖topLeft (signB E).encoded (eigenVec E i) - (sign21Scale : ℂ) • eigenVec E i‖ ≤
      sign21Eps + 0.0236 := by
  have hx : eigenValue E i ∈ Set.Icc (0.15 : ℝ) 1 := ⟨hi, (eigenValue_mem_Icc E i).2⟩
  rw [signB_apply_eigenVec, ← sub_smul, norm_smul, norm_eigenVec, mul_one]
  exact sign21_rePoly_sub_scale_le _ hx

/-- APP-1 (certified behaviour, negative spectrum). Every eigenvector `ψᵢ` of `A` with eigenvalue
`ςᵢ ≤ -0.15` is mapped to `-sign21Scale · ψᵢ ≈ -0.8924 ψᵢ`, up to an error of norm at most
`10⁻¹² + 0.0236`. -/
theorem signB_apply_neg (hi : eigenValue E i ≤ -0.15) :
    ‖topLeft (signB E).encoded (eigenVec E i) - (-(sign21Scale : ℂ)) • eigenVec E i‖ ≤
      sign21Eps + 0.0236 := by
  have hx : eigenValue E i ∈ Set.Icc (-1 : ℝ) (-0.15) := ⟨(eigenValue_mem_Icc E i).1, hi⟩
  rw [signB_apply_eigenVec, ← sub_smul, norm_smul, norm_eigenVec, mul_one, sub_neg_eq_add]
  exact sign21_rePoly_add_scale_le _ hx

/-- APP-1 (global bound). The compressed Route B circuit maps every eigenvector `ψᵢ` (any
eigenvalue in `[-1, 1]`) to a vector of norm at most `1 + 10⁻¹²`, from the admissibility
certificate `‖sign21‖_∞ ≤ 1` and the phase certificate. -/
theorem signB_apply_norm_le : ‖topLeft (signB E).encoded (eigenVec E i)‖ ≤ 1 + sign21Eps := by
  rw [signB_apply_eigenVec, norm_smul, norm_eigenVec, mul_one]
  exact sign21_rePoly_norm_le _ (eigenValue_mem_Icc E i)

end Circuit

/-! ### Resources (GSLW Lemma 19 / Cor 18, IR-2) -/

/-- APP-1. The Route B circuit makes `21 = deg sign21` oracle calls (`U` or `U†`), the optimal
count; Route A makes `231` (`signCircuit_queries`). -/
theorem signB_oracleCount :
    Circuit.oracleCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 := by
  rw [Circuit.oracleCount_compileQsvtReal, List.length_map, sign21Phases_length]

/-- APP-1. `42 = 2 · 21` controlled NOTs `C_Π NOT`. -/
theorem signB_cpiNotCount :
    Circuit.cpiNotCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) = 42 := by
  rw [Circuit.cpiNotCount_compileQsvtReal, List.length_map, sign21Phases_length]

/-- APP-1. `21` ancilla phase gates `e^{iφ Z}`, one per certified phase. -/
theorem signB_phaseCount :
    Circuit.phaseCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 := by
  rw [Circuit.phaseCount_compileQsvtReal, List.length_map, sign21Phases_length]

/-- APP-1. Two ancilla Hadamards (the LCU of `U_Φ̃` and `U_{−Φ̃}`). -/
theorem signB_hadCount :
    Circuit.hadCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) = 2 :=
  Circuit.hadCount_compileQsvtReal _

/-- APP-1. `86 = 4 · 21 + 2` primitive gates in all. -/
theorem signB_length : (Circuit.compileQsvtReal (sign21Phases.map (↑))).length = 86 := by
  rw [Circuit.length_compileQsvtReal, List.length_map, sign21Phases_length]

/-! ### The same example through the IR (IR-1/2) -/

section IR

open QSVT.IR

/-- APP-1. The IR program: one real-part QSVT node with the certified phases applied to the
oracle. -/
noncomputable def signBExpr : Expr := .qsvtReal (sign21Phases.map (↑)) .oracle

/-- APP-1. The specification polynomial of `signBExpr` is `Re[P_Φ̃]`. -/
theorem spec_signBExpr : spec signBExpr = rePoly (qspPoly (sign21Phases.map (↑))).1 := by
  rw [signBExpr, spec_qsvtReal, normSpec_oracle, comp_X]

/-- APP-1. `signBExpr` implements `sign21` within `10⁻¹²` on `[-1, 1]`. -/
theorem spec_signBExpr_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(spec signBExpr).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)‖ ≤ sign21Eps := by
  rw [spec_signBExpr]
  exact sign21_rePoly_bound

/-- APP-1. A QSVT step is exact: no subnormalisation. -/
theorem scale_signBExpr : scale signBExpr = 1 := rfl

/-- APP-1. `signBExpr` is well scaled (no `chebLCU` node). -/
theorem signBExpr_wellScaled : WellScaled signBExpr := trivial

/-- APP-1 (through the IR soundness theorem). The base block of `signBExpr` is `Re[P_Φ̃](A₀) Π`,
the same operator as `signB_topLeft`. -/
theorem base_signBExpr (E₀ : HermitianEncoding ℋ) :
    base E₀ signBExpr = aeval E₀.encoded (rePoly (qspPoly (sign21Phases.map (↑))).1) * E₀.P :=
  base_qsvtReal_oracle E₀ _

/-- APP-1. `signBExpr` uses `21` oracle queries (IR-2); `signExpr` of Route A uses `231`. -/
theorem queries_signBExpr : queries signBExpr = 21 := by
  rw [signBExpr, queries_qsvtReal, queries_oracle, List.length_map, sign21Phases_length, mul_one]

/-- APP-1. The ancilla of `signBExpr` is one qubit (`ancillaDim = 2`; Route A: `22`). -/
theorem ancillaDim_signBExpr : ancillaDim signBExpr = 2 := by
  rw [signBExpr, ancillaDim_qsvtReal, ancillaDim_oracle, mul_one]

/-- APP-1. The degree bound of IR-2 instantiated: `deg (spec signBExpr) ≤ 21`. -/
theorem natDegree_spec_signBExpr_le : (spec signBExpr).natDegree ≤ 21 :=
  (natDegree_spec_le signBExpr).trans_eq queries_signBExpr

end IR

end QSVT.Examples
