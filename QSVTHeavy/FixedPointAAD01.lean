/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Compose
import QSVTHeavy.SignD01Phases

/-!
# APP-1 (gap `δ = 0.1`): fixed-point amplitude amplification with the degree-35 sign polynomial

The fixed-point amplitude amplification of `QSVT.Examples.FixedPointAA` (APP-1, GSLW Thm 27)
instantiated with the second certified sign approximation `signD01` of the heavy library
(`QSVTHeavy.SignD01`, `QSVTHeavy.SignD01Phases`): gap `δ = 0.1` instead of `0.15`, degree `35`
instead of `21`, plateau centre `c = signD01Scale = 0.9875` instead of `0.8924` and ripple `0.012`
instead of `0.0236`.  This is the amplification step needed by the matrix-inversion example
(`QSVTHeavy.InverseAA`, GSLW Thm 41), whose initial good amplitude is only `≈ 0.112 < 0.15`.

The setting, the encoding `aaEncoding hU hG hψ₀ = (U, |ψ₀⟩⟨ψ₀|, Π_good)` and the singular pair
`(ψ₀, a)` with left singular vector `ψ_G` are those of `QSVT.Examples.FixedPointAA`; only the phase
list changes, so every proof is the sign21 proof with the SignD01 certificates
(`signD01_rePoly_sub_scale_le`, `signD01_rePoly_bound`, `signD01_plateau`).

* `aaCircuitD01 hU hG hψ₀ = lcu2 U_Φ̃ U_{−Φ̃}` with `Φ̃ = signD01Phases` (odd length `35`), on
  `Anc ℋ`: one ancilla qubit, `35` queries to `U`/`U†` (`aaCircuitD01_oracleCount`), gate list
  `compileQsvtReal Φ̃` of `142` primitive gates (`aaCircuitD01_eq_denote`, `aaCircuitD01_length`).
* `fixedPointAAD01_apply` (exact): `(⟨0| ⊗ Π_good) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G`.
* `fixedPointAAD01_bound`: for every initial amplitude `a ≥ 0.1`,
  `‖(⟨0| ⊗ Π_good) W (|0⟩ ⊗ ψ₀) − c ψ_G‖ ≤ 10⁻¹² + 0.012`, `c = signD01Scale = 0.9875`.
* `fixedPointAAD01_amplitude`: `0.975 ≤ ‖(|0⟩⟨0| ⊗ Π_good) W (|0⟩ ⊗ ψ₀)‖` for every `a ≥ 0.1`
  (success probability `≥ 0.975² ≈ 0.95`, against `a² ≥ 0.01` initially), from the plateau
  certificate `signD01_plateau` (`p ≥ 0.9755` on `[0.1, 1]`) and the phase certificate.
* The register version (APP-COMPOSE bridge): for a unitary `W : L (Reg m ℋ)`, `b ∈ ran Π`,
  `‖b‖ = 1`, the circuit `regAAD01Circuit E hW hb1 : L (Anc (Reg m ℋ))` satisfies
  `regAAD01_apply`, `regAAD01_bound` and `regAAD01_amplitude` under the hypothesis
  `0.1 ≤ regAmp E W b`.

Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`QSVTHeavy.InverseAATest`).
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QSVT.IR QSVT.Pipeline QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The phases -/

/-- APP-1. The certified gap-`0.1` phase list has odd length `35`. -/
theorem signD01Phases_odd : Odd ((signD01Phases.map (↑) : List ℝ)).length := by
  rw [List.length_map, signD01Phases_length]
  exact ⟨17, rfl⟩

/-- APP-1. `‖(signD01Scale : ℂ)‖ = signD01Scale` (`= 0.9875 ≥ 0`). -/
theorem norm_signD01Scale : ‖(signD01Scale : ℂ)‖ = (signD01Scale : ℝ) := by
  rw [Complex.norm_ratCast, abs_of_nonneg]
  rw [signD01Scale]
  norm_num

/-- APP-1. `0 ≤ signD01Scale`. -/
theorem signD01Scale_nonneg : (0 : ℝ) ≤ signD01Scale := by
  rw [signD01Scale]
  norm_num

/-! ### The fixed-point amplitude amplification circuit with gap `0.1` -/

section Setting

variable {U : L ℋ} {G : L ℋ} {ψ₀ ψG : ℋ} {a : ℝ}
  (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G) (hψ₀ : ‖ψ₀‖ = 1)

/-- APP-1 (GSLW Thm 27 circuit, gap `0.1`). The fixed-point amplitude amplification circuit
`W = lcu2 U_Φ̃ U_{−Φ̃}` on `Anc ℋ` with `Φ̃ = signD01Phases`: one ancilla qubit, `35` queries. It
is the unitary of the general Cor 18 encoding `(aaEncoding …).qsvtReal Φ̃` (`aaCircuitD01_eq_U`). -/
noncomputable def aaCircuitD01 : L (Anc ℋ) :=
  lcu2 (altSeq (aaEncoding hU hG hψ₀) (signD01Phases.map (↑)))
    (altSeq (aaEncoding hU hG hψ₀) ((signD01Phases.map (↑)).map Neg.neg))

/-- APP-1. `W` is the unitary of the packaged general Cor 18 encoding. -/
theorem aaCircuitD01_eq_U :
    aaCircuitD01 hU hG hψ₀ = ((aaEncoding hU hG hψ₀).qsvtReal (signD01Phases.map (↑))).U := rfl

/-- APP-1. `W` is unitary. -/
theorem aaCircuitD01_mem_unitary : aaCircuitD01 hU hG hψ₀ ∈ unitary (L (Anc ℋ)) := by
  rw [aaCircuitD01_eq_U]
  exact ProjUnitaryEncoding.hU _

/-- APP-1 (CIRC-3). `W` is the denotation of the gate list `compileQsvtReal Φ̃` with the oracle
`U`: `142` primitive gates, `35` of them oracle calls (`aaCircuitD01_oracleCount`). -/
theorem aaCircuitD01_eq_denote :
    aaCircuitD01 hU hG hψ₀ =
      Circuit.denote (aaEncoding hU hG hψ₀)
        (Circuit.compileQsvtReal (signD01Phases.map (↑))) := by
  rw [Circuit.compileQsvtReal, Circuit.denote_append, Circuit.denote_append,
    Circuit.denote_compileAltSeq_eq_blockDiag, Circuit.denote_singleton, Circuit.Prim.denote_hadA,
    aaCircuitD01, lcu2]

/-- APP-1 (exact, GSLW Thm 26/27 on the singular pair `(ψ₀, a)`). The good-subspace,
ancilla-`0` block of the circuit maps `ψ₀` *exactly* onto `ψ_G`, scaled by `Re[P_Φ̃](a)`:
```
(⟨0| ⊗ Π_good) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G.
```
-/
theorem fixedPointAAD01_apply (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    topLeft (blockDiag G 0 * aaCircuitD01 hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ =
      ((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (a : ℂ)) • ψG := by
  have h := topLeft_qsvt_real_apply_singular (aaEncoding hU hG hψ₀)
    (aa_isSingularPair hU hG hψ₀ hψG ha0 hGU) signD01Phases_odd
  rw [aa_lvOf hU hG hψ₀ ha0 hGU, aaEncoding_P, aaEncoding_P'] at h
  rw [aaCircuitD01]
  exact h

/-- APP-1 (fixed-point property, certified, gap `0.1`). For every initial good amplitude
`a ≥ 0.1`, the output of the `35`-query circuit in the good subspace is
`signD01Scale · ψ_G = 0.9875 ψ_G` up to an error of norm at most `10⁻¹² + 0.012`, independently
of `a`:
```
‖(⟨0| ⊗ Π_good) W (|0⟩ ⊗ ψ₀) − c ψ_G‖ ≤ 10⁻¹² + 0.012,    c = signD01Scale.
```
-/
theorem fixedPointAAD01_bound (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG)
    (ha : 0.1 ≤ a) :
    ‖topLeft (blockDiag G 0 * aaCircuitD01 hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ -
        (signD01Scale : ℂ) • ψG‖ ≤ signD01Eps + 0.012 := by
  rw [fixedPointAAD01_apply hU hG hψ₀ hψG ha0 hGU, ← sub_smul, norm_smul, hψG, mul_one]
  exact signD01_rePoly_sub_scale_le a ⟨ha, aa_le_one hU hG hψ₀ hψG ha0 hGU⟩

/-- APP-1. The ancilla-`0`, good-subspace component of the full output state `W (|0⟩ ⊗ ψ₀)` is
the `(0,0)`-block image of `ψ₀`, embedded in the ancilla-`0` branch. -/
theorem fixedPointAAD01_state :
    blockDiag G 0 (aaCircuitD01 hU hG hψ₀ (inl ψ₀)) =
      inl (topLeft (blockDiag G 0 * aaCircuitD01 hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀) := by
  have h0 : blockDiag (rankOne ψ₀) 0 (inl ψ₀) = inl ψ₀ := by
    rw [blockDiag, block_apply_inl, rankOne_apply_self hψ₀, LinearMap.zero_apply, map_zero,
      add_zero]
  rw [topLeft_apply, Module.End.mul_apply, Module.End.mul_apply, h0, blockDiag, fst_block,
    block_apply]
  simp only [LinearMap.zero_apply, add_zero, map_zero]

/-- APP-1 (success amplitude, gap `0.1`). After one run of the `35`-query circuit on
`|0⟩ ⊗ ψ₀`, the norm of the ancilla-`0`, good-subspace component is at least `0.975`, for every
initial amplitude `a ≥ 0.1` (success probability `≥ 0.975² ≈ 0.95`, against `a² ≥ 0.01`
initially); from the plateau certificate `signD01_plateau` (`p ≥ 0.9755` on `[0.1, 1]`) and the
phase certificate `signD01_rePoly_bound`. -/
theorem fixedPointAAD01_amplitude (hψG : ‖ψG‖ = 1) (ha0 : 0 < a)
    (hGU : G (U ψ₀) = (a : ℂ) • ψG) (ha : 0.1 ≤ a) :
    0.975 ≤ ‖blockDiag G 0 (aaCircuitD01 hU hG hψ₀ (inl ψ₀))‖ := by
  have ha1 : a ≤ 1 := aa_le_one hU hG hψ₀ hψG ha0 hGU
  rw [fixedPointAAD01_state hU hG hψ₀, norm_inl, fixedPointAAD01_apply hU hG hψ₀ hψG ha0 hGU,
    norm_smul, hψG, mul_one]
  have h1 := signD01_rePoly_bound a ⟨by linarith, ha1⟩
  have h2 : 0.9755 ≤ ‖signD01.toPoly.eval (a : ℂ)‖ := by
    rw [PolyQ.norm_eval_toPoly]
    exact (signD01_plateau a ⟨ha, ha1⟩).1.trans (le_abs_self _)
  have h3 := norm_le_norm_add_norm_sub
    ((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (a : ℂ)) (signD01.toPoly.eval (a : ℂ))
  have hε : ((signD01Eps : ℚ) : ℝ) ≤ 0.0001 := by
    rw [signD01Eps]
    norm_num
  linarith

end Setting

/-! ### Resources (GSLW Lemma 19 / Cor 18, IR-2) -/

/-- APP-1. The circuit makes `35` oracle calls (`U` or `U†`): one per certified phase. -/
theorem aaCircuitD01_oracleCount :
    Circuit.oracleCount (Circuit.compileQsvtReal (signD01Phases.map (↑))) = 35 := by
  rw [Circuit.oracleCount_compileQsvtReal, List.length_map, signD01Phases_length]

/-- APP-1. `142 = 4 · 35 + 2` primitive gates in all (one ancilla qubit). -/
theorem aaCircuitD01_length : (Circuit.compileQsvtReal (signD01Phases.map (↑))).length = 142 := by
  rw [Circuit.length_compileQsvtReal, List.length_map, signD01Phases_length]

/-! ### Fixed-point amplitude amplification of a register circuit (gap `0.1`) -/

section RegisterAACircuit

variable {m : ℕ} [NeZero m] (E : HermitianEncoding ℋ) {W : L (Reg m ℋ)}
  (hW : W ∈ unitary (L (Reg m ℋ))) {b : ℋ} (hb1 : ‖b‖ = 1)

/-- APP-1 (APP-COMPOSE bridge, gap `0.1`). The fixed-point amplitude amplification circuit with
the phases `signD01Phases` for the register circuit `W`, initial state `|0⟩ ⊗ b` and good
projector `|0⟩⟨0| ⊗ Π`, on `Anc (Reg m ℋ)` (one more ancilla qubit), with `35` uses of `W`/`W†`
(`aaCircuitD01_oracleCount`). -/
noncomputable def regAAD01Circuit : L (Anc (Reg m ℋ)) :=
  aaCircuitD01 hW (atZero_isProjective (m := m) E.hP) (norm_inj_zero b hb1)

/-- APP-1. The circuit is unitary. -/
theorem regAAD01Circuit_mem_unitary :
    regAAD01Circuit E hW hb1 ∈ unitary (L (Anc (Reg m ℋ))) :=
  aaCircuitD01_mem_unitary _ _ _

/-- APP-1 (exact; `fixedPointAAD01_apply`). The good-subspace, ancilla-`0` block of the circuit
maps `|0⟩ ⊗ b` exactly onto `ψ_G`, scaled by `Re[P_Φ̃](a)`. -/
theorem regAAD01_apply (hb : E.P b = b) (h : 0 < regAmp E W b) :
    topLeft (blockDiag (atZero E.P) 0 * regAAD01Circuit E hW hb1 *
        blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) =
      ((rePoly (qspPoly (signD01Phases.map (↑))).1).eval ((regAmp E W b : ℝ) : ℂ)) •
        regGoodState E W b :=
  fixedPointAAD01_apply hW _ _ (norm_regGoodState E W b h) h (atZero_P_apply_eq_smul E W b hb h)

/-- APP-1 (`fixedPointAAD01_bound`). For an initial amplitude `a ≥ 0.1` the good-subspace
output is `signD01Scale · ψ_G = 0.9875 ψ_G` up to `10⁻¹² + 0.012`. -/
theorem regAAD01_bound (hb : E.P b = b) (ha : 0.1 ≤ regAmp E W b) :
    ‖topLeft (blockDiag (atZero E.P) 0 * regAAD01Circuit E hW hb1 *
        blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) -
      (signD01Scale : ℂ) • regGoodState E W b‖ ≤ signD01Eps + 0.012 :=
  fixedPointAAD01_bound hW _ _ (norm_regGoodState E W b (by linarith)) (by linarith)
    (atZero_P_apply_eq_smul E W b hb (by linarith)) ha

/-- APP-1 (`fixedPointAAD01_amplitude`). For an initial amplitude `a ≥ 0.1` the norm of the
ancilla-`0`, good-subspace component of the output state is at least `0.975`. -/
theorem regAAD01_amplitude (hb : E.P b = b) (ha : 0.1 ≤ regAmp E W b) :
    0.975 ≤ ‖blockDiag (atZero E.P) 0 (regAAD01Circuit E hW hb1 (inl (inj 0 b)))‖ :=
  fixedPointAAD01_amplitude hW _ _ (norm_regGoodState E W b (by linarith)) (by linarith)
    (atZero_P_apply_eq_smul E W b hb (by linarith)) ha

end RegisterAACircuit

end QSVT.Examples
