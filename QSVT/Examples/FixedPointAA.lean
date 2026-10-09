/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.RealPolyGeneral
import QSVT.Certificate.Sign21Phases
import QSVT.Circuit.Primitive

/-!
# APP-1: fixed-point amplitude amplification by QSVT (GSLW Thm 26/27 flavour)

The third end-to-end application of the library: the *singular vector transformation* of GSLW
Thm 26 applied to the rank-one encoding of fixed-point amplitude amplification (GSLW Thm 27),
with the certified degree-21 sign approximation `sign21` of CERT-B and the general (non-Hermitian)
Cor 18 of `QSVT.SVT.RealPolyGeneral`.

## Setting (GSLW Thm 27)

A unitary `U`, an orthogonal projector `Π` onto the "good" subspace (called `G` here, since `Π`
is Mathlib's pi-type binder), and a unit initial state `ψ₀` such that
```
Π U ψ₀ = a ψ_G,      ‖ψ_G‖ = 1,  0 < a
```
(`a = ‖Π U ψ₀‖` is the initial good amplitude; GSLW's `|ψ_G⟩ = Π U |ψ₀⟩ / ‖Π U |ψ₀⟩‖`). With the
rank-one projector `|ψ₀⟩⟨ψ₀|` (`rankOne ψ₀`) this is the projected unitary encoding
`E = (U, Π = |ψ₀⟩⟨ψ₀|, Π̃ = Π)` (`aaEncoding`), whose encoded operator is `A = Π U |ψ₀⟩⟨ψ₀|`,
and `(ψ₀, a)` is a singular pair of `A` with left singular vector `ψ_G`
(`aa_isSingularPair`, `aa_lvOf`): `A ψ₀ = a ψ_G`, `A†A ψ₀ = a² ψ₀`.

## The circuit and its guarantees

With the certified phases `Φ̃ = sign21Phases` (odd length `21`) the circuit is the two-term LCU
`W = lcu2 U_Φ̃ U_{−Φ̃}` on `Anc ℋ` (`aaCircuit`), one ancilla qubit and `21` queries to `U`/`U†`;
its gate list is `compileQsvtReal Φ̃` of CIRC-3 (`aaCircuit_eq_denote`, `aaCircuit_oracleCount`).
By the general Cor 18 on the singular pair `(ψ₀, a)`:

* `fixedPointAA_apply` (exact): `(⟨0| ⊗ Π) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G`. The
  good-subspace component of the output is *exactly* along `ψ_G`, for every `a ∈ (0, 1]`.
* `fixedPointAA_bound`: for every initial amplitude `a ≥ 0.15`,
  `‖(⟨0| ⊗ Π) W (|0⟩ ⊗ ψ₀) − c ψ_G‖ ≤ 10⁻¹² + 0.0236` with the plateau value
  `c = sign21Scale ≈ 0.8924` — the fixed-point property: the output amplitude is `≈ c` whatever
  the unknown initial overlap `a ≥ 0.15` is, with no risk of "overshooting".
* `fixedPointAA_amplitude`: `0.869 ≤ ‖(|0⟩⟨0| ⊗ Π) W (|0⟩ ⊗ ψ₀)‖`, i.e. after one run of the
  `21`-query circuit the probability of measuring the ancilla in `|0⟩` and the system in the good
  subspace is at least `0.869² ≈ 0.755`, uniformly in `a ∈ [0.15, 1]` (against `a²` initially,
  which can be as small as `0.0225`); and conditioned on this outcome the system state is exactly
  `ψ_G`.

## Relation to GSLW Thm 27 (ε-dependence)

GSLW Thm 27 prepares `ψ_G` to precision `ε` with `O(log(1/ε)/δ)` queries from any `a ≥ δ`, using
a polynomial approximation of `sign x` with plateau value `1 − ε` on `[δ, 1]`. Our certified
polynomial has `δ = 0.15`, degree `21`, and plateau value `c ≈ 0.8924` *rather than `1`*: the
phase solver's target was `c · sign x` scaled so that the QSP polynomial fits into the unit disc
(`sign21Scale`, CERT-B part 1), and the ripple `0.0236` is its Chebyshev truncation error. The
direction of the output is still exact (`fixedPointAA_apply`); only its norm is `≈ 0.89` instead
of `≈ 1`. A polynomial with plateau closer to `1` (hence higher degree, or an `L^∞`-optimal sign
approximation) would need a new certificate, produced by the same pipeline (phase solver →
`checkRe` kernel certificate → `sign21_rePoly_sub_scale_le`-style bound); nothing else changes.
Every theorem here depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/FixedPointAA.lean`).
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The rank-one projector `|ψ₀⟩⟨ψ₀|` -/

/-- APP-1. The rank-one operator `|ψ₀⟩⟨ψ₀| : x ↦ ⟪ψ₀, x⟫ ψ₀`. -/
noncomputable def rankOne (ψ₀ : ℋ) : L ℋ where
  toFun x := inner ℂ ψ₀ x • ψ₀
  map_add' x y := by rw [inner_add_right, add_smul]
  map_smul' c x := by rw [inner_smul_right, smul_smul, RingHom.id_apply]

theorem rankOne_apply (ψ₀ x : ℋ) : rankOne ψ₀ x = inner ℂ ψ₀ x • ψ₀ := rfl

/-- APP-1. `|ψ₀⟩⟨ψ₀| ψ₀ = ψ₀` for a unit vector. -/
theorem rankOne_apply_self {ψ₀ : ℋ} (h : ‖ψ₀‖ = 1) : rankOne ψ₀ ψ₀ = ψ₀ := by
  rw [rankOne_apply, inner_self_eq_norm_sq_to_K, h]
  simp

/-- APP-1. `|ψ₀⟩⟨ψ₀|` is idempotent for a unit vector. -/
theorem rankOne_mul_self {ψ₀ : ℋ} (h : ‖ψ₀‖ = 1) : rankOne ψ₀ * rankOne ψ₀ = rankOne ψ₀ := by
  ext x
  rw [Module.End.mul_apply, rankOne_apply ψ₀ x, map_smul, rankOne_apply_self h]

/-- APP-1. `|ψ₀⟩⟨ψ₀|` is self-adjoint. -/
theorem rankOne_adjoint (ψ₀ : ℋ) : (rankOne ψ₀)† = rankOne ψ₀ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [rankOne_apply, rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

/-- APP-1. `|ψ₀⟩⟨ψ₀|` is an orthogonal projection for a unit vector `ψ₀`. -/
theorem rankOne_isProjective {ψ₀ : ℋ} (h : ‖ψ₀‖ = 1) : IsProjective (rankOne ψ₀) :=
  isProjective_iff_isStarProjection.mpr ⟨rankOne_mul_self h, rankOne_adjoint ψ₀⟩

/-! ### The encoding of amplitude amplification -/

section Setting

variable {U : L ℋ} {G : L ℋ} {ψ₀ ψG : ℋ} {a : ℝ}

/-- APP-1 (GSLW Thm 27). The projected unitary encoding `(U, Π = |ψ₀⟩⟨ψ₀|, Π̃ = Π_good)` of
amplitude amplification, with encoded operator `A = Π_good U |ψ₀⟩⟨ψ₀|`. -/
noncomputable def aaEncoding (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G) (hψ₀ : ‖ψ₀‖ = 1) :
    ProjUnitaryEncoding ℋ where
  U := U
  hU := hU
  P := rankOne ψ₀
  P' := G
  hP := rankOne_isProjective hψ₀
  hP' := hG

variable (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G) (hψ₀ : ‖ψ₀‖ = 1)

@[simp] theorem aaEncoding_U : (aaEncoding hU hG hψ₀).U = U := rfl

@[simp] theorem aaEncoding_P : (aaEncoding hU hG hψ₀).P = rankOne ψ₀ := rfl

@[simp] theorem aaEncoding_P' : (aaEncoding hU hG hψ₀).P' = G := rfl

/-- APP-1. `A ψ₀ = Π_good U ψ₀ = a ψ_G`. -/
theorem aa_encoded_apply (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    (aaEncoding hU hG hψ₀).encoded ψ₀ = (a : ℂ) • ψG := by
  change G (U (rankOne ψ₀ ψ₀)) = _
  rw [rankOne_apply_self hψ₀, hGU]

/-- APP-1. `ψ_G` lies in the good subspace: `Π_good ψ_G = ψ_G` (as `a ≠ 0`). -/
theorem aa_G_ψG (hG : IsProjective G) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    G ψG = ψG := by
  have h1 : G (G (U ψ₀)) = G (U ψ₀) := by rw [← Module.End.mul_apply, hG.mul_self]
  rw [hGU, map_smul] at h1
  exact smul_right_injective ℋ (Complex.ofReal_ne_zero.mpr ha0.ne') h1

/-- APP-1. `⟪U ψ₀, ψ_G⟫ = a` (from `⟪U ψ₀, Π_good ψ_G⟫ = ⟪Π_good U ψ₀, ψ_G⟫ = a ‖ψ_G‖²`). -/
theorem aa_inner_U_ψG (hG : IsProjective G) (hψG : ‖ψG‖ = 1) (ha0 : 0 < a)
    (hGU : G (U ψ₀) = (a : ℂ) • ψG) : inner ℂ (U ψ₀) ψG = (a : ℂ) := by
  calc inner ℂ (U ψ₀) ψG = inner ℂ (U ψ₀) (G ψG) := by rw [aa_G_ψG hG ha0 hGU]
    _ = inner ℂ (G (U ψ₀)) ψG := by
        rw [← LinearMap.adjoint_inner_left G ψG (U ψ₀), hG.adjoint_eq]
    _ = (a : ℂ) := by
        rw [hGU, inner_smul_left, inner_self_eq_norm_sq_to_K, hψG, Complex.conj_ofReal]
        simp

/-- APP-1. `a ≤ 1`: `a = ‖Π_good U ψ₀‖ ≤ ‖U ψ₀‖ = ‖ψ₀‖ = 1`. -/
theorem aa_le_one (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G) (hψ₀ : ‖ψ₀‖ = 1)
    (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) : a ≤ 1 := by
  have h1 : ‖G (U ψ₀)‖ ≤ 1 :=
    calc ‖G (U ψ₀)‖ ≤ ‖U ψ₀‖ := norm_proj_apply_le hG _
      _ = 1 := by rw [norm_unitary_apply hU, hψ₀]
  rwa [hGU, norm_smul, hψG, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] at h1

/-- APP-1 (GSLW Thm 27 ⊂ Thm 26). `(ψ₀, a)` is a singular pair of the encoding: `ψ₀ ∈ ran Π`,
`0 ≤ a ≤ 1`, and `A†A ψ₀ = a² ψ₀` (from `A† (a ψ_G) = a ⟪ψ₀, U† ψ_G⟫ ψ₀ = a² ψ₀`). -/
theorem aa_isSingularPair (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    IsSingularPair (aaEncoding hU hG hψ₀) ψ₀ a where
  P_eq := rankOne_apply_self hψ₀
  nonneg := ha0.le
  le_one := aa_le_one hU hG hψ₀ hψG ha0 hGU
  gram := by
    rw [aa_encoded_apply hU hG hψ₀ hGU, map_smul, ProjUnitaryEncoding.encoded_adjoint,
      aaEncoding_P, aaEncoding_P', aaEncoding_U, Module.End.mul_apply, Module.End.mul_apply,
      aa_G_ψG hG ha0 hGU, rankOne_apply, LinearMap.adjoint_inner_right,
      aa_inner_U_ψG hG hψG ha0 hGU, smul_smul, sq]

/-- APP-1. The left singular vector of the pair `(ψ₀, a)` is `ψ_G`: `lvOf E ψ₀ a = A ψ₀ / a`. -/
theorem aa_lvOf (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    lvOf (aaEncoding hU hG hψ₀) ψ₀ a = ψG := by
  rw [lvOf_of_ne_zero _ ha0.ne', aa_encoded_apply hU hG hψ₀ hGU, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha0.ne'), one_smul]

/-! ### The fixed-point amplitude amplification circuit -/

/-- APP-1. The certified phase list has odd length `21`. -/
theorem sign21Phases_odd : Odd ((sign21Phases.map (↑) : List ℝ)).length := by
  rw [List.length_map, sign21Phases_length]
  exact ⟨10, rfl⟩

/-- APP-1 (GSLW Thm 27 circuit). The fixed-point amplitude amplification circuit
`W = lcu2 U_Φ̃ U_{−Φ̃}` on `Anc ℋ`: one ancilla qubit, `Φ̃ = sign21Phases`, `21` queries. It is
the unitary of the general Cor 18 encoding `(aaEncoding …).qsvtReal Φ̃` (`aaCircuit_eq_U`). -/
noncomputable def aaCircuit : L (Anc ℋ) :=
  lcu2 (altSeq (aaEncoding hU hG hψ₀) (sign21Phases.map (↑)))
    (altSeq (aaEncoding hU hG hψ₀) ((sign21Phases.map (↑)).map Neg.neg))

/-- APP-1. `W` is the unitary of the packaged general Cor 18 encoding. -/
theorem aaCircuit_eq_U :
    aaCircuit hU hG hψ₀ = ((aaEncoding hU hG hψ₀).qsvtReal (sign21Phases.map (↑))).U := rfl

/-- APP-1. `W` is unitary. -/
theorem aaCircuit_mem_unitary : aaCircuit hU hG hψ₀ ∈ unitary (L (Anc ℋ)) := by
  rw [aaCircuit_eq_U]
  exact ProjUnitaryEncoding.hU _

/-- APP-1 (CIRC-3). `W` is the denotation of the gate list `compileQsvtReal Φ̃` with the oracle
`U`: `86` primitive gates, `21` of them oracle calls (`aaCircuit_oracleCount`). -/
theorem aaCircuit_eq_denote :
    aaCircuit hU hG hψ₀ =
      Circuit.denote (aaEncoding hU hG hψ₀) (Circuit.compileQsvtReal (sign21Phases.map (↑))) := by
  rw [Circuit.compileQsvtReal, Circuit.denote_append, Circuit.denote_append,
    Circuit.denote_compileAltSeq_eq_blockDiag, Circuit.denote_singleton, Circuit.Prim.denote_hadA,
    aaCircuit, lcu2]

/-- APP-1 (exact, GSLW Thm 26/27 on the singular pair `(ψ₀, a)`). The good-subspace,
ancilla-`0` block of the circuit maps `ψ₀` *exactly* onto `ψ_G`, scaled by `Re[P_Φ̃](a)`:
```
(⟨0| ⊗ Π_good) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G.
```
-/
theorem fixedPointAA_apply (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG) :
    topLeft (blockDiag G 0 * aaCircuit hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ =
      ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (a : ℂ)) • ψG := by
  have h := topLeft_qsvt_real_apply_singular (aaEncoding hU hG hψ₀)
    (aa_isSingularPair hU hG hψ₀ hψG ha0 hGU) sign21Phases_odd
  rw [aa_lvOf hU hG hψ₀ ha0 hGU, aaEncoding_P, aaEncoding_P'] at h
  rw [aaCircuit]
  exact h

/-- APP-1 (fixed-point property, certified). For every initial good amplitude `a ≥ 0.15`, the
output of the `21`-query circuit in the good subspace is `sign21Scale · ψ_G ≈ 0.8924 ψ_G` up to
an error of norm at most `10⁻¹² + 0.0236`, independently of `a`:
```
‖(⟨0| ⊗ Π_good) W (|0⟩ ⊗ ψ₀) − c ψ_G‖ ≤ 10⁻¹² + 0.0236,    c = sign21Scale.
```
-/
theorem fixedPointAA_bound (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG)
    (ha : 0.15 ≤ a) :
    ‖topLeft (blockDiag G 0 * aaCircuit hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ -
        (sign21Scale : ℂ) • ψG‖ ≤ sign21Eps + 0.0236 := by
  rw [fixedPointAA_apply hU hG hψ₀ hψG ha0 hGU, ← sub_smul, norm_smul, hψG, mul_one]
  exact sign21_rePoly_sub_scale_le a ⟨ha, aa_le_one hU hG hψ₀ hψG ha0 hGU⟩

/-- APP-1. The ancilla-`0`, good-subspace component of the full output state `W (|0⟩ ⊗ ψ₀)` is
the `(0,0)`-block image of `ψ₀`, embedded in the ancilla-`0` branch:
`(|0⟩⟨0| ⊗ Π_good) W (|0⟩ ⊗ ψ₀) = |0⟩ ⊗ ((⟨0| ⊗ Π_good) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀)`. -/
theorem fixedPointAA_state :
    blockDiag G 0 (aaCircuit hU hG hψ₀ (inl ψ₀)) =
      inl (topLeft (blockDiag G 0 * aaCircuit hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀) := by
  have h0 : blockDiag (rankOne ψ₀) 0 (inl ψ₀) = inl ψ₀ := by
    rw [blockDiag, block_apply_inl, rankOne_apply_self hψ₀, LinearMap.zero_apply, map_zero,
      add_zero]
  rw [topLeft_apply, Module.End.mul_apply, Module.End.mul_apply, h0, blockDiag, fst_block,
    block_apply]
  simp only [LinearMap.zero_apply, add_zero, map_zero]

/-- APP-1 (success amplitude). After one run of the `21`-query circuit on `|0⟩ ⊗ ψ₀`, the norm
of the ancilla-`0`, good-subspace component is at least `0.869`, for every initial amplitude
`a ≥ 0.15` (so the success probability is at least `0.869² ≈ 0.755`, against `a² ≥ 0.0225`
initially); from the plateau certificate `sign21_plateau` and the phase certificate. -/
theorem fixedPointAA_amplitude (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG)
    (ha : 0.15 ≤ a) :
    0.869 ≤ ‖blockDiag G 0 (aaCircuit hU hG hψ₀ (inl ψ₀))‖ := by
  have ha1 : a ≤ 1 := aa_le_one hU hG hψ₀ hψG ha0 hGU
  rw [fixedPointAA_state hU hG hψ₀, norm_inl, fixedPointAA_apply hU hG hψ₀ hψG ha0 hGU, norm_smul,
    hψG, mul_one]
  have h1 := sign21_rePoly_bound a ⟨by linarith, ha1⟩
  have h2 : 0.8692 ≤ ‖sign21.toPoly.eval (a : ℂ)‖ := by
    rw [PolyQ.norm_eval_toPoly]
    exact (sign21_plateau a ⟨ha, ha1⟩).1.trans (le_abs_self _)
  have h3 := norm_le_norm_add_norm_sub ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (a : ℂ))
    (sign21.toPoly.eval (a : ℂ))
  have hε : ((sign21Eps : ℚ) : ℝ) ≤ 0.0001 := by
    rw [sign21Eps]
    norm_num
  linarith

end Setting

/-! ### Resources (GSLW Lemma 19 / Cor 18, IR-2) -/

/-- APP-1. The circuit makes `21` oracle calls (`U` or `U†`): one per certified phase. -/
theorem aaCircuit_oracleCount :
    Circuit.oracleCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) = 21 := by
  rw [Circuit.oracleCount_compileQsvtReal, List.length_map, sign21Phases_length]

/-- APP-1. `86 = 4 · 21 + 2` primitive gates in all (one ancilla qubit). -/
theorem aaCircuit_length : (Circuit.compileQsvtReal (sign21Phases.map (↑))).length = 86 := by
  rw [Circuit.length_compileQsvtReal, List.length_map, sign21Phases_length]

end QSVT.Examples
