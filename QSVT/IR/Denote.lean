/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.IR.Expr
import QSVT.Pipeline.ChebLCU

/-!
# Denotation of IR programs into Hermitian encodings (formal-spec IR-1)

Given a Hermitian oracle encoding `E₀ : HermitianEncoding ℋ` of `A₀`, every program `e : Expr`
denotes a Hermitian encoding `denote E₀ e` on the space `space ℋ e` obtained from `ℋ` by
attaching one ancilla qubit (`Anc`, ENC-2) per `qsvtReal` node and an `m`-dimensional ancilla
register (`Reg m`, ENC-2) per `chebLCU` node. The base block of such an encoding is read off by
`compress e : L (space ℋ e) → L ℋ`, which takes the `(0,0)` block (`topLeft`, `regTopLeft`) at
every level, i.e. projects every ancilla onto `|0⟩` (GSLW Def 43).

## Design point: the projector of the LCU step must include "ancilla = |0⟩"

CERT-A packages the Route A circuit `chebLCU E c` with the projector `regP E = 1 ⊗ Π`
(`chebHermitianEncoding`), whose encoded operator `(1 ⊗ Π) chebLCU (1 ⊗ Π)` has the right
`(0,0)` block but in general nonzero off-diagonal register blocks. Polynomials of such an
operator are *not* determined by its `(0,0)` block, so this packaging is not composable: a
subsequent `qsvtReal` step would see the whole register. The composable packaging is GSLW's
`Π = |0⟩⟨0|^{⊗a} ⊗ I` convention (Def 43): the projector of the LCU output is
`atZero Π = |0⟩⟨0| ⊗ Π` (`chebEnc0`), whose encoded operator is supported on the `(0,0)`
block only (`chebEnc0_encoded`), exactly as the `qsvtReal` output `|0⟩⟨0| ⊗ (Re[P](B) Π)`
(SVT-8 `qsvtReal_encoded`). Both block shapes are closed under polynomials
(`aeval_blockDiag_zero_mul`, `aeval_atZero_mul`), which is what makes the soundness proof of
`QSVT.IR.Sound` go through by induction.

## Contents

* `space ℋ e`, `instance : Qudit (space ℋ e)`.
* `atZero B = |0⟩⟨0| ⊗ B` on `Reg m ℋ` with its algebra (`atZero_mul`, `atZero_add`,
  `atZero_smul`, `atZero_adjoint`, `regTopLeft_atZero`, `atZero_isProjective`,
  `atZero_mul_mul_atZero`).
* `aeval_mul_of_mul_hom`: polynomials commute with an additive, `ℂ`-linear, multiplicative
  (not necessarily unital) map `ι` in the form `aeval (ι B) q * ι P = ι (aeval B q * P)`;
  instances `aeval_blockDiag_zero_mul`, `aeval_atZero_mul`.
* `chebEnc0 E c hc : HermitianEncoding (Reg m ℋ)`, the Route A circuit with projector
  `|0⟩⟨0| ⊗ Π`, and `chebEnc0_encoded`.
* `denote E₀ e`, `denote_P`, `liftP`, `compress`, `compress_add`, `compress_smul`,
  `compress_one`, `l1_chebCoeffC` (`scale` of a `chebLCU` node is CERT-A's `l1`).

## Mathlib API used

`Polynomial.induction_on'`, `Polynomial.aeval_monomial`, `Algebra.algebraMap_eq_smul_one`,
`IsSelfAdjoint.conjugate`, `LinearMap.isSelfAdjoint_iff'`, `Complex.ofReal_ratCast`,
`Complex.norm_real`, `Real.norm_eq_abs`.
-/

namespace QSVT.IR

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Pipeline Polynomial
-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C`.
open Polynomial.Chebyshev (T)

universe u

/-! ### The space of a program -/

/-- IR-1. The Hilbert space on which `denote E₀ e` lives: one ancilla qubit (`Anc`) per
`qsvtReal` node and an ancilla register of dimension `c.length + 1` (`Reg`) per `chebLCU` node. -/
abbrev space (ℋ : Type u) : Expr → Type u
  | .oracle => ℋ
  | .qsvtReal _ e => Anc (space ℋ e)
  | .chebLCU _ c e => Reg (c.length + 1) (space ℋ e)

variable {ℋ : Type u}

theorem space_oracle : space ℋ .oracle = ℋ := rfl

theorem space_qsvtReal (Φ : List ℝ) (e : Expr) : space ℋ (.qsvtReal Φ e) = Anc (space ℋ e) := rfl

theorem space_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    space ℋ (.chebLCU c₀ c e) = Reg (c.length + 1) (space ℋ e) := rfl

variable [Qudit ℋ]

/-- IR-1. `space ℋ e` is again a qudit, by recursion (`instQuditAnc`, `instQuditReg`). -/
noncomputable instance instQuditSpace : (e : Expr) → Qudit (space ℋ e)
  | .oracle => ‹Qudit ℋ›
  | .qsvtReal _ e => @instQuditAnc (space ℋ e) (instQuditSpace e)
  | .chebLCU _ c e => @instQuditReg (space ℋ e) (instQuditSpace e) (c.length + 1)

/-! ### Polynomials of block-supported operators -/

section MulHom

variable {ℋ' : Type u} [Qudit ℋ']

/-- IR-1 (helper). For a map `ι : L ℋ → L ℋ'` that is additive, `ℂ`-linear and multiplicative
(but not necessarily unital, e.g. `B ↦ |0⟩⟨0| ⊗ B`), polynomials pass through `ι` once a factor
`ι P` is present: `aeval (ι B) q * ι P = ι (aeval B q * P)`. -/
theorem aeval_mul_of_mul_hom (ι : L ℋ → L ℋ') (hadd : ∀ B C, ι (B + C) = ι B + ι C)
    (hsmul : ∀ (a : ℂ) (B : L ℋ), ι (a • B) = a • ι B) (hmul : ∀ B C, ι (B * C) = ι B * ι C)
    (B P : L ℋ) (q : ℂ[X]) : aeval (ι B) q * ι P = ι (aeval B q * P) := by
  have hpow : ∀ n : ℕ, ι B ^ n * ι P = ι (B ^ n * P) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
    | succ n ih => rw [pow_succ', mul_assoc, ih, ← hmul, ← mul_assoc, ← pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mul, hp, hq, map_add, add_mul, hadd]
  | monomial n a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hpow,
      hsmul]

end MulHom

/-- IR-1 (helper, `Anc`). `q(|0⟩⟨0| ⊗ B) (|0⟩⟨0| ⊗ P) = |0⟩⟨0| ⊗ (q(B) P)`. -/
theorem aeval_blockDiag_zero_mul (B P : L ℋ) (q : ℂ[X]) :
    aeval (blockDiag B 0) q * blockDiag P 0 = blockDiag (aeval B q * P) 0 :=
  aeval_mul_of_mul_hom (fun B => blockDiag B 0)
    (fun B C => by rw [blockDiag_add, add_zero])
    (fun a B => by rw [blockDiag_smul, smul_zero])
    (fun B C => by rw [blockDiag_mul, mul_zero]) B P q

/-! ### The operator `|0⟩⟨0| ⊗ B` on a register -/

section AtZero

variable {m : ℕ} [NeZero m]

/-- IR-1. The operator `|0⟩⟨0| ⊗ B` on `Reg m ℋ`: `B` on the "ancilla `= |0⟩`" summand and `0`
on the others. For a projection `Π` this is GSLW's projector `|0⟩⟨0| ⊗ Π` (Def 43). -/
noncomputable def atZero (B : L ℋ) : L (Reg m ℋ) := selectOp fun k => if k = 0 then B else 0

variable (B C : L ℋ)

theorem atZero_mul : (atZero B : L (Reg m ℋ)) * atZero C = atZero (B * C) := by
  rw [atZero, atZero, atZero, selectOp_mul]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

theorem atZero_add : (atZero B : L (Reg m ℋ)) + atZero C = atZero (B + C) := by
  rw [atZero, atZero, atZero, ← selectOp_add]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

theorem atZero_smul (a : ℂ) : a • (atZero B : L (Reg m ℋ)) = atZero (a • B) := by
  rw [atZero, atZero, ← selectOp_smul]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

@[simp] theorem atZero_zero : (atZero (0 : L ℋ) : L (Reg m ℋ)) = 0 := by
  rw [atZero, ← selectOp_zero]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

theorem atZero_adjoint : (atZero B : L (Reg m ℋ))† = atZero (B†) := by
  rw [atZero, atZero, selectOp_adjoint]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

@[simp] theorem regTopLeft_atZero : regTopLeft (atZero B : L (Reg m ℋ)) = B := by
  rw [atZero, regTopLeft_selectOp]
  simp

/-- IR-1. `|0⟩⟨0| ⊗ Π` is an orthogonal projection when `Π` is. -/
theorem atZero_isProjective {P : L ℋ} (hP : IsProjective P) :
    IsProjective (atZero P : L (Reg m ℋ)) :=
  isProjective_iff_isStarProjection.mpr
    ⟨show (atZero P : L (Reg m ℋ)) * atZero P = atZero P by rw [atZero_mul, hP.mul_self],
      show (atZero P : L (Reg m ℋ))† = atZero P by rw [atZero_adjoint, hP.adjoint_eq]⟩

/-- `|0⟩⟨0| ⊗ B = (|0⟩⟨0| ⊗ 1)(1 ⊗ B)`. -/
theorem atZero_eq_reg0_mul : (atZero B : L (Reg m ℋ)) = reg0 * selectOp fun _ => B := by
  rw [atZero, reg0, selectOp_mul]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

/-- `|0⟩⟨0| ⊗ B = (1 ⊗ B)(|0⟩⟨0| ⊗ 1)`. -/
theorem atZero_eq_mul_reg0 : (atZero B : L (Reg m ℋ)) = (selectOp fun _ => B) * reg0 := by
  rw [atZero, reg0, selectOp_mul]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [h]

/-- `(|0⟩⟨0| ⊗ P) T (|0⟩⟨0| ⊗ P) = (|0⟩⟨0| ⊗ 1) ((1 ⊗ P) T (1 ⊗ P)) (|0⟩⟨0| ⊗ 1)`. -/
theorem atZero_mul_mul_eq (P : L ℋ) (T : L (Reg m ℋ)) :
    atZero P * T * atZero P =
      reg0 * ((selectOp fun _ => P) * T * selectOp fun _ => P) * reg0 := by
  have h1 : (atZero P : L (Reg m ℋ)) = reg0 * selectOp fun _ => P := atZero_eq_reg0_mul P
  have h2 : (atZero P : L (Reg m ℋ)) = (selectOp fun _ => P) * reg0 := atZero_eq_mul_reg0 P
  calc atZero P * T * atZero P
      = (reg0 * selectOp fun _ => P) * T * ((selectOp fun _ => P) * reg0) := by rw [← h1, ← h2]
    _ = reg0 * ((selectOp fun _ => P) * T * selectOp fun _ => P) * reg0 := by
        simp only [mul_assoc]

/-- IR-1. Compressing by `|0⟩⟨0| ⊗ P` on both sides keeps only `P T₀₀ P` at the `(0,0)` block. -/
theorem atZero_mul_mul_atZero (P : L ℋ) (T : L (Reg m ℋ)) :
    atZero P * T * atZero P = atZero (P * regTopLeft T * P) := by
  rw [atZero_mul_mul_eq, reg0_mul_mul_reg0, regTopLeft_selectOp_const_mul_mul, atZero]

/-- IR-1 (helper, `Reg`). `q(|0⟩⟨0| ⊗ B) (|0⟩⟨0| ⊗ P) = |0⟩⟨0| ⊗ (q(B) P)`. -/
theorem aeval_atZero_mul (P : L ℋ) (q : ℂ[X]) :
    aeval (atZero B : L (Reg m ℋ)) q * atZero P = atZero (aeval B q * P) :=
  aeval_mul_of_mul_hom (fun B : L ℋ => (atZero B : L (Reg m ℋ))) (fun B C => (atZero_add B C).symm)
    (fun a B => (atZero_smul B a).symm) (fun B C => (atZero_mul B C).symm) B P q

end AtZero

/-! ### The LCU step with the projector `|0⟩⟨0| ⊗ Π` -/

section ChebEnc0

variable {m : ℕ} [NeZero m] (E : HermitianEncoding ℋ) (c : Fin m → ℂ)

/-- IR-1 (CERT-A repackaged). The Route A circuit `chebLCU E c` with real coefficients `c`, as
a Hermitian encoding on `Reg m ℋ` whose projector is `|0⟩⟨0| ⊗ Π` (GSLW Def 43) instead of
CERT-A's `1 ⊗ Π`. Its encoded operator is `|0⟩⟨0| ⊗ (‖c‖₁⁻¹ • f(A) Π)` for `f = ∑ₖ cₖ T_k`
(`chebEnc0_encoded`), so that it composes with further steps. -/
noncomputable def chebEnc0 (hc : ∀ k, (c k).im = 0) : HermitianEncoding (Reg m ℋ) where
  U := chebLCU E c
  hU := chebLCU_mem_unitary E c
  P := atZero E.P
  P' := atZero E.P
  hP := atZero_isProjective E.hP
  hP' := atZero_isProjective E.hP
  P'_eq := rfl
  encoded_selfAdjoint := by
    have h : IsSelfAdjoint (regP E * chebLCU E c * regP E) :=
      (chebHermitianEncoding E c hc).encoded_selfAdjoint
    have h' := h.conjugate (reg0 : L (Reg m ℋ))
    rw [LinearMap.star_eq_adjoint, reg0_adjoint] at h'
    rw [atZero_mul_mul_eq]
    exact h'

variable (hc : ∀ k, (c k).im = 0)

@[simp] theorem chebEnc0_U : (chebEnc0 E c hc).U = chebLCU E c := rfl

@[simp] theorem chebEnc0_P : (chebEnc0 E c hc).P = atZero E.P := rfl

@[simp] theorem chebEnc0_P' : (chebEnc0 E c hc).P' = atZero E.P := rfl

/-- IR-1 (CERT-A). The encoded operator of `chebEnc0 E c hc` is supported on the `(0,0)` block:
`|0⟩⟨0| ⊗ (‖c‖₁⁻¹ • (∑ₖ cₖ T_k)(A) Π)`. -/
theorem chebEnc0_encoded (h : l1 c ≠ 0) :
    (chebEnc0 E c hc).encoded =
      atZero (((l1 c : ℂ)⁻¹) • (aeval E.encoded (∑ k, C (c k) * T ℂ (k : ℕ)) * E.P)) := by
  rw [HermitianEncoding.encoded_eq, chebEnc0_P, chebEnc0_U, atZero_mul_mul_atZero,
    ← regTopLeft_selectOp_const_mul_mul, ← regP, regTopLeft_regP_chebLCU_regP E c h]

end ChebEnc0

/-! ### Denotation -/

/-- IR-1. The subnormalisation of a `chebLCU` node is CERT-A's `ℓ¹` norm of its coefficients. -/
theorem l1_chebCoeffC (c₀ : ℚ) (c : List ℚ) : l1 (chebCoeffC c₀ c) = chebScale c₀ c := by
  rw [← sum_abs_chebCoeff]
  simp only [l1, chebCoeffC, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

/-- IR-1. The denotation of a program as a Hermitian encoding on `space ℋ e`: the oracle is
`E₀`; `qsvtReal Φ` is SVT-8's `HermitianEncoding.qsvtReal`; `chebLCU c₀ c` is the Route A
circuit with the projector `|0⟩⟨0| ⊗ Π` (`chebEnc0`). -/
noncomputable def denote (E₀ : HermitianEncoding ℋ) : (e : Expr) → HermitianEncoding (space ℋ e)
  | .oracle => E₀
  | .qsvtReal Φ e => (denote E₀ e).qsvtReal Φ
  | .chebLCU c₀ c e => chebEnc0 (denote E₀ e) (chebCoeffC c₀ c) (chebCoeffC_im c₀ c)

variable (E₀ : HermitianEncoding ℋ)

@[simp] theorem denote_oracle : denote E₀ .oracle = E₀ := rfl

theorem denote_qsvtReal (Φ : List ℝ) (e : Expr) :
    denote E₀ (.qsvtReal Φ e) = (denote E₀ e).qsvtReal Φ := rfl

theorem denote_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    denote E₀ (.chebLCU c₀ c e) =
      chebEnc0 (denote E₀ e) (chebCoeffC c₀ c) (chebCoeffC_im c₀ c) := rfl

/-- IR-1. The projector of `denote E₀ e` is the oracle projector `Π` lifted by
`|0⟩⟨0| ⊗ ·` at every level: `liftP e Π`. -/
noncomputable def liftP : (e : Expr) → L ℋ → L (space ℋ e)
  | .oracle, P => P
  | .qsvtReal _ e, P => blockDiag (liftP e P) 0
  | .chebLCU _ _ e, P => atZero (liftP e P)

/-- IR-1. `(denote E₀ e).P = liftP e E₀.P`: the projector of the denotation is
`|0⟩⟨0|^{⊗a} ⊗ Π` in the sense of GSLW Def 43. -/
theorem denote_P : ∀ e : Expr, (denote E₀ e).P = liftP e E₀.P
  | .oracle => rfl
  | .qsvtReal Φ e => by
    change blockDiag (denote E₀ e).P 0 = blockDiag (liftP e E₀.P) 0
    rw [denote_P e]
  | .chebLCU c₀ c e => by
    change atZero (denote E₀ e).P = atZero (liftP e E₀.P)
    rw [denote_P e]

/-! ### Compression to the base space -/

/-- IR-1. The base block of an operator on `space ℋ e`: take the `(0,0)` block (ancilla `|0⟩`)
at every level, `topLeft` for `Anc` and `regTopLeft` for `Reg` (GSLW Def 43). -/
noncomputable def compress : (e : Expr) → L (space ℋ e) → L ℋ
  | .oracle, T => T
  | .qsvtReal _ e, T => compress e (topLeft (ℋ := space ℋ e) T)
  | .chebLCU _ c e, T => compress e (regTopLeft (m := c.length + 1) T)

@[simp] theorem compress_oracle (T : L ℋ) : compress .oracle T = T := rfl

theorem compress_qsvtReal (Φ : List ℝ) (e : Expr) (T : L (Anc (space ℋ e))) :
    compress (.qsvtReal Φ e) T = compress e (topLeft T) := rfl

theorem compress_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr)
    (T : L (Reg (c.length + 1) (space ℋ e))) :
    compress (.chebLCU c₀ c e) T = compress e (regTopLeft T) := rfl

theorem compress_add : ∀ (e : Expr) (S T : L (space ℋ e)),
    compress e (S + T) = compress e S + compress e T
  | .oracle, _, _ => rfl
  | .qsvtReal Φ e, S, T => by
    rw [compress_qsvtReal, compress_qsvtReal, compress_qsvtReal, topLeft_add, compress_add e]
  | .chebLCU c₀ c e, S, T => by
    rw [compress_chebLCU, compress_chebLCU, compress_chebLCU, regTopLeft_add, compress_add e]

theorem compress_smul : ∀ (e : Expr) (a : ℂ) (T : L (space ℋ e)),
    compress e (a • T) = a • compress e T
  | .oracle, _, _ => rfl
  | .qsvtReal Φ e, a, T => by
    rw [compress_qsvtReal, compress_qsvtReal, topLeft_smul, compress_smul e]
  | .chebLCU c₀ c e, a, T => by
    rw [compress_chebLCU, compress_chebLCU, regTopLeft_smul, compress_smul e]

@[simp] theorem compress_one : ∀ e : Expr, compress e (1 : L (space ℋ e)) = 1
  | .oracle => rfl
  | .qsvtReal Φ e => by rw [compress_qsvtReal, topLeft_one, compress_one e]
  | .chebLCU c₀ c e => by rw [compress_chebLCU, regTopLeft_one, compress_one e]

/-- IR-1. The compression of the lifted projector is the projector itself. -/
@[simp] theorem compress_liftP : ∀ (e : Expr) (P : L ℋ), compress e (liftP e P) = P
  | .oracle, _ => rfl
  | .qsvtReal Φ e, P => by
    rw [compress_qsvtReal, liftP, topLeft_blockDiag, compress_liftP e]
  | .chebLCU c₀ c e, P => by
    rw [compress_chebLCU, liftP, regTopLeft_atZero, compress_liftP e]

/-- IR-1. The compressed projector of the denotation is the oracle projector `Π`. -/
theorem compress_denote_P (e : Expr) : compress e (denote E₀ e).P = E₀.P := by
  rw [denote_P, compress_liftP]

end QSVT.IR
