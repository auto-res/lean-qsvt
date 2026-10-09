/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.RealPoly

/-!
# The abstract program IR over a Hermitian oracle encoding (formal-spec IR-1)

A *program* `e : Expr` describes a QSVT-style circuit built from one Hermitian oracle
encoding `E₀` of an operator `A₀ = Π U₀ Π` (GSLW Def 11, `QSVT.Encoding.HermitianEncoding`) by
two kinds of steps, each of which turns a Hermitian encoding of some operator `B` into a
Hermitian encoding of a polynomial in `B` on a larger space:

* `qsvtReal Φ e`: the real-part QSVT step of GSLW Cor 18 (SVT-8,
  `HermitianEncoding.qsvtReal`), encoding `Re[P_Φ](B)` with one more ancilla qubit;
* `chebLCU c₀ c e`: the Route A step of CERT-A (`QSVT.Pipeline.chebLCU`), encoding
  `‖c‖₁⁻¹ • (∑ₖ cₖ T_k)(B)` for the *rational* Chebyshev coefficients `c = (c₀, c₁, …)` (the
  first coefficient is a separate argument so that the list is nonempty by construction),
  with an `m = c.length + 1`-dimensional ancilla register.

This module is the *definitional* part of IR-1: the inductive `Expr`, the polynomial `spec e`
and the subnormalisation `scale e` that a program is meant to implement, in the sense that the
operator block-encoded by `e` is `(scale e)⁻¹ • spec e (A₀)` (`normSpec e = C (scale e)⁻¹ * spec e`
is the polynomial actually encoded). The denotation into encodings (`QSVT.IR.Denote`), the
soundness theorem (`QSVT.IR.Sound`) and the cost model (`QSVT.IR.Cost`) are separate modules.

## Composition rule

If the current encoding encodes `g(A₀) = (scale e)⁻¹ • spec e (A₀)` and a step applies the
polynomial `f` to the *encoded* operator, the new program encodes `f(g(A₀))`, i.e. the new spec
is `f.comp (normSpec e)`. The `chebLCU` step additionally subnormalises by `‖c‖₁`; a program is
`WellScaled` when no `chebLCU` node has an all-zero coefficient vector (otherwise the LCU
state preparation is degenerate and the step does not encode `0`).

## Mathlib API used

`Polynomial.comp`, `Polynomial.C`, `Polynomial.X`, `Polynomial.Chebyshev.T`, `Finset.sum`
over `Fin`, `List.get`, `Fin.sum_univ_fun_getElem`.
-/

namespace QSVT.IR

open Polynomial QSVT.QSP QSVT.SVT
-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C`.
open Polynomial.Chebyshev (T)

/-- IR-1. Programs over one Hermitian oracle encoding. `oracle` is the oracle itself;
`qsvtReal Φ e` applies the real-part QSVT step (GSLW Cor 18) with phases `Φ` to the encoding
produced by `e`; `chebLCU c₀ c e` applies the Route A Chebyshev-LCU step (CERT-A) with the
rational coefficients `c₀ :: c` of `∑ₖ cₖ T_k` to the encoding produced by `e`. -/
inductive Expr : Type
  /-- The oracle encoding `E₀` of `A₀`. -/
  | oracle : Expr
  /-- `Re[P_Φ]` of the current encoding (GSLW Cor 18, SVT-8). -/
  | qsvtReal (Φ : List ℝ) (e : Expr) : Expr
  /-- `‖c‖₁⁻¹ ∑ₖ cₖ T_k` of the current encoding via the `(c.length + 1)`-term LCU (CERT-A),
  with coefficients `c₀ :: c`. -/
  | chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) : Expr

/-! ### The Chebyshev data of a `chebLCU` node -/

/-- IR-1. The coefficient vector `(c₀, c₁, …, c_n)` (`n = c.length`) of a `chebLCU c₀ c _`
node, as a function on `Fin (c.length + 1)`. -/
def chebCoeff (c₀ : ℚ) (c : List ℚ) (k : Fin (c.length + 1)) : ℚ := (c₀ :: c).get k

@[simp] theorem chebCoeff_zero (c₀ : ℚ) (c : List ℚ) : chebCoeff c₀ c 0 = c₀ := rfl

@[simp] theorem chebCoeff_succ (c₀ : ℚ) (c : List ℚ) (k : Fin c.length) :
    chebCoeff c₀ c k.succ = c.get k := rfl

/-- IR-1. The coefficient vector of a `chebLCU` node as complex numbers (the input of
`QSVT.Pipeline.chebLCU`). -/
noncomputable def chebCoeffC (c₀ : ℚ) (c : List ℚ) (k : Fin (c.length + 1)) : ℂ :=
  (chebCoeff c₀ c k : ℂ)

/-- IR-1. The coefficients of a `chebLCU` node are real. -/
theorem chebCoeffC_im (c₀ : ℚ) (c : List ℚ) (k : Fin (c.length + 1)) :
    (chebCoeffC c₀ c k).im = 0 :=
  Complex.ratCast_im (chebCoeff c₀ c k)

/-- IR-1. The polynomial `∑ₖ cₖ T_k` of a `chebLCU c₀ c _` node. -/
noncomputable def chebPoly (c₀ : ℚ) (c : List ℚ) : ℂ[X] :=
  ∑ k : Fin (c.length + 1), C (chebCoeffC c₀ c k) * T ℂ (k : ℕ)

/-- IR-1. The subnormalisation `‖c‖₁ = ∑ₖ |cₖ|` of a `chebLCU c₀ c _` node, as a list sum so that
`norm_num [chebScale]` evaluates it on concrete programs (`sum_abs_chebCoeff` is the `Fin` form). -/
noncomputable def chebScale (c₀ : ℚ) (c : List ℚ) : ℝ :=
  ((c₀ :: c).map fun q : ℚ => |(q : ℝ)|).sum

/-- IR-1. `‖c‖₁ = ∑ₖ |cₖ|` as a sum over `Fin (c.length + 1)`. -/
theorem sum_abs_chebCoeff (c₀ : ℚ) (c : List ℚ) :
    ∑ k : Fin (c.length + 1), |(chebCoeff c₀ c k : ℝ)| = chebScale c₀ c :=
  Fin.sum_univ_fun_getElem (c₀ :: c) fun q : ℚ => |(q : ℝ)|

theorem chebScale_nonneg (c₀ : ℚ) (c : List ℚ) : 0 ≤ chebScale c₀ c := by
  rw [← sum_abs_chebCoeff]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-! ### Specification polynomial and subnormalisation -/

/-- IR-1. The subnormalisation `α ≥ 0` of a program: the operator block-encoded by `e` is
`(scale e)⁻¹ • spec e (A₀)`. QSVT steps are exact (`α = 1`); a `chebLCU` step contributes the
`ℓ¹` norm of its coefficients (CERT-A). -/
noncomputable def scale : Expr → ℝ
  | .oracle => 1
  | .qsvtReal _ _ => 1
  | .chebLCU c₀ c _ => chebScale c₀ c

/-- IR-1. The polynomial in the oracle operator `A₀` that a program implements, up to the
subnormalisation `scale e`: `oracle` implements `X`; a step applying the polynomial `f` to the
operator `(scale e)⁻¹ • spec e (A₀)` encoded by `e` implements `f.comp (C (scale e)⁻¹ * spec e)`.
The step polynomials are `Re[P_Φ]` (`qsvtReal`, GSLW Cor 18) and `∑ₖ cₖ T_k` (`chebLCU`). -/
noncomputable def spec : Expr → ℂ[X]
  | .oracle => X
  | .qsvtReal Φ e => (rePoly (qspPoly Φ).1).comp (C ((scale e : ℂ)⁻¹) * spec e)
  | .chebLCU c₀ c e => (chebPoly c₀ c).comp (C ((scale e : ℂ)⁻¹) * spec e)

/-- IR-1. The polynomial actually block-encoded by a program: `normSpec e = C (scale e)⁻¹ * spec e`,
so that the encoded operator is `normSpec e (A₀)`. -/
noncomputable def normSpec (e : Expr) : ℂ[X] := C ((scale e : ℂ)⁻¹) * spec e

@[simp] theorem scale_oracle : scale .oracle = 1 := rfl

@[simp] theorem scale_qsvtReal (Φ : List ℝ) (e : Expr) : scale (.qsvtReal Φ e) = 1 := rfl

@[simp] theorem scale_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    scale (.chebLCU c₀ c e) = chebScale c₀ c := rfl

@[simp] theorem spec_oracle : spec .oracle = X := rfl

theorem spec_qsvtReal (Φ : List ℝ) (e : Expr) :
    spec (.qsvtReal Φ e) = (rePoly (qspPoly Φ).1).comp (normSpec e) := rfl

theorem spec_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    spec (.chebLCU c₀ c e) = (chebPoly c₀ c).comp (normSpec e) := rfl

/-- IR-1. `scale e ≥ 0`. -/
theorem scale_nonneg : ∀ e : Expr, 0 ≤ scale e
  | .oracle => zero_le_one
  | .qsvtReal _ _ => zero_le_one
  | .chebLCU c₀ c _ => chebScale_nonneg c₀ c

@[simp] theorem normSpec_oracle : normSpec .oracle = X := by
  simp [normSpec]

/-- IR-1. A QSVT step is exact: `normSpec (qsvtReal Φ e) = Re[P_Φ].comp (normSpec e)`. -/
@[simp] theorem normSpec_qsvtReal (Φ : List ℝ) (e : Expr) :
    normSpec (.qsvtReal Φ e) = (rePoly (qspPoly Φ).1).comp (normSpec e) := by
  simp [normSpec, spec_qsvtReal]

/-- IR-1. A `chebLCU` step subnormalises by `‖c‖₁`:
`normSpec (chebLCU c₀ c e) = C ‖c‖₁⁻¹ * (∑ₖ cₖ T_k).comp (normSpec e)`. -/
theorem normSpec_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    normSpec (.chebLCU c₀ c e) = C ((chebScale c₀ c : ℂ)⁻¹) * (chebPoly c₀ c).comp (normSpec e) :=
  rfl

/-! ### Well-scaled programs -/

/-- IR-1. A program is *well scaled* when every `chebLCU` node has a nonzero coefficient vector
(`‖c‖₁ ≠ 0`). This is the hypothesis of the soundness theorem: with all-zero coefficients the
LCU state preparation of CERT-A is degenerate and the node does not encode `0`. -/
def WellScaled : Expr → Prop
  | .oracle => True
  | .qsvtReal _ e => WellScaled e
  | .chebLCU c₀ c e => chebScale c₀ c ≠ 0 ∧ WellScaled e

@[simp] theorem wellScaled_oracle : WellScaled .oracle := trivial

@[simp] theorem wellScaled_qsvtReal (Φ : List ℝ) (e : Expr) :
    WellScaled (.qsvtReal Φ e) ↔ WellScaled e := Iff.rfl

@[simp] theorem wellScaled_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    WellScaled (.chebLCU c₀ c e) ↔ chebScale c₀ c ≠ 0 ∧ WellScaled e := Iff.rfl

/-- IR-1. A well-scaled program has `scale e ≠ 0`. -/
theorem scale_ne_zero : ∀ {e : Expr}, WellScaled e → scale e ≠ 0
  | .oracle, _ => one_ne_zero
  | .qsvtReal _ _, _ => one_ne_zero
  | .chebLCU _ _ _, h => h.1

/-- IR-1. A well-scaled program has `scale e > 0`. -/
theorem scale_pos {e : Expr} (h : WellScaled e) : 0 < scale e :=
  lt_of_le_of_ne (scale_nonneg e) (scale_ne_zero h).symm

end QSVT.IR
