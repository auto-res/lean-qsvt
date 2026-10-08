/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.ExprQ
import QSVT.Certificate.Sign21Phases

/-!
# Surface syntax for QSVT programs (LANG-1)

Scoped notations (`open QSVT.Lang` enables them) that make a surface program `QSVT.Lang.ExprQ`
read like a program:

| syntax            | term                | meaning                                        |
|-------------------|---------------------|------------------------------------------------|
| `U₀`              | `ExprQ.oracle`      | the oracle encoding of `A₀`                    |
| `qsvt[Φ] e`       | `ExprQ.qsvt Φ e`    | `Re[P_Φ]` of `e` (GSLW Cor 18), `Φ : List ℚ`   |
| `cheb[c] e`       | `ExprQ.cheb c e`    | `‖c‖₁⁻¹ ∑ₖ cₖ T_k` of `e`, `c : List ℚ`        |
| `poly[l] e`       | `ExprQ.poly l e`    | `‖c‖₁⁻¹ ∑ᵢ lᵢ xⁱ` of `e`, `l : List ℚ`         |

The bracket content is a single term, so a named list works: `qsvt[sign21Phases] U₀` is the
Route B sign program of APP-1 (`QSVT.Examples.signBExpr`), and `poly[[0, -3, 0, 4]] U₀` is the
Route A demo program `chebLCU 0 [0, 0, 1] oracle` for `4x³ − 3x = T₃`. The step notations are
right-nested at precedence `65`: `qsvt[Φ] poly[l] U₀` is `qsvt[Φ] (poly[l] U₀)`.
-/

namespace QSVT.Lang

/-- LANG-1. `U₀` is the oracle program `ExprQ.oracle`. -/
scoped notation "U₀" => ExprQ.oracle

/-- LANG-1. `qsvt[Φ] e` is `ExprQ.qsvt Φ e`: the real-part QSVT step with phases `Φ : List ℚ`
applied to `e`. -/
scoped notation:65 "qsvt[" Φ "] " e:65 => ExprQ.qsvt Φ e

/-- LANG-1. `cheb[c] e` is `ExprQ.cheb c e`: the Chebyshev-LCU step with Chebyshev coefficients
`c : List ℚ` applied to `e`. -/
scoped notation:65 "cheb[" c "] " e:65 => ExprQ.cheb c e

/-- LANG-1. `poly[l] e` is `ExprQ.poly l e`: the Chebyshev-LCU step for the polynomial with
monomial coefficients `l : List ℚ` applied to `e`. -/
scoped notation:65 "poly[" l "] " e:65 => ExprQ.poly l e

/-! ### Examples -/

open QSVT.Certificate in
/-- The Route B sign program of APP-1 in surface syntax. -/
example : ExprQ := qsvt[sign21Phases] U₀

/-- The Route A demo program `4x³ − 3x = T₃` in surface syntax. -/
example : ExprQ := poly[[0, -3, 0, 4]] U₀

/-- The same polynomial by its Chebyshev coefficients. -/
example : ExprQ := cheb[[0, 0, 0, 1]] U₀

/-- Steps nest to the right. -/
example : qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀ =
    ExprQ.qsvt [1 / 2, -1 / 3] (ExprQ.poly [0, -3, 0, 4] ExprQ.oracle) := rfl

end QSVT.Lang
