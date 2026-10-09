/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.IR.Sound
import QSVT.IR.Cost

/-!
# The language layer: rational programs and their translation to the IR (LANG-1)

The first slice of the language layer (plan Phase 7, layer L4). A *surface program* `e : ExprQ`
is a computable mirror of the IR `QSVT.IR.Expr` (IR-1) whose data are rational lists, so that it
can be evaluated (`#eval`, `#guard`, the `#qsvt_info` command of `QSVT.Lang.Info`) while its
meaning is fixed by the translation `toExpr : ExprQ → Expr` into the verified IR:

* `oracle` (written `U₀`): the oracle encoding `E₀` of `A₀ = Π U₀ Π`;
* `qsvt Φ e` (written `qsvt[Φ] e`): the real-part QSVT step of GSLW Cor 18 with rational phases
  `Φ`, translated to `qsvtReal (Φ.map (↑))`;
* `cheb c e` (written `cheb[c] e`): the Route A Chebyshev-LCU step with Chebyshev coefficients
  `c = (c₀, c₁, …)` of `∑ₖ cₖ T_k`, translated to `chebLCU c₀ c.tail`; the empty list `cheb [] e`
  is translated to `chebLCU 0 []` (the zero polynomial, never well scaled);
* `poly l e` (written `poly[l] e`): the same step for a real polynomial given in the *monomial*
  basis `l = (l₀, l₁, …)` of `∑ᵢ lᵢ xⁱ`; the Chebyshev coefficients are computed by
  `ChebQC.ofMonomials` (POLY-6, `chebOfMonomials`), which is exact over `ℚ`.

Every cost of the IR has a computable counterpart on `ExprQ` that agrees with it:
`queriesQ_eq` (`queries`), `ancillaDimQ_eq` (`ancillaDim`), `scaleQ_eq` (`scale`, a cast lemma
since the IR scale is a real list sum), `wellScaled_toExpr_iff` (`WellScaled`, as a `Bool`), and
the degree bound `natDegree_spec_toExpr_le : deg (spec (toExpr e)) ≤ degreeBoundQ e`, which is
sharper than IR-2's `natDegree_spec_le` on `chebLCU` nodes (`c.length - 1` instead of the
Gauss sum). The headline theorem `baseQ_eq` restates IR-1 soundness (`base_eq_smul`) for a
surface program: for `wellScaledQ e = true`, the base block of the denotation is
`(scaleQ e)⁻¹ • (spec (toExpr e))(A₀) Π`. Hence every program written in the surface syntax
carries its correctness theorem (`baseQ_eq`) and its cost theorem (`queriesQ_eq`).

## Mathlib API used

`Rat.cast_list_sum`, `Rat.cast_abs`, `Rat.cast_ne_zero`, `List.length_tail`, `List.length_map`,
`Polynomial.natDegree_comp_le`, `Polynomial.natDegree_C_mul_le`.
-/

namespace QSVT.Lang

open QSVT.IR QSVT.Poly Polynomial

/-! ### Surface programs -/

/-- LANG-1. Surface programs over one Hermitian oracle encoding, with rational data. `oracle`
is the oracle `U₀`; `qsvt Φ e` applies the real-part QSVT step with phases `Φ` (GSLW Cor 18);
`cheb c e` applies the Chebyshev-LCU step with Chebyshev coefficients `c` (CERT-A); `poly l e`
applies the Chebyshev-LCU step for the polynomial with monomial coefficients `l`. -/
inductive ExprQ : Type
  /-- The oracle encoding `E₀` of `A₀` (surface syntax `U₀`). -/
  | oracle : ExprQ
  /-- `Re[P_Φ]` of the current encoding (surface syntax `qsvt[Φ] e`). -/
  | qsvt (Φ : List ℚ) (e : ExprQ) : ExprQ
  /-- `‖c‖₁⁻¹ ∑ₖ cₖ T_k` of the current encoding, Chebyshev coefficients `c = (c₀, c₁, …)`
  (surface syntax `cheb[c] e`). -/
  | cheb (c : List ℚ) (e : ExprQ) : ExprQ
  /-- `‖c‖₁⁻¹ ∑ᵢ lᵢ xⁱ` of the current encoding, monomial coefficients `l = (l₀, l₁, …)`,
  `c = chebOfMonomials l` (surface syntax `poly[l] e`). -/
  | poly (l : List ℚ) (e : ExprQ) : ExprQ
  deriving Repr, DecidableEq, Inhabited

/-! ### Coefficient lists -/

/-- LANG-1. The `ℓ¹` norm `∑ₖ |cₖ|` of a rational coefficient list (the subnormalisation of a
Chebyshev-LCU step). -/
def l1Q (c : List ℚ) : ℚ := (c.map fun q : ℚ => |q|).sum

/-- LANG-1. The Chebyshev coefficients of the real polynomial `∑ᵢ lᵢ xⁱ`, computed by the exact
change of basis `ChebQC.ofMonomials` (POLY-6) on the Gaussian rationals `(lᵢ, 0)`. -/
def chebOfMonomials (l : List ℚ) : List ℚ :=
  (ChebQC.ofMonomials (l.map fun q : ℚ => ((q, 0) : QC))).map Prod.fst

/-- LANG-1. The IR node of a Chebyshev coefficient list: `chebLCU c₀ c'` for `c = c₀ :: c'`, and
`chebLCU 0 []` (the zero polynomial) for `c = []`. -/
def chebNode (c : List ℚ) (e : Expr) : Expr := .chebLCU (c.headD 0) c.tail e

/-- LANG-1. The query factor of a Chebyshev-LCU step with `c.length` coefficients:
`∑_{k < c.length} k = c.length (c.length - 1) / 2` (CERT-A `routeA_queries`). -/
def chebQueries (c : List ℚ) : ℕ := c.length * (c.length - 1) / 2

/-- LANG-1. The ancilla register dimension of a Chebyshev-LCU step: `max c.length 1` (the IR node
`chebLCU c₀ c'` has an `(c'.length + 1)`-dimensional register). -/
def chebDim (c : List ℚ) : ℕ := max c.length 1

/-- LANG-1. `((∑ₖ |cₖ| : ℚ) : ℝ) = ∑ₖ |(cₖ : ℝ)|`. -/
theorem l1Q_cast (c : List ℚ) : ((l1Q c : ℚ) : ℝ) = (c.map fun q : ℚ => |(q : ℝ)|).sum := by
  rw [l1Q, Rat.cast_list_sum, List.map_map]
  simp only [Function.comp_def, Rat.cast_abs]

/-- LANG-1. The IR subnormalisation of `chebNode c _` is the cast of `l1Q c`. -/
theorem chebScale_headD_tail (c : List ℚ) : chebScale (c.headD 0) c.tail = (l1Q c : ℝ) := by
  cases c with
  | nil => simp [chebScale, l1Q]
  | cons a c => rw [List.headD_cons, List.tail_cons, chebScale, l1Q_cast]

theorem scale_chebNode (c : List ℚ) (e : Expr) : scale (chebNode c e) = (l1Q c : ℝ) := by
  rw [chebNode, scale_chebLCU, chebScale_headD_tail]

theorem queries_chebNode (c : List ℚ) (e : Expr) :
    queries (chebNode c e) = chebQueries c * queries e := by
  rw [chebNode, queries_chebLCU_eq]
  cases c with
  | nil => simp [chebQueries]
  | cons a c => simp [chebQueries]

theorem ancillaDim_chebNode (c : List ℚ) (e : Expr) :
    ancillaDim (chebNode c e) = chebDim c * ancillaDim e := by
  rw [chebNode, ancillaDim_chebLCU]
  cases c with
  | nil => rfl
  | cons a c =>
    simp only [List.tail_cons, List.length_cons, chebDim]
    congr 1
    omega

theorem wellScaled_chebNode_iff (c : List ℚ) (e : Expr) :
    WellScaled (chebNode c e) ↔ l1Q c ≠ 0 ∧ WellScaled e := by
  rw [chebNode, wellScaled_chebLCU, chebScale_headD_tail, Rat.cast_ne_zero]

/-- LANG-1. The degree of the spec of a Chebyshev-LCU node is at most `(c.length - 1)` times the
degree of the inner spec (`natDegree_chebPoly_le`, `natDegree_comp_le`). -/
theorem natDegree_spec_chebNode_le (c : List ℚ) {e : Expr} {d : ℕ} (h : (spec e).natDegree ≤ d) :
    (spec (chebNode c e)).natDegree ≤ (c.length - 1) * d := by
  rw [chebNode, spec_chebLCU]
  refine natDegree_comp_le.trans (Nat.mul_le_mul ?_ ?_)
  · exact (natDegree_chebPoly_le _ _).trans_eq List.length_tail
  · exact (natDegree_C_mul_le _ _).trans h

/-! ### Translation to the IR -/

/-- LANG-1. The translation of a surface program into the IR (IR-1): `qsvt Φ` is
`qsvtReal (Φ.map (↑))`, `cheb c` is `chebNode c` and `poly l` is `chebNode (chebOfMonomials l)`. -/
noncomputable def toExpr : ExprQ → Expr
  | .oracle => .oracle
  | .qsvt Φ e => .qsvtReal (Φ.map (↑)) (toExpr e)
  | .cheb c e => chebNode c (toExpr e)
  | .poly l e => chebNode (chebOfMonomials l) (toExpr e)

@[simp] theorem toExpr_oracle : toExpr .oracle = .oracle := rfl

@[simp] theorem toExpr_qsvt (Φ : List ℚ) (e : ExprQ) :
    toExpr (.qsvt Φ e) = .qsvtReal (Φ.map (↑)) (toExpr e) := rfl

@[simp] theorem toExpr_cheb (c : List ℚ) (e : ExprQ) : toExpr (.cheb c e) = chebNode c (toExpr e) :=
  rfl

@[simp] theorem toExpr_poly (l : List ℚ) (e : ExprQ) :
    toExpr (.poly l e) = chebNode (chebOfMonomials l) (toExpr e) := rfl

/-! ### Computable costs -/

/-- LANG-1. The number of oracle queries of a surface program (`= queries (toExpr e)`,
`queriesQ_eq`): `1` for the oracle, `×Φ.length` per `qsvt Φ` step, `×∑_{k < c.length} k` per
Chebyshev-LCU step with `c.length` coefficients. -/
def queriesQ : ExprQ → ℕ
  | .oracle => 1
  | .qsvt Φ e => Φ.length * queriesQ e
  | .cheb c e => chebQueries c * queriesQ e
  | .poly l e => chebQueries (chebOfMonomials l) * queriesQ e

/-- LANG-1. The ancilla dimension of a surface program (`= ancillaDim (toExpr e)`,
`ancillaDimQ_eq`): `×2` per `qsvt` step, `×max c.length 1` per Chebyshev-LCU step. -/
def ancillaDimQ : ExprQ → ℕ
  | .oracle => 1
  | .qsvt _ e => 2 * ancillaDimQ e
  | .cheb c e => chebDim c * ancillaDimQ e
  | .poly l e => chebDim (chebOfMonomials l) * ancillaDimQ e

/-- LANG-1. A computable bound on the degree of the implemented polynomial
(`natDegree_spec_toExpr_le`): `1` for the oracle, `×Φ.length` per `qsvt Φ` step (QSP-3),
`×(c.length - 1)` per Chebyshev-LCU step. -/
def degreeBoundQ : ExprQ → ℕ
  | .oracle => 1
  | .qsvt Φ e => Φ.length * degreeBoundQ e
  | .cheb c e => (c.length - 1) * degreeBoundQ e
  | .poly l e => ((chebOfMonomials l).length - 1) * degreeBoundQ e

/-- LANG-1. The subnormalisation of a surface program (`= scale (toExpr e)`, `scaleQ_eq`): `1`
for the oracle and for a `qsvt` step, `‖c‖₁` for a Chebyshev-LCU step. -/
def scaleQ : ExprQ → ℚ
  | .oracle => 1
  | .qsvt _ _ => 1
  | .cheb c _ => l1Q c
  | .poly l _ => l1Q (chebOfMonomials l)

/-- LANG-1. Computable well-scaledness (`WellScaled (toExpr e)`, `wellScaled_toExpr_iff`): every
Chebyshev-LCU node has `‖c‖₁ ≠ 0`. -/
def wellScaledQ : ExprQ → Bool
  | .oracle => true
  | .qsvt _ e => wellScaledQ e
  | .cheb c e => decide (l1Q c ≠ 0) && wellScaledQ e
  | .poly l e => decide (l1Q (chebOfMonomials l) ≠ 0) && wellScaledQ e

/-! ### Agreement with the IR -/

/-- LANG-1 (cost theorem). The IR query count of a surface program is `queriesQ e`. -/
theorem queriesQ_eq : ∀ e : ExprQ, queries (toExpr e) = queriesQ e
  | .oracle => rfl
  | .qsvt Φ e => by rw [toExpr_qsvt, queries_qsvtReal, List.length_map, queriesQ, queriesQ_eq e]
  | .cheb c e => by rw [toExpr_cheb, queries_chebNode, queriesQ, queriesQ_eq e]
  | .poly l e => by rw [toExpr_poly, queries_chebNode, queriesQ, queriesQ_eq e]

/-- LANG-1. The IR ancilla dimension of a surface program is `ancillaDimQ e`. -/
theorem ancillaDimQ_eq : ∀ e : ExprQ, ancillaDim (toExpr e) = ancillaDimQ e
  | .oracle => rfl
  | .qsvt Φ e => by rw [toExpr_qsvt, ancillaDim_qsvtReal, ancillaDimQ, ancillaDimQ_eq e]
  | .cheb c e => by rw [toExpr_cheb, ancillaDim_chebNode, ancillaDimQ, ancillaDimQ_eq e]
  | .poly l e => by rw [toExpr_poly, ancillaDim_chebNode, ancillaDimQ, ancillaDimQ_eq e]

/-- LANG-1 (cast lemma). The IR subnormalisation of a surface program is the cast of `scaleQ e`. -/
theorem scaleQ_eq : ∀ e : ExprQ, scale (toExpr e) = (scaleQ e : ℝ)
  | .oracle => by rw [toExpr_oracle, scale_oracle, scaleQ, Rat.cast_one]
  | .qsvt Φ e => by rw [toExpr_qsvt, scale_qsvtReal, scaleQ, Rat.cast_one]
  | .cheb c e => by rw [toExpr_cheb, scale_chebNode, scaleQ]
  | .poly l e => by rw [toExpr_poly, scale_chebNode, scaleQ]

/-- LANG-1. The IR well-scaledness of a surface program is decided by `wellScaledQ`. -/
theorem wellScaled_toExpr_iff : ∀ e : ExprQ, WellScaled (toExpr e) ↔ wellScaledQ e = true
  | .oracle => by simp [wellScaledQ]
  | .qsvt Φ e => by rw [toExpr_qsvt, wellScaled_qsvtReal, wellScaledQ, wellScaled_toExpr_iff e]
  | .cheb c e => by
    rw [toExpr_cheb, wellScaled_chebNode_iff, wellScaledQ, Bool.and_eq_true, decide_eq_true_eq,
      wellScaled_toExpr_iff e]
  | .poly l e => by
    rw [toExpr_poly, wellScaled_chebNode_iff, wellScaledQ, Bool.and_eq_true, decide_eq_true_eq,
      wellScaled_toExpr_iff e]

/-- LANG-1 (degree bound). The implemented polynomial of a surface program has degree at most
`degreeBoundQ e` (QSP-3 `natDegree_fst_le` and `natDegree_chebPoly_le`, propagated through the
composition rule). -/
theorem natDegree_spec_toExpr_le : ∀ e : ExprQ, (spec (toExpr e)).natDegree ≤ degreeBoundQ e
  | .oracle => natDegree_X.le
  | .qsvt Φ e => by
    rw [toExpr_qsvt, spec_qsvtReal, degreeBoundQ]
    refine natDegree_comp_le.trans (Nat.mul_le_mul ?_ ?_)
    · exact (QSVT.SVT.natDegree_rePoly_le _).trans
        ((QSVT.QSP.natDegree_fst_le _).trans_eq (List.length_map _))
    · exact (natDegree_C_mul_le _ _).trans (natDegree_spec_toExpr_le e)
  | .cheb c e => by
    rw [toExpr_cheb, degreeBoundQ]
    exact natDegree_spec_chebNode_le c (natDegree_spec_toExpr_le e)
  | .poly l e => by
    rw [toExpr_poly, degreeBoundQ]
    exact natDegree_spec_chebNode_le _ (natDegree_spec_toExpr_le e)

/-- LANG-1. The degree bound is also bounded by the query count (IR-2 `natDegree_spec_le`). -/
theorem natDegree_spec_toExpr_le_queriesQ (e : ExprQ) :
    (spec (toExpr e)).natDegree ≤ queriesQ e :=
  (natDegree_spec_le _).trans_eq (queriesQ_eq e)

/-! ### Semantics -/

section Semantics

open QuantumState QSVT.Encoding

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- LANG-1. The denotation of a surface program over the oracle encoding `E₀`: the IR denotation
of its translation (IR-1 `denote`), a Hermitian encoding on `space ℋ (toExpr e)`. -/
noncomputable def denoteQ (E₀ : HermitianEncoding ℋ) (e : ExprQ) :
    HermitianEncoding (space ℋ (toExpr e)) :=
  denote E₀ (toExpr e)

/-- LANG-1 (correctness theorem of a surface program; IR-1 `base_eq_smul` restated). For a
well-scaled program (`wellScaledQ e = true`, decidable), the base block of the denotation, with
all ancillas in `|0⟩`, is `(scaleQ e)⁻¹ • (spec (toExpr e))(A₀) Π`. -/
theorem baseQ_eq (E₀ : HermitianEncoding ℋ) {e : ExprQ} (hw : wellScaledQ e = true) :
    compress (toExpr e) (denoteQ E₀ e).encoded =
      ((scaleQ e : ℝ) : ℂ)⁻¹ • (aeval E₀.encoded (spec (toExpr e)) * E₀.P) := by
  have h := base_eq_smul E₀ ((wellScaled_toExpr_iff e).mpr hw)
  rw [base, scaleQ_eq] at h
  exact h

/-- LANG-1. The dimension of the denotation space is `ancillaDimQ e · dim ℋ` (IR-2
`finrank_space`). -/
theorem finrank_space_toExpr (e : ExprQ) :
    Module.finrank ℂ (space ℋ (toExpr e)) = ancillaDimQ e * Module.finrank ℂ ℋ := by
  rw [finrank_space, ancillaDimQ_eq]

end Semantics

end QSVT.Lang
