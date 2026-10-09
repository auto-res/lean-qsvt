/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.IR.Denote

/-!
# Query-cost accounting for IR programs (formal-spec IR-2)

The resource model of a program `e : Expr` (IR-1):

* `queries e`: the number of (controlled) uses of the oracle `U₀`/`U₀†`. A `qsvtReal Φ` step runs
  the alternating phase sequence of length `Φ.length` on the current encoding (GSLW Cor 18 /
  Lemma 19), so it multiplies the count by `Φ.length`; a `chebLCU c₀ c` step runs
  `U_{chebPhases k}` for `k < c.length + 1` in superposition (CERT-A `routeA_queries`), so it
  multiplies the count by `∑_{k ≤ c.length} k = (c.length + 1) c.length / 2`.
* `ancillaDim e`: the dimension of the total ancilla space, `space ℋ e ≅ ℂ^{ancillaDim e} ⊗ ℋ`
  (`finrank_space`): `2` per `qsvtReal` node and `c.length + 1` per `chebLCU` node.

The `simp` lemmas `queries_*` and `ancillaDim_*` reduce the cost of a concrete program to a
numeral (IR-2, "G3"). The degree bound `natDegree_spec_le : (spec e).natDegree ≤ queries e`
is the IR-level form of the QSP degree bound (QSP-3 `natDegree_fst_le`) propagated through
composition.

## Mathlib API used

`Finset.sum_range_succ`, `Finset.sum_range_id`, `Polynomial.natDegree_comp_le`,
`Polynomial.natDegree_C_mul_le`, `Polynomial.natDegree_sum_le_of_forall_le`,
`Polynomial.Chebyshev.natDegree_T`, `Int.natAbs_natCast`, `LinearEquiv.finrank_eq`,
`Module.finrank_prod`, `Module.finrank_pi_fintype`.
-/

namespace QSVT.IR

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Pipeline Polynomial
-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C`.
open Polynomial.Chebyshev (T)

universe u

/-! ### Oracle queries -/

/-- IR-2. The number of uses of the oracle `U₀`/`U₀†` in the circuit of a program: `1` for the
oracle, `×Φ.length` per `qsvtReal Φ` step (GSLW Cor 18), `×∑_{k ≤ c.length} k` per
`chebLCU c₀ c` step (CERT-A). -/
def queries : Expr → ℕ
  | .oracle => 1
  | .qsvtReal Φ e => Φ.length * queries e
  | .chebLCU _ c e => (∑ k ∈ Finset.range (c.length + 1), k) * queries e

@[simp] theorem queries_oracle : queries .oracle = 1 := rfl

@[simp] theorem queries_qsvtReal (Φ : List ℝ) (e : Expr) :
    queries (.qsvtReal Φ e) = Φ.length * queries e := rfl

@[simp] theorem queries_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    queries (.chebLCU c₀ c e) = (∑ k ∈ Finset.range (c.length + 1), k) * queries e := rfl

/-- IR-2. The `chebLCU` factor is CERT-A's `routeA_queries (c.length + 1)`. -/
theorem queries_chebLCU_eq_routeA (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    queries (.chebLCU c₀ c e) = routeA_queries (c.length + 1) * queries e := rfl

/-- IR-2. Closed form of the `chebLCU` factor: `(c.length + 1) c.length / 2` (Gauss sum). -/
theorem queries_chebLCU_eq (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    queries (.chebLCU c₀ c e) = (c.length + 1) * c.length / 2 * queries e := by
  rw [queries_chebLCU_eq_routeA, routeA_queries_eq, Nat.add_sub_cancel]

/-! ### Ancilla dimension -/

/-- IR-2. The dimension of the total ancilla space of a program (`space ℋ e ≅ ℂ^{ancillaDim e} ⊗ ℋ`,
see `finrank_space`): `1` for the oracle, `×2` per `qsvtReal` step, `×(c.length + 1)` per
`chebLCU c₀ c` step. -/
def ancillaDim : Expr → ℕ
  | .oracle => 1
  | .qsvtReal _ e => 2 * ancillaDim e
  | .chebLCU _ c e => (c.length + 1) * ancillaDim e

@[simp] theorem ancillaDim_oracle : ancillaDim .oracle = 1 := rfl

@[simp] theorem ancillaDim_qsvtReal (Φ : List ℝ) (e : Expr) :
    ancillaDim (.qsvtReal Φ e) = 2 * ancillaDim e := rfl

@[simp] theorem ancillaDim_chebLCU (c₀ : ℚ) (c : List ℚ) (e : Expr) :
    ancillaDim (.chebLCU c₀ c e) = (c.length + 1) * ancillaDim e := rfl

theorem ancillaDim_pos : ∀ e : Expr, 0 < ancillaDim e
  | .oracle => Nat.one_pos
  | .qsvtReal _ e => Nat.mul_pos Nat.two_pos (ancillaDim_pos e)
  | .chebLCU _ _ e => Nat.mul_pos (Nat.succ_pos _) (ancillaDim_pos e)

variable {ℋ : Type u} [Qudit ℋ]

/-- IR-2. `dim (space ℋ e) = ancillaDim e · dim ℋ`: `ancillaDim` is the dimension of the ancilla
factor of the denotation space. -/
theorem finrank_space :
    ∀ e : Expr, Module.finrank ℂ (space ℋ e) = ancillaDim e * Module.finrank ℂ ℋ
  | .oracle => (one_mul _).symm
  | .qsvtReal Φ e => by
    change Module.finrank ℂ (Anc (space ℋ e)) = 2 * ancillaDim e * Module.finrank ℂ ℋ
    rw [(WithLp.linearEquiv 2 ℂ (space ℋ e × space ℋ e)).finrank_eq, Module.finrank_prod,
      finrank_space e, ← two_mul, mul_assoc]
  | .chebLCU c₀ c e => by
    change Module.finrank ℂ (Reg (c.length + 1) (space ℋ e)) =
      (c.length + 1) * ancillaDim e * Module.finrank ℂ ℋ
    rw [(WithLp.linearEquiv 2 ℂ (∀ _ : Fin (c.length + 1), space ℋ e)).finrank_eq,
      Module.finrank_pi_fintype, finrank_space e, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_assoc]

/-! ### Degree bound -/

/-- IR-2. The Chebyshev polynomial of a `chebLCU c₀ c` node has degree `≤ c.length`. -/
theorem natDegree_chebPoly_le (c₀ : ℚ) (c : List ℚ) : (chebPoly c₀ c).natDegree ≤ c.length := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  exact Nat.lt_succ_iff.mp k.isLt

/-- IR-2. `n ≤ ∑_{k ≤ n} k`. -/
theorem le_sum_range_succ (n : ℕ) : n ≤ ∑ k ∈ Finset.range (n + 1), k := by
  rw [Finset.sum_range_succ]
  exact Nat.le_add_left n _

/-- IR-2 (degree bound). The specified polynomial of a program has degree at most the number of
oracle queries: `deg (spec e) ≤ queries e` (QSP-3 `natDegree_fst_le` propagated through the
composition rule `natDegree_comp_le`). -/
theorem natDegree_spec_le : ∀ e : Expr, (spec e).natDegree ≤ queries e
  | .oracle => natDegree_X.le
  | .qsvtReal Φ e => by
    rw [spec_qsvtReal, queries_qsvtReal]
    refine natDegree_comp_le.trans (Nat.mul_le_mul ?_ ?_)
    · exact (natDegree_rePoly_le _).trans (natDegree_fst_le Φ)
    · exact (natDegree_C_mul_le _ _).trans (natDegree_spec_le e)
  | .chebLCU c₀ c e => by
    rw [spec_chebLCU, queries_chebLCU]
    refine natDegree_comp_le.trans (Nat.mul_le_mul ?_ ?_)
    · exact (natDegree_chebPoly_le c₀ c).trans (le_sum_range_succ c.length)
    · exact (natDegree_C_mul_le _ _).trans (natDegree_spec_le e)

end QSVT.IR
