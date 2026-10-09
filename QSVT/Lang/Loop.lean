/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.Notation

/-!
# Classical loops around QSVT programs (LANG-2, APP-5)

The *loop combinators* of the language layer. By design decision D7 of the plan, the core IR is
purely unitary: quantum data never branches classically, and every loop of a QSVT algorithm is a
loop of the *meta-language* (Lean), i.e. a Lean recursion that builds or runs surface programs
`QSVT.Lang.ExprQ`. This module provides the two shapes of such loops and their cost theorems:

* **Nested QSVT** (`iterate`, `qsvtIter`): `qsvtIter Φ k = qsvt[Φ] (qsvt[Φ] (⋯ U₀))` applies the
  same real-part QSVT step `k` times, the output encoding of one step being the oracle of the
  next (GSLW Lemma 53 / SVT-7 iterated). The implemented polynomial is the `k`-fold composition
  `compIter (Re[P_Φ̃]) k = Re[P_Φ̃] ∘ ⋯ ∘ Re[P_Φ̃]` (`spec_toExpr_qsvtIter`), the degree and the
  query count are `|Φ| ^ k` (`queriesQ_qsvtIter`, `degreeBoundQ_qsvtIter`), the ancilla dimension
  is `2 ^ k` (`ancillaDimQ_qsvtIter`), there is no subnormalisation (`scaleQ_qsvtIter`), and the
  correctness theorem `base_qsvtIter` is an instance of `baseQ_eq`.
* **Sweeps over classical parameters** (`totalQueries`, `maxAncillaDim`): a list of programs
  `progs : List ExprQ` (typically `xs.map progOf` for a parameter list `xs`) run one after the
  other; the total query count is the sum (`totalQueries_map`, bounded by
  `totalQueries_le : totalQueries ps ≤ ps.length * B` when every program uses at most `B`
  queries, exact in `totalQueries_eq`), and the ancilla register needed is the largest one
  (`ancillaDimQ_le_maxAncillaDim`).

## Measurement and post-selection (D7)

Repeat-until-success and post-selection loops are *not* quantum control flow in this language:
measurement is confined to the top-level `run`, and a loop "run the circuit, measure the ancilla,
retry on failure" is modelled classically as repeated runs of the *same* program. Its cost is
`runs × queriesQ p` (`totalQueries_replicate`), and with success probability `s` per run the
expected number of oracle queries is `queriesQ p / s` (`expectedQueries`; no probability theory
is formalised here, the quantity is just the bookkeeping constant). The quantum part of every
run carries its own correctness theorem `baseQ_eq`.

## Mathlib API used

`Function.iterate_succ_apply'`, `Polynomial.iterate_comp_eval`, `Polynomial.natDegree_comp_le`,
`Polynomial.natDegree_X_le`, `List.sum_le_length_nsmul`, `List.sum_eq_length_nsmul`,
`List.forall_mem_map`, `List.sum_replicate`, `div_mul_cancel₀`, `le_div_iff₀`.
-/

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- APP-5. The `k`-fold composition of a polynomial with itself: `compIter p 0 = X` and
`compIter p (k + 1) = p.comp (compIter p k)`, so `compIter p k = p ∘ ⋯ ∘ p` (`k` copies). It is
the spec of the nested QSVT program `qsvtIter` (`spec_toExpr_qsvtIter`). -/
noncomputable def compIter (p : R[X]) : ℕ → R[X]
  | 0 => X
  | k + 1 => p.comp (compIter p k)

@[simp] theorem compIter_zero (p : R[X]) : compIter p 0 = X := rfl

@[simp] theorem compIter_succ (p : R[X]) (k : ℕ) : compIter p (k + 1) = p.comp (compIter p k) :=
  rfl

theorem compIter_one (p : R[X]) : compIter p 1 = p := by
  rw [compIter_succ, compIter_zero, comp_X]

/-- APP-5. `compIter p k` is Mathlib's iterate `p.comp^[k] X`. -/
theorem compIter_eq_iterate (p : R[X]) (k : ℕ) : compIter p k = p.comp^[k] X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [compIter_succ, ih, Function.iterate_succ_apply']

/-- APP-5 (degree). `deg (compIter p k) ≤ (deg p) ^ k`. -/
theorem natDegree_compIter_le (p : R[X]) (k : ℕ) :
    (compIter p k).natDegree ≤ p.natDegree ^ k := by
  induction k with
  | zero => exact natDegree_X_le.trans_eq (pow_zero _).symm
  | succ k ih =>
    rw [compIter_succ, pow_succ']
    exact natDegree_comp_le.trans (Nat.mul_le_mul_left _ ih)

end Semiring

/-- APP-5 (evaluation). `(compIter p k).eval x = p.eval (p.eval (⋯ (p.eval x)))`: the value of the
composed polynomial is the `k`-fold iterate of the scalar map `x ↦ p.eval x`. -/
theorem eval_compIter {R : Type*} [CommSemiring R] (p : R[X]) (k : ℕ) (x : R) :
    (compIter p k).eval x = (fun y => p.eval y)^[k] x := by
  rw [compIter_eq_iterate, iterate_comp_eval, eval_X]

end Polynomial

namespace QSVT.Lang

open QSVT.IR QSVT.QSP QSVT.SVT Polynomial

/-! ### Nested QSVT: the classical `for` loop of the language -/

/-- LANG-2. The `k`-fold application of a program transformer: `iterate 0 f e = e` and
`iterate (k + 1) f e = f (iterate k f e)`. This is the classical `for` loop of the language (D7):
the loop counter lives in Lean, the quantum data in the program `e`. -/
def iterate : ℕ → (ExprQ → ExprQ) → ExprQ → ExprQ
  | 0, _, e => e
  | k + 1, f, e => f (iterate k f e)

@[simp] theorem iterate_zero (f : ExprQ → ExprQ) (e : ExprQ) : iterate 0 f e = e := rfl

@[simp] theorem iterate_succ (k : ℕ) (f : ExprQ → ExprQ) (e : ExprQ) :
    iterate (k + 1) f e = f (iterate k f e) := rfl

/-- LANG-2. `iterate k f e` is the function iterate `f^[k] e`. -/
theorem iterate_eq_nat_iterate (k : ℕ) (f : ExprQ → ExprQ) (e : ExprQ) :
    iterate k f e = f^[k] e := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, ih, Function.iterate_succ_apply']

/-- APP-5 (b of the plan: "QSVT of a QSVT"). The nested QSVT program
`qsvtIter Φ k = qsvt[Φ] (qsvt[Φ] (⋯ U₀))` with `k` steps: the encoding output by one real-part
QSVT step is the oracle of the next (GSLW Lemma 53, SVT-7 iterated). -/
def qsvtIter (Φ : List ℚ) (k : ℕ) : ExprQ := iterate k (ExprQ.qsvt Φ) U₀

@[simp] theorem qsvtIter_zero (Φ : List ℚ) : qsvtIter Φ 0 = U₀ := rfl

@[simp] theorem qsvtIter_succ (Φ : List ℚ) (k : ℕ) :
    qsvtIter Φ (k + 1) = qsvt[Φ] qsvtIter Φ k := rfl

/-- APP-5 (cost). `k` nested QSVT steps with `|Φ|` phases use `|Φ| ^ k` oracle queries: the
degree of a composition is the product of the degrees. -/
theorem queriesQ_qsvtIter (Φ : List ℚ) : ∀ k : ℕ, queriesQ (qsvtIter Φ k) = Φ.length ^ k
  | 0 => by rw [qsvtIter_zero, queriesQ, pow_zero]
  | k + 1 => by rw [qsvtIter_succ, queriesQ, queriesQ_qsvtIter Φ k, pow_succ']

/-- APP-5 (cost). `k` nested QSVT steps use `k` ancilla qubits (`ancillaDim = 2 ^ k`). -/
theorem ancillaDimQ_qsvtIter (Φ : List ℚ) : ∀ k : ℕ, ancillaDimQ (qsvtIter Φ k) = 2 ^ k
  | 0 => by rw [qsvtIter_zero, ancillaDimQ, pow_zero]
  | k + 1 => by rw [qsvtIter_succ, ancillaDimQ, ancillaDimQ_qsvtIter Φ k, pow_succ']

/-- APP-5 (degree bound). `deg (spec (qsvtIter Φ k)) ≤ |Φ| ^ k` (`natDegree_spec_toExpr_le`). -/
theorem degreeBoundQ_qsvtIter (Φ : List ℚ) : ∀ k : ℕ, degreeBoundQ (qsvtIter Φ k) = Φ.length ^ k
  | 0 => by rw [qsvtIter_zero, degreeBoundQ, pow_zero]
  | k + 1 => by rw [qsvtIter_succ, degreeBoundQ, degreeBoundQ_qsvtIter Φ k, pow_succ']

/-- APP-5. QSVT steps are exact: a nested QSVT program has no subnormalisation. -/
theorem scaleQ_qsvtIter (Φ : List ℚ) : ∀ k : ℕ, scaleQ (qsvtIter Φ k) = 1
  | 0 => rfl
  | _ + 1 => rfl

/-- APP-5. A nested QSVT program is always well scaled (no Chebyshev-LCU node). -/
theorem wellScaledQ_qsvtIter (Φ : List ℚ) : ∀ k : ℕ, wellScaledQ (qsvtIter Φ k) = true
  | 0 => rfl
  | k + 1 => by rw [qsvtIter_succ, wellScaledQ, wellScaledQ_qsvtIter Φ k]

/-- LANG-2. For a program without subnormalisation (`scaleQ e = 1`) the encoded polynomial
`normSpec` is the spec itself. -/
theorem normSpec_toExpr_of_scaleQ_eq_one {e : ExprQ} (h : scaleQ e = 1) :
    normSpec (toExpr e) = spec (toExpr e) := by
  rw [normSpec, scaleQ_eq, h, Rat.cast_one, Complex.ofReal_one, inv_one, C_1, one_mul]

/-- APP-5 (semantics of the loop). The polynomial implemented by `k` nested QSVT steps is the
`k`-fold composition `Re[P_Φ̃] ∘ ⋯ ∘ Re[P_Φ̃]` of the step polynomial (IR-1 composition rule with
`scale = 1` at every level). -/
theorem spec_toExpr_qsvtIter (Φ : List ℚ) :
    ∀ k : ℕ, spec (toExpr (qsvtIter Φ k)) = compIter (rePoly (qspPoly (Φ.map (↑))).1) k
  | 0 => rfl
  | k + 1 => by
    rw [qsvtIter_succ, toExpr_qsvt, spec_qsvtReal,
      normSpec_toExpr_of_scaleQ_eq_one (scaleQ_qsvtIter Φ k), spec_toExpr_qsvtIter Φ k,
      compIter_succ]

/-- APP-5 (evaluation on an eigenvalue). On a real point `x`, the composed polynomial is the
`k`-fold iterate of the scalar map `x ↦ Re[P_Φ̃](x)`. -/
theorem eval_spec_toExpr_qsvtIter (Φ : List ℚ) (k : ℕ) (x : ℂ) :
    (spec (toExpr (qsvtIter Φ k))).eval x =
      (fun y => (rePoly (qspPoly (Φ.map (↑))).1).eval y)^[k] x := by
  rw [spec_toExpr_qsvtIter, eval_compIter]

section Semantics

open QuantumState QSVT.Encoding

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- APP-5 (correctness of the loop; `baseQ_eq` instantiated). The base block of the denotation
of `qsvtIter Φ k`, with all `k` ancilla qubits in `|0⟩`, is `(Re[P_Φ̃] ∘ ⋯ ∘ Re[P_Φ̃])(A₀) Π`. -/
theorem base_qsvtIter (E₀ : HermitianEncoding ℋ) (Φ : List ℚ) (k : ℕ) :
    compress (toExpr (qsvtIter Φ k)) (denoteQ E₀ (qsvtIter Φ k)).encoded =
      aeval E₀.encoded (compIter (rePoly (qspPoly (Φ.map (↑))).1) k) * E₀.P := by
  rw [baseQ_eq E₀ (wellScaledQ_qsvtIter Φ k), scaleQ_qsvtIter, spec_toExpr_qsvtIter, Rat.cast_one,
    Complex.ofReal_one, inv_one, one_smul]

end Semantics

/-! ### Sweeps over classical parameters -/

/-- LANG-2. The total number of oracle queries of a list of programs run one after the other
(a sweep over a classical parameter list, `ps = xs.map progOf`). -/
def totalQueries (ps : List ExprQ) : ℕ := (ps.map queriesQ).sum

@[simp] theorem totalQueries_nil : totalQueries [] = 0 := rfl

@[simp] theorem totalQueries_cons (p : ExprQ) (ps : List ExprQ) :
    totalQueries (p :: ps) = queriesQ p + totalQueries ps := rfl

/-- LANG-2. The queries of a sweep `xs.map progOf` are `∑_{x ∈ xs} queriesQ (progOf x)`. -/
theorem totalQueries_map {α : Type*} (progOf : α → ExprQ) (xs : List α) :
    totalQueries (xs.map progOf) = (xs.map fun x => queriesQ (progOf x)).sum := by
  rw [totalQueries, List.map_map]
  rfl

/-- LANG-2. Repeated runs of the same program (a repeat-until-success loop, D7) cost
`runs × queries`. -/
theorem totalQueries_replicate (runs : ℕ) (p : ExprQ) :
    totalQueries (List.replicate runs p) = runs * queriesQ p := by
  rw [totalQueries, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- LANG-2 (cost bound of a sweep). If every program of the sweep uses at most `B` queries, the
sweep uses at most `length × B`. -/
theorem totalQueries_le (ps : List ExprQ) (B : ℕ) (h : ∀ p ∈ ps, queriesQ p ≤ B) :
    totalQueries ps ≤ ps.length * B := by
  have := List.sum_le_length_nsmul (ps.map queriesQ) B (List.forall_mem_map.mpr h)
  rwa [List.length_map, smul_eq_mul] at this

/-- LANG-2. If every program of the sweep uses exactly `q` queries, the sweep uses `length × q`. -/
theorem totalQueries_eq (ps : List ExprQ) (q : ℕ) (h : ∀ p ∈ ps, queriesQ p = q) :
    totalQueries ps = ps.length * q := by
  have := List.sum_eq_length_nsmul (ps.map queriesQ) q (List.forall_mem_map.mpr h)
  rwa [List.length_map, smul_eq_mul] at this

/-- LANG-2. The largest ancilla dimension of a list of programs: the register a sweep needs
(`0` for the empty list). -/
def maxAncillaDim (ps : List ExprQ) : ℕ := (ps.map ancillaDimQ).foldr max 0

@[simp] theorem maxAncillaDim_nil : maxAncillaDim [] = 0 := rfl

@[simp] theorem maxAncillaDim_cons (p : ExprQ) (ps : List ExprQ) :
    maxAncillaDim (p :: ps) = max (ancillaDimQ p) (maxAncillaDim ps) := rfl

/-- LANG-2. Every program of a sweep fits in the register of dimension `maxAncillaDim`. -/
theorem ancillaDimQ_le_maxAncillaDim :
    ∀ {ps : List ExprQ} {p : ExprQ}, p ∈ ps → ancillaDimQ p ≤ maxAncillaDim ps
  | [], _, h => by simp at h
  | q :: ps, p, h => by
    rw [maxAncillaDim_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_max_of_le_right (ancillaDimQ_le_maxAncillaDim h)

/-! ### Post-selection bookkeeping (D7) -/

/-- LANG-2 (D7). The expected number of oracle queries of a repeat-until-success loop around the
program `p` whose single run succeeds with probability `successProb`: `queriesQ p / successProb`
(the mean of a geometric number of runs times the queries per run). Measurement is not part of
the language: the loop is a classical loop of the meta-language around runs of `p`, each carrying
`baseQ_eq`. The quantity is meaningful for `0 < successProb ≤ 1` (`expectedQueries_mul`,
`queriesQ_le_expectedQueries`); for `successProb = 0` it is `0` by the convention `x / 0 = 0`. -/
def expectedQueries (p : ExprQ) (successProb : ℚ) : ℚ := queriesQ p / successProb

@[simp] theorem expectedQueries_one (p : ExprQ) : expectedQueries p 1 = queriesQ p := div_one _

/-- LANG-2. `expectedQueries p s × s = queriesQ p` for a positive success probability. -/
theorem expectedQueries_mul (p : ExprQ) {s : ℚ} (hs : 0 < s) :
    expectedQueries p s * s = queriesQ p :=
  div_mul_cancel₀ _ hs.ne'

/-- LANG-2. A repeat-until-success loop costs at least one run. -/
theorem queriesQ_le_expectedQueries (p : ExprQ) {s : ℚ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (queriesQ p : ℚ) ≤ expectedQueries p s := by
  rw [expectedQueries, le_div_iff₀ hs]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hs1

end QSVT.Lang
