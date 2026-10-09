/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Lang.Loop
import QSVT.Examples.Sign21RouteB

/-!
# APP-5: programs with loops (QSVT called many times from a classical loop)

Two worked programs in which QSVT is used many times, the loop being a Lean recursion (plan
§3 D7: classical loops live in the meta-language, quantum data never branches classically).

* **(a) Iterated sign amplification** `signIter k = qsvtIter sign21Phases k`: the certified
  Route B sign step of APP-1 (`qsvt[sign21Phases] U₀`, `signBExpr`) applied `k` times, each
  step taking the encoding output by the previous one as its oracle (GSLW Lemma 53 / SVT-7
  iterated). Costs: `21 ^ k` queries, `k` ancilla qubits (`queriesQ_signIter`,
  `ancillaDimQ_signIter`; `441` and `4` for `k = 2`); semantics: the exact identity
  `spec (signIter k) = compIter (Re[P_Φ̃]) k`, i.e. `Re[P_Φ̃] ∘ ⋯ ∘ Re[P_Φ̃]` (`spec_signIter`),
  and the correctness theorem `base_signIter` from `baseQ_eq`.

  *Remark (not proved here).* Let `P = Re[P_Φ̃]`, `c = sign21Scale ≈ 0.8924`,
  `δ = sign21Eps + 0.0236`. The certified plateau bound of APP-1 gives `|P(λ) − c| ≤ δ` for
  `λ ∈ [0.15, 1]`, so `P(λ)` lies again in the plateau region (up to the overshoot `≤ 10⁻¹²` of
  `‖P‖_∞ ≤ 1 + 10⁻¹²`), and applying the bound a second time gives `|P(P(λ)) − c| ≤ δ` up to a
  Lipschitz slack `L · 10⁻¹²` for the overshoot. Note that the composition `P ∘ P` is close to
  `c` (the fixed point of the plateau), not to the product `c · c`. Turning this into a theorem
  needs a Lipschitz bound of `P` near `x = 1`, which the certificates of CERT-B do not provide;
  only the exact `spec` identity and the cost theorems are stated.

* **(b) A binary-search sweep over thresholds** (the skeleton of Lin–Tong style ground-energy
  estimation): a classical bisection `bisect steps lo hi decide` over a threshold `t`, where each
  oracle call `decide t` is realised by running the eigenvalue-window program `progOf t` and
  measuring its ancilla (a classical loop around QSVT calls, D7); the quantum part of each step
  carries its own `baseQ_eq`. The midpoints queried are `visited steps lo hi decide`
  (`length_visited`: exactly `steps` calls), the result stays in `[lo, hi]` (`bisect_mem_Icc`),
  and the oracle-query bill is `groundEnergyQueries ≤ steps × B` when every window program uses
  at most `B` queries (`groundEnergyQueries_le`). The concrete window program
  `windowProg t = qsvt[sign21Phases] cheb[[-t, 1]] U₀` ("shift by `t`, then the certified sign")
  uses `21` queries for every `t` (`queriesQ_windowProg`), so the whole search uses `21 × steps`
  queries (`groundEnergyQueries_windowProg`); its spec is the shifted sign polynomial
  `Re[P_Φ̃]((x − t) / (1 + |t|))` (`spec_windowProg`). The family `sweepPrograms` is the same
  pattern for an explicit list of threshold polynomials given by monomial coefficients.

Everything here is fully proved and depends only on `propext`, `Classical.choice`,
`Quot.sound` (audited in `test/QSVTTest/Loop.lean`).
-/

namespace QSVT.Examples

open QSVT.Lang QSVT.IR QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Encoding QuantumState Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### (a) Iterated sign amplification -/

/-- APP-5 (a). The certified sign step of APP-1 applied `k` times:
`signIter k = qsvt[sign21Phases] (⋯ (qsvt[sign21Phases] U₀))`. -/
def signIter (k : ℕ) : ExprQ := qsvtIter sign21Phases k

/-- APP-5 (a). One iteration is the Route B sign program of APP-1. -/
theorem toExpr_signIter_one : toExpr (signIter 1) = signBExpr := rfl

/-- APP-5 (a). `k` iterations use `21 ^ k` oracle queries. -/
theorem queriesQ_signIter (k : ℕ) : queriesQ (signIter k) = 21 ^ k := by
  rw [signIter, queriesQ_qsvtIter, sign21Phases_length]

/-- APP-5 (a). Two iterations use `441 = 21²` queries. -/
theorem queriesQ_signIter_two : queriesQ (signIter 2) = 441 := by
  rw [queriesQ_signIter]; norm_num

/-- APP-5 (a). `k` iterations use `k` ancilla qubits. -/
theorem ancillaDimQ_signIter (k : ℕ) : ancillaDimQ (signIter k) = 2 ^ k :=
  ancillaDimQ_qsvtIter _ _

/-- APP-5 (a). Two iterations use two ancilla qubits (`ancillaDim = 4`). -/
theorem ancillaDimQ_signIter_two : ancillaDimQ (signIter 2) = 4 := by
  rw [ancillaDimQ_signIter]; norm_num

/-- APP-5 (a). `deg (spec (signIter k)) ≤ 21 ^ k`. -/
theorem degreeBoundQ_signIter (k : ℕ) : degreeBoundQ (signIter k) = 21 ^ k := by
  rw [signIter, degreeBoundQ_qsvtIter, sign21Phases_length]

/-- APP-5 (a, semantics). The polynomial implemented by `k` iterations is the `k`-fold
composition of the APP-1 polynomial `spec signBExpr = Re[P_Φ̃]` with itself. -/
theorem spec_signIter (k : ℕ) : spec (toExpr (signIter k)) = compIter (spec signBExpr) k := by
  rw [signIter, spec_toExpr_qsvtIter, spec_signBExpr]

/-- APP-5 (a). Two iterations implement `Re[P_Φ̃] ∘ Re[P_Φ̃]` exactly. -/
theorem spec_signIter_two :
    spec (toExpr (signIter 2)) = (spec signBExpr).comp (spec signBExpr) := by
  rw [spec_signIter, compIter_succ, compIter_one]

/-- APP-5 (a, correctness; `baseQ_eq`). The base block of `signIter k` is
`(Re[P_Φ̃] ∘ ⋯ ∘ Re[P_Φ̃])(A₀) Π`. -/
theorem base_signIter (E₀ : HermitianEncoding ℋ) (k : ℕ) :
    compress (toExpr (signIter k)) (denoteQ E₀ (signIter k)).encoded =
      aeval E₀.encoded (compIter (spec signBExpr) k) * E₀.P := by
  rw [signIter, base_qsvtIter, spec_signBExpr]

/-! ### (b) A binary-search sweep over thresholds -/

/-- APP-5 (b). The programs of a threshold sweep given by monomial coefficient lists: one Route A
step `poly[l] U₀` per list. -/
def sweepPrograms (ts : List (List ℚ)) : List ExprQ := ts.map fun l => poly[l] U₀

theorem length_sweepPrograms (ts : List (List ℚ)) : (sweepPrograms ts).length = ts.length :=
  List.length_map ..

/-- APP-5 (b). The queries of the sweep are the sum of the Chebyshev-LCU query factors. -/
theorem totalQueries_sweepPrograms (ts : List (List ℚ)) :
    totalQueries (sweepPrograms ts) = (ts.map fun l => chebQueries (chebOfMonomials l)).sum := by
  rw [sweepPrograms, totalQueries_map]
  simp only [queriesQ, mul_one]

/-- APP-5 (b). The midpoint of `[lo, hi]`. -/
def mid (lo hi : ℚ) : ℚ := (lo + hi) / 2

theorem mid_mem_Icc {lo hi : ℚ} (h : lo ≤ hi) : mid lo hi ∈ Set.Icc lo hi :=
  ⟨by rw [mid]; linarith, by rw [mid]; linarith⟩

/-- APP-5 (b). Classical bisection with `steps` oracle calls: `decide t = true` means "the
threshold `t` is above the quantity searched for", so the search continues in `[lo, t]`; the
result is the midpoint of the final interval. In the ground-energy skeleton `decide t` is realised
by running `progOf t` and measuring the ancilla (D7). -/
def bisect : ℕ → ℚ → ℚ → (ℚ → Bool) → ℚ
  | 0, lo, hi, _ => mid lo hi
  | k + 1, lo, hi, d =>
    if d (mid lo hi) then bisect k lo (mid lo hi) d else bisect k (mid lo hi) hi d

/-- APP-5 (b). The result of the bisection stays in the initial interval. -/
theorem bisect_mem_Icc :
    ∀ (k : ℕ) {lo hi : ℚ} (d : ℚ → Bool), lo ≤ hi → bisect k lo hi d ∈ Set.Icc lo hi
  | 0, _, _, _, h => mid_mem_Icc h
  | k + 1, lo, hi, d, h => by
    have hm := mid_mem_Icc h
    rw [bisect]
    split_ifs
    · exact Set.Icc_subset_Icc le_rfl hm.2 (bisect_mem_Icc k d hm.1)
    · exact Set.Icc_subset_Icc hm.1 le_rfl (bisect_mem_Icc k d hm.2)

/-- APP-5 (b). The thresholds queried by `bisect`, in order: the midpoints visited. -/
def visited : ℕ → ℚ → ℚ → (ℚ → Bool) → List ℚ
  | 0, _, _, _ => []
  | k + 1, lo, hi, d =>
    mid lo hi :: (if d (mid lo hi) then visited k lo (mid lo hi) d else visited k (mid lo hi) hi d)

/-- APP-5 (b). The bisection makes exactly `steps` calls of `decide` (one QSVT run each). -/
theorem length_visited : ∀ (k : ℕ) (lo hi : ℚ) (d : ℚ → Bool), (visited k lo hi d).length = k
  | 0, _, _, _ => rfl
  | k + 1, lo, hi, d => by
    rw [visited, List.length_cons]
    split_ifs <;> rw [length_visited]

/-- APP-5 (b). Every threshold queried lies in the initial interval. -/
theorem visited_mem_Icc :
    ∀ (k : ℕ) {lo hi : ℚ} (d : ℚ → Bool), lo ≤ hi → ∀ t ∈ visited k lo hi d, t ∈ Set.Icc lo hi
  | 0, _, _, _, _, _, ht => by simp [visited] at ht
  | k + 1, lo, hi, d, h, t, ht => by
    have hm := mid_mem_Icc h
    rw [visited, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hm
    · split_ifs at ht
      · exact Set.Icc_subset_Icc le_rfl hm.2 (visited_mem_Icc k d hm.1 t ht)
      · exact Set.Icc_subset_Icc hm.1 le_rfl (visited_mem_Icc k d hm.2 t ht)

/-- APP-5 (b). The total oracle-query bill of the ground-energy skeleton: the window program
`progOf t` is run once for every threshold `t` visited by the bisection. -/
def groundEnergyQueries (steps : ℕ) (lo hi : ℚ) (d : ℚ → Bool) (progOf : ℚ → ExprQ) : ℕ :=
  totalQueries ((visited steps lo hi d).map progOf)

/-- APP-5 (b, cost bound). If every window program uses at most `B` queries, the search uses at
most `steps × B`. -/
theorem groundEnergyQueries_le (steps : ℕ) (lo hi : ℚ) (d : ℚ → Bool) (progOf : ℚ → ExprQ)
    (B : ℕ) (h : ∀ t, queriesQ (progOf t) ≤ B) :
    groundEnergyQueries steps lo hi d progOf ≤ steps * B := by
  have := totalQueries_le ((visited steps lo hi d).map progOf) B
    (List.forall_mem_map.mpr fun t _ => h t)
  rwa [List.length_map, length_visited] at this

/-- APP-5 (b). If every window program uses exactly `q` queries, the search uses `steps × q`. -/
theorem groundEnergyQueries_eq (steps : ℕ) (lo hi : ℚ) (d : ℚ → Bool) (progOf : ℚ → ExprQ)
    (q : ℕ) (h : ∀ t, queriesQ (progOf t) = q) :
    groundEnergyQueries steps lo hi d progOf = steps * q := by
  have := totalQueries_eq ((visited steps lo hi d).map progOf) q
    (List.forall_mem_map.mpr fun t _ => h t)
  rwa [List.length_map, length_visited] at this

/-! #### A concrete window program: shift, then the certified sign -/

/-- APP-5 (b). The eigenvalue-window program at threshold `t`: the Chebyshev-LCU step
`cheb[[-t, 1]]` encodes `(x − t) / (1 + |t|)` (coefficients `−t · T₀ + T₁`), and the certified
sign step of APP-1 turns it into `≈ c · sign(x − t)` for eigenvalues at distance
`≥ 0.15 (1 + |t|)` from `t`. -/
def windowProg (t : ℚ) : ExprQ := qsvt[sign21Phases] cheb[[-t, 1]] U₀

/-- APP-5 (b). The shift step has `ℓ¹` norm `|t| + 1`. -/
theorem l1Q_shift (t : ℚ) : l1Q [-t, 1] = |t| + 1 := by
  simp [l1Q]

/-- APP-5 (b). Every window program uses `21` queries: the shift costs one query
(`chebQueries [-t, 1] = 1`) and the sign step `21`. -/
theorem queriesQ_windowProg (t : ℚ) : queriesQ (windowProg t) = 21 := by
  rw [windowProg, queriesQ, queriesQ, queriesQ, sign21Phases_length]
  norm_num [chebQueries]

/-- APP-5 (b). Every window program uses a `4`-dimensional ancilla (two qubits). -/
theorem ancillaDimQ_windowProg (t : ℚ) : ancillaDimQ (windowProg t) = 4 := rfl

/-- APP-5 (b). `deg (spec (windowProg t)) ≤ 21`. -/
theorem degreeBoundQ_windowProg (t : ℚ) : degreeBoundQ (windowProg t) = 21 := by
  rw [windowProg, degreeBoundQ, degreeBoundQ, degreeBoundQ, sign21Phases_length]
  rfl

/-- APP-5 (b). The window program is well scaled for every `t` (`|t| + 1 ≠ 0`). -/
theorem wellScaledQ_windowProg (t : ℚ) : wellScaledQ (windowProg t) = true := by
  simp only [windowProg, wellScaledQ, l1Q_shift, Bool.and_true, decide_eq_true_eq]
  positivity

/-- APP-5 (b). The shift step implements `X − t`. -/
theorem spec_shift (t : ℚ) : spec (toExpr (cheb[[-t, 1]] U₀)) = X - C (t : ℂ) := by
  rw [toExpr_cheb, toExpr_oracle, chebNode, spec_chebLCU, normSpec_oracle, comp_X, List.headD_cons,
    List.tail_cons]
  change ∑ k : Fin 2, C (chebCoeffC (-t) [1] k) * Polynomial.Chebyshev.T ℂ (k : ℕ) = _
  have h0 : chebCoeffC (-t) [1] 0 = ((-t : ℚ) : ℂ) := rfl
  have h1 : chebCoeffC (-t) [1] 1 = ((1 : ℚ) : ℂ) := rfl
  rw [Fin.sum_univ_two, h0, h1]
  simp [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, neg_add_eq_sub]

/-- APP-5 (b, semantics). The window program implements the shifted sign polynomial
`Re[P_Φ̃]((x − t) / (1 + |t|))`. -/
theorem spec_windowProg (t : ℚ) :
    spec (toExpr (windowProg t)) =
      (spec signBExpr).comp (C (((|t| + 1 : ℚ) : ℂ)⁻¹) * (X - C (t : ℂ))) := by
  rw [windowProg, toExpr_qsvt, spec_qsvtReal, normSpec, scaleQ_eq, spec_shift, spec_signBExpr,
    scaleQ, l1Q_shift, Complex.ofReal_ratCast]

/-- APP-5 (b). The whole bisection with the window programs uses `21 × steps` oracle queries. -/
theorem groundEnergyQueries_windowProg (steps : ℕ) (lo hi : ℚ) (d : ℚ → Bool) :
    groundEnergyQueries steps lo hi d windowProg = steps * 21 :=
  groundEnergyQueries_eq steps lo hi d windowProg 21 queriesQ_windowProg

end QSVT.Examples
