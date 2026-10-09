/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import LeanCert.Core.IntervalRat.Taylor
import QSVT.Certificate.ChebC

/-!
# Kernel-checkable certificates for QSP phase lists (formal-spec CERT-B, part 2)

Given rational phases `Φ̃ : List ℚ` (the output of a numerical phase solver, converted to the
reflection convention), a real rational target `t : List ℚ` in the Chebyshev basis
(`∑ₖ tₖ Tₖ`) and a tolerance `ε : ℚ`, the Boolean `check Φ̃ t ε n` runs the QSP recursion
(QSP-3) in interval arithmetic on Chebyshev coefficient lists and compares the resulting
`ℓ¹` bound on `P_Φ̃ − ∑ₖ tₖ Tₖ` with `ε`.  It is a closed computation over `ℚ`, so the Lean
kernel evaluates it with `decide +kernel`, and `check_sound` turns `check Φ̃ t ε n = true` into
`‖P_Φ̃(x) − ∑ₖ tₖ Tₖ(x)‖ ≤ ε` on `[-1, 1]` (and `supNorm_sound` into a `supNorm` bound).
`checkRe`/`checkRe_sound` do the same for the real part `Re P_Φ̃`, which is what phase solvers
(QSPPACK, pyqsp) actually fit; `Re P_Φ̃` is the polynomial realised by GSLW Cor 18 (SVT-8,
`rePoly`).

## Layers

* `CI` : rectangular complex intervals `re + im i` with LeanCert's `IntervalRat` (rational
  endpoints) as components, membership `z ∈ w := z.re ∈ w.re ∧ z.im ∈ w.im`, operations
  `add`, `neg`, `mul`, `scale q`, `ofRat`, the unit complex `expI φ n` (enclosing `e^{iφ}` by
  LeanCert's `cosComputable`/`sinComputable`, Taylor depth `n`), and the bounds `absBound`
  (`‖z‖ ≤ absBound w`) and `reBound` (`|Re z| ≤ reBound w`).  Soundness lemmas `mem_*` from
  LeanCert's `IntervalRat.mem_add/mem_sub/mem_neg/mem_mul/mem_scale/mem_singleton`,
  `mem_cosComputable`, `mem_sinComputable`, `abs_le_maxAbs`.
* `ChebI := List CI` : interval Chebyshev lists mirroring `ChebC` operation by operation
  (`addI`, `smulI`, `scaleI`, `negI`, `mulXI`, `oneSubXSqI`, `stepI`, `qspChebI`).
* `ListMem c l := List.Forall₂ (· ∈ ·) c l` : the enclosure relation between an exact list
  `c : ChebC` and an interval list `l : ChebI`; `listMem_*` for every operation, culminating in
  `listMem_qspChebI : ListMem (qspChebC (Φ̃.map (↑))).1 (qspChebI n Φ̃).1` (and `.2`).
* `errBound l t`, `errBoundRe l t` : the computable `ℓ¹` bounds on the coefficient differences,
  `check`, `checkRe`, and the soundness theorems `check_sound` (explicit `∑ₖ tₖ Tₖ`),
  `check_sound_target`, `supNorm_sound`, `checkRe_sound` (real part embedded in `ℂ`, matching
  `eval_rePoly_ofReal` of SVT-8) and `checkRe_sound_real` (real-valued form).

## Trust story

`check` is a plain Boolean function; `check_sound` is an ordinary theorem.  For a concrete
instance, `check Φ̃ t ε n = true` is proved by `decide +kernel`, so the only trusted component is
the Lean kernel (no `Lean.ofReduceBool`); `#print axioms` lists `propext`, `Classical.choice`,
`Quot.sound` only.  Coefficient growth is exact rational arithmetic; no rounding is performed, so
the cost grows with the degree and the Taylor depth (see the timings in
`test/QSVTTest/PhaseCheck.lean`).
-/

namespace QSVT.Certificate

open Polynomial
open Polynomial.Chebyshev (T)
open QSVT.Poly QSVT.QSP
open LeanCert.Core

/-! ### Complex intervals -/

/-- CERT-B. A rectangular complex interval `re + im i` with rational endpoints. -/
structure CI where
  /-- The interval of the real part. -/
  re : IntervalRat
  /-- The interval of the imaginary part. -/
  im : IntervalRat
  deriving Repr, DecidableEq

namespace CI

/-- CERT-B. `z ∈ w` iff `Re z ∈ w.re` and `Im z ∈ w.im`. -/
instance : Membership ℂ CI := ⟨fun w z => z.re ∈ w.re ∧ z.im ∈ w.im⟩

theorem mem_def (z : ℂ) (w : CI) : z ∈ w ↔ z.re ∈ w.re ∧ z.im ∈ w.im := Iff.rfl

/-- CERT-B. The point interval of a rational. -/
def ofRat (q : ℚ) : CI := ⟨IntervalRat.singleton q, IntervalRat.singleton 0⟩

/-- CERT-B. Componentwise addition. -/
def add (w v : CI) : CI := ⟨IntervalRat.add w.re v.re, IntervalRat.add w.im v.im⟩

/-- CERT-B. Componentwise negation. -/
def neg (w : CI) : CI := ⟨IntervalRat.neg w.re, IntervalRat.neg w.im⟩

/-- CERT-B. Complex multiplication `(a + b i)(c + d i) = (ac - bd) + (ad + bc) i` in interval
arithmetic. -/
def mul (w v : CI) : CI :=
  ⟨IntervalRat.sub (IntervalRat.mul w.re v.re) (IntervalRat.mul w.im v.im),
    IntervalRat.add (IntervalRat.mul w.re v.im) (IntervalRat.mul w.im v.re)⟩

/-- CERT-B. Scaling by a rational. -/
def scale (q : ℚ) (w : CI) : CI := ⟨IntervalRat.scale q w.re, IntervalRat.scale q w.im⟩

/-- CERT-B. An upper bound `max |lo| |hi|` of `|Re|` plus the same for `|Im|`, hence of the
modulus. -/
def absBound (w : CI) : ℚ := IntervalRat.maxAbs w.re + IntervalRat.maxAbs w.im

/-- CERT-B. An upper bound of `|Re|`. -/
def reBound (w : CI) : ℚ := IntervalRat.maxAbs w.re

/-- CERT-B. An enclosure of `e^{iφ} = cos φ + i sin φ` for rational `φ`, by LeanCert's Taylor
enclosures of depth `n`. -/
def expI (φ : ℚ) (n : ℕ) : CI :=
  ⟨IntervalRat.cosComputable (IntervalRat.singleton φ) n,
    IntervalRat.sinComputable (IntervalRat.singleton φ) n⟩

theorem mem_ofRat (q : ℚ) : (q : ℂ) ∈ ofRat q := by
  have h0 : (0 : ℝ) ∈ IntervalRat.singleton 0 := by simpa using IntervalRat.mem_singleton 0
  rw [mem_def, Complex.ratCast_re, Complex.ratCast_im]
  exact ⟨IntervalRat.mem_singleton q, h0⟩

theorem mem_ofRat_zero : (0 : ℂ) ∈ ofRat 0 := by simpa using mem_ofRat 0

theorem mem_ofRat_one : (1 : ℂ) ∈ ofRat 1 := by simpa using mem_ofRat 1

theorem mem_add {z v : ℂ} {w u : CI} (hz : z ∈ w) (hv : v ∈ u) : z + v ∈ add w u := by
  rw [mem_def] at *
  exact ⟨by rw [Complex.add_re]; exact IntervalRat.mem_add hz.1 hv.1,
    by rw [Complex.add_im]; exact IntervalRat.mem_add hz.2 hv.2⟩

theorem mem_neg {z : ℂ} {w : CI} (hz : z ∈ w) : -z ∈ neg w := by
  rw [mem_def] at *
  exact ⟨by rw [Complex.neg_re]; exact IntervalRat.mem_neg hz.1,
    by rw [Complex.neg_im]; exact IntervalRat.mem_neg hz.2⟩

theorem mem_mul {z v : ℂ} {w u : CI} (hz : z ∈ w) (hv : v ∈ u) : z * v ∈ mul w u := by
  rw [mem_def] at *
  exact ⟨by
      rw [Complex.mul_re]
      exact IntervalRat.mem_sub (IntervalRat.mem_mul hz.1 hv.1) (IntervalRat.mem_mul hz.2 hv.2),
    by
      rw [Complex.mul_im]
      exact IntervalRat.mem_add (IntervalRat.mem_mul hz.1 hv.2) (IntervalRat.mem_mul hz.2 hv.1)⟩

theorem mem_scale {z : ℂ} {w : CI} (q : ℚ) (hz : z ∈ w) : (q : ℂ) * z ∈ scale q w := by
  rw [mem_def] at *
  exact ⟨by
      rw [Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
      exact IntervalRat.mem_scale q hz.1,
    by
      rw [Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, add_zero]
      exact IntervalRat.mem_scale q hz.2⟩

/-- CERT-B. `‖z‖ ≤ |Re z| + |Im z| ≤ absBound w` for `z ∈ w`. -/
theorem norm_le_absBound {z : ℂ} {w : CI} (hz : z ∈ w) : ‖z‖ ≤ (absBound w : ℝ) := by
  rw [mem_def] at hz
  rw [absBound, Rat.cast_add]
  exact (Complex.norm_le_abs_re_add_abs_im z).trans
    (add_le_add (IntervalRat.abs_le_maxAbs hz.1) (IntervalRat.abs_le_maxAbs hz.2))

/-- CERT-B. `|Re z| ≤ reBound w` for `z ∈ w`. -/
theorem abs_re_le_reBound {z : ℂ} {w : CI} (hz : z ∈ w) : |z.re| ≤ (reBound w : ℝ) :=
  IntervalRat.abs_le_maxAbs ((mem_def z w).mp hz).1

/-- CERT-B. `e^{iφ} ∈ expI φ n` (LeanCert `mem_cosComputable`, `mem_sinComputable`). -/
theorem mem_expI (φ : ℚ) (n : ℕ) : Complex.exp (Complex.I * ((φ : ℚ) : ℝ)) ∈ expI φ n := by
  rw [mem_def, mul_comm, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨IntervalRat.mem_cosComputable (IntervalRat.mem_singleton φ) n,
    IntervalRat.mem_sinComputable (IntervalRat.mem_singleton φ) n⟩

/-- CERT-B. `e^{-iφ} ∈ expI (-φ) n`. -/
theorem mem_expI_neg (φ : ℚ) (n : ℕ) :
    Complex.exp (-(Complex.I * ((φ : ℚ) : ℝ))) ∈ expI (-φ) n := by
  have h : -(Complex.I * ((φ : ℚ) : ℝ)) = Complex.I * (((-φ : ℚ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h]
  exact mem_expI (-φ) n

end CI

/-! ### Interval Chebyshev lists -/

/-- CERT-B. A Chebyshev coefficient list of complex intervals. -/
abbrev ChebI := List CI

namespace ChebI

/-- CERT-B. Pointwise addition, padding with zeros (mirrors `ChebC.addC`). -/
def addI : ChebI → ChebI → ChebI
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => CI.add a b :: addI l m

/-- CERT-B. Multiplication of every coefficient by a complex interval (mirrors `ChebC.smulC`). -/
def smulI (w : CI) (l : ChebI) : ChebI := l.map (CI.mul w)

/-- CERT-B. Rational scaling of every coefficient (mirrors `ChebC.smulC (q : ℂ)`). -/
def scaleI (q : ℚ) (l : ChebI) : ChebI := l.map (CI.scale q)

/-- CERT-B. Negation of every coefficient (mirrors `ChebC.smulC (-1)`). -/
def negI (l : ChebI) : ChebI := l.map CI.neg

/-- CERT-B. Multiplication by `X` in the Chebyshev basis (mirrors `ChebC.mulX`). -/
def mulXI : ChebI → ChebI
  | [] => []
  | a :: c => addI (CI.ofRat 0 :: a :: scaleI (1 / 2) c) (scaleI (1 / 2) c)

/-- CERT-B. Multiplication by `1 - X²` (mirrors `ChebC.oneSubXSq`). -/
def oneSubXSqI (c : ChebI) : ChebI := addI c (negI (mulXI (mulXI c)))

/-- CERT-B. One QSP step in interval arithmetic (mirrors `ChebC.stepC`); `n` is the Taylor depth
of the `e^{±iφ}` enclosures. -/
def stepI (φ : ℚ) (n : ℕ) (P Q : ChebI) : ChebI × ChebI :=
  (smulI (CI.expI φ n) (addI (mulXI P) (oneSubXSqI Q)),
    smulI (CI.expI (-φ) n) (addI P (negI (mulXI Q))))

/-- CERT-B. The interval QSP recursion (mirrors `ChebC.qspChebC`). -/
def qspChebI (n : ℕ) : List ℚ → ChebI × ChebI
  | [] => ([CI.ofRat 1], [])
  | φ :: Φ => stepI φ n (qspChebI n Φ).1 (qspChebI n Φ).2

/-- CERT-B. The point intervals of a rational coefficient list. -/
def ofRatList (t : List ℚ) : ChebI := t.map CI.ofRat

/-- CERT-B. The computable `ℓ¹` bound `∑ₖ absBound lₖ`. -/
def l1Bound (l : ChebI) : ℚ := (l.map CI.absBound).sum

/-- CERT-B. The computable `ℓ¹` bound on the real parts, `∑ₖ reBound lₖ`. -/
def l1BoundRe (l : ChebI) : ℚ := (l.map CI.reBound).sum

/-- CERT-B. The `ℓ¹` bound on the coefficient differences `lₖ − tₖ`. -/
def errBound (l : ChebI) (t : List ℚ) : ℚ := l1Bound (addI l (negI (ofRatList t)))

/-- CERT-B. The `ℓ¹` bound on the real parts of the coefficient differences `lₖ − tₖ`. -/
def errBoundRe (l : ChebI) (t : List ℚ) : ℚ := l1BoundRe (addI l (negI (ofRatList t)))

end ChebI

/-! ### The enclosure relation -/

/-- CERT-B. `ListMem c l`: the exact list `c` is enclosed coefficientwise by `l` (same length,
`cₖ ∈ lₖ`). -/
abbrev ListMem (c : ChebC) (l : ChebI) : Prop := List.Forall₂ (fun z w => z ∈ w) c l

open ChebC ChebI

theorem listMem_addI {c d : ChebC} {l m : ChebI} (hc : ListMem c l) (hd : ListMem d m) :
    ListMem (addC c d) (addI l m) := by
  induction hc generalizing d m with
  | nil => exact hd
  | cons ha hc ih =>
    cases hd with
    | nil => exact List.Forall₂.cons ha hc
    | cons hb hd => exact List.Forall₂.cons (CI.mem_add ha hb) (ih hd)

theorem listMem_map {f : ℂ → ℂ} {g : CI → CI} (h : ∀ z w, z ∈ w → f z ∈ g w) {c : ChebC}
    {l : ChebI} (hc : ListMem c l) : ListMem (c.map f) (l.map g) := by
  induction hc with
  | nil => exact List.Forall₂.nil
  | cons ha _ ih => exact List.Forall₂.cons (h _ _ ha) ih

theorem listMem_smulI {a : ℂ} {w : CI} (ha : a ∈ w) {c : ChebC} {l : ChebI} (hc : ListMem c l) :
    ListMem (smulC a c) (smulI w l) :=
  listMem_map (fun _ _ hz => CI.mem_mul ha hz) hc

theorem listMem_scaleI (q : ℚ) {c : ChebC} {l : ChebI} (hc : ListMem c l) :
    ListMem (smulC (q : ℂ) c) (scaleI q l) :=
  listMem_map (fun _ _ hz => CI.mem_scale q hz) hc

theorem listMem_negI {c : ChebC} {l : ChebI} (hc : ListMem c l) :
    ListMem (smulC (-1) c) (negI l) :=
  listMem_map (fun _ _ hz => by rw [neg_one_mul]; exact CI.mem_neg hz) hc

theorem listMem_mulXI {c : ChebC} {l : ChebI} (hc : ListMem c l) : ListMem (mulX c) (mulXI l) := by
  cases hc with
  | nil => exact List.Forall₂.nil
  | cons ha hc =>
    exact listMem_addI
      (List.Forall₂.cons CI.mem_ofRat_zero (List.Forall₂.cons ha (listMem_scaleI _ hc)))
      (listMem_scaleI _ hc)

theorem listMem_oneSubXSqI {c : ChebC} {l : ChebI} (hc : ListMem c l) :
    ListMem (oneSubXSq c) (oneSubXSqI l) :=
  listMem_addI hc (listMem_negI (listMem_mulXI (listMem_mulXI hc)))

theorem listMem_stepI (φ : ℚ) (n : ℕ) {P Q : ChebC} {P' Q' : ChebI} (hP : ListMem P P')
    (hQ : ListMem Q Q') :
    ListMem (stepC ((φ : ℚ) : ℝ) P Q).1 (stepI φ n P' Q').1 ∧
      ListMem (stepC ((φ : ℚ) : ℝ) P Q).2 (stepI φ n P' Q').2 :=
  ⟨listMem_smulI (CI.mem_expI φ n) (listMem_addI (listMem_mulXI hP) (listMem_oneSubXSqI hQ)),
    listMem_smulI (CI.mem_expI_neg φ n) (listMem_addI hP (listMem_negI (listMem_mulXI hQ)))⟩

/-- CERT-B. The interval recursion encloses the exact Chebyshev recursion. -/
theorem listMem_qspChebI (n : ℕ) (Φ : List ℚ) :
    ListMem (qspChebC (Φ.map (↑))).1 (qspChebI n Φ).1 ∧
      ListMem (qspChebC (Φ.map (↑))).2 (qspChebI n Φ).2 := by
  induction Φ with
  | nil => exact ⟨List.Forall₂.cons CI.mem_ofRat_one List.Forall₂.nil, List.Forall₂.nil⟩
  | cons φ Φ ih =>
    rw [List.map_cons, qspChebC_cons, qspChebI]
    exact listMem_stepI φ n ih.1 ih.2

theorem listMem_ofRatList (t : List ℚ) :
    ListMem (t.map fun q => ((q : ℚ) : ℂ)) (ofRatList t) := by
  induction t with
  | nil => exact List.Forall₂.nil
  | cons q t ih => exact List.Forall₂.cons (CI.mem_ofRat q) ih

/-! ### From enclosures to `ℓ¹` bounds -/

/-- CERT-B. `l1 c ≤ l1Bound l` for an enclosure `ListMem c l`. -/
theorem l1_le_l1Bound {c : ChebC} {l : ChebI} (h : ListMem c l) : l1 c ≤ (l1Bound l : ℝ) := by
  induction h with
  | nil => simp [l1, l1Bound]
  | cons ha _ ih =>
    simp only [l1, l1Bound, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    exact add_le_add (CI.norm_le_absBound ha) ih

/-- CERT-B. `l1 (reC c) ≤ l1BoundRe l` for an enclosure `ListMem c l`. -/
theorem l1_reC_le_l1BoundRe {c : ChebC} {l : ChebI} (h : ListMem c l) :
    l1 (reC c) ≤ (l1BoundRe l : ℝ) := by
  induction h with
  | nil => simp [l1, l1BoundRe]
  | cons ha _ ih =>
    simp only [l1, l1BoundRe, reC_cons, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    refine add_le_add ?_ ih
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact CI.abs_re_le_reBound ha

/-! ### The checker -/

/-- CERT-B. The certificate checker: the interval QSP recursion with Taylor depth `n` on the
phases `Φ̃`, and the `ℓ¹` bound on `P_Φ̃ − ∑ₖ tₖ Tₖ` compared with `ε`. -/
def check (Φ : List ℚ) (t : List ℚ) (ε : ℚ) (n : ℕ) : Bool :=
  decide (errBound (qspChebI n Φ).1 t ≤ ε)

/-- CERT-B. The real-part checker: the `ℓ¹` bound on `Re P_Φ̃ − ∑ₖ tₖ Tₖ` compared with `ε`. -/
def checkRe (Φ : List ℚ) (t : List ℚ) (ε : ℚ) (n : ℕ) : Bool :=
  decide (errBoundRe (qspChebI n Φ).1 t ≤ ε)

/-- The exact difference list `P_Φ̃ − t` is enclosed by the interval difference list. -/
theorem listMem_diff (n : ℕ) (Φ t : List ℚ) :
    ListMem (addC (qspChebC (Φ.map (↑))).1 (smulC (-1) (t.map fun q => ((q : ℚ) : ℂ))))
      (addI (qspChebI n Φ).1 (negI (ofRatList t))) :=
  listMem_addI (listMem_qspChebI n Φ).1 (listMem_negI (listMem_ofRatList t))

/-- The exact difference list represents `P_Φ̃ − target t`. -/
theorem toPoly_diff (Φ t : List ℚ) :
    toPoly (addC (qspChebC (Φ.map (↑))).1 (smulC (-1) (t.map fun q => ((q : ℚ) : ℂ)))) =
      (qspPoly (Φ.map (↑))).1 - target t := by
  rw [toPoly_addC, toPoly_smulC, (toPoly_qspChebC_fst_snd _).1, target, C_neg, C_1]
  ring

/-- CERT-B. Soundness of `check`, with the target written as `target t`. -/
theorem check_sound_target {Φ t : List ℚ} {ε : ℚ} {n : ℕ} (h : check Φ t ε n = true) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(qspPoly (Φ.map (↑))).1.eval (x : ℂ) - (target t).eval (x : ℂ)‖ ≤ ε := by
  intro x hx
  have hb : ((errBound (qspChebI n Φ).1 t : ℚ) : ℝ) ≤ ε := by
    exact_mod_cast (of_decide_eq_true h : errBound (qspChebI n Φ).1 t ≤ ε)
  have h1 := norm_eval_toPoly_le_l1
    (addC (qspChebC (Φ.map (↑))).1 (smulC (-1) (t.map fun q => ((q : ℚ) : ℂ)))) hx
  rw [toPoly_diff, eval_sub] at h1
  exact h1.trans ((l1_le_l1Bound (listMem_diff n Φ t)).trans hb)

/-- CERT-B. Soundness of the certificate checker: if `check Φ̃ t ε n = true` then
`‖P_Φ̃(x) − ∑ₖ tₖ Tₖ(x)‖ ≤ ε` for all `x ∈ [-1, 1]`, where `P_Φ̃ = (qspPoly Φ̃).1` (QSP-3). -/
theorem check_sound {Φ t : List ℚ} {ε : ℚ} {n : ℕ} (h : check Φ t ε n = true) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(qspPoly (Φ.map (↑))).1.eval (x : ℂ) -
        (∑ k ∈ Finset.range t.length, C ((t.getD k 0 : ℚ) : ℂ) * T ℂ k).eval (x : ℂ)‖ ≤ ε := by
  rw [← target_eq]
  exact check_sound_target h

/-- CERT-B. `supNorm (P_Φ̃ − target t) ≤ ε` from the certificate. -/
theorem supNorm_sound {Φ t : List ℚ} {ε : ℚ} {n : ℕ} (h : check Φ t ε n = true) :
    supNorm ((qspPoly (Φ.map (↑))).1 - target t) ≤ ε :=
  supNorm_le_of_forall fun x hx => by
    rw [eval_sub]
    exact check_sound_target h x hx

/-- CERT-B. Soundness of `checkRe`: if `checkRe Φ̃ t ε n = true` then
`‖Re P_Φ̃(x) − ∑ₖ tₖ Tₖ(x)‖ ≤ ε` for all `x ∈ [-1, 1]` (the real part embedded in `ℂ`, as in
`eval_rePoly_ofReal`). -/
theorem checkRe_sound {Φ t : List ℚ} {ε : ℚ} {n : ℕ} (h : checkRe Φ t ε n = true) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖((((qspPoly (Φ.map (↑))).1.eval (x : ℂ)).re : ℝ) : ℂ) - (target t).eval (x : ℂ)‖ ≤ ε := by
  intro x hx
  have hb : ((errBoundRe (qspChebI n Φ).1 t : ℚ) : ℝ) ≤ ε := by
    exact_mod_cast (of_decide_eq_true h : errBoundRe (qspChebI n Φ).1 t ≤ ε)
  have h1 := norm_eval_toPoly_le_l1
    (reC (addC (qspChebC (Φ.map (↑))).1 (smulC (-1) (t.map fun q => ((q : ℚ) : ℂ))))) hx
  rw [eval_toPoly_reC, toPoly_diff, eval_sub, Complex.sub_re, Complex.ofReal_sub,
    ofReal_re_eval_target] at h1
  exact h1.trans ((l1_reC_le_l1BoundRe (listMem_diff n Φ t)).trans hb)

/-- CERT-B. The real-valued form of `checkRe_sound`:
`|Re P_Φ̃(x) − ∑ₖ tₖ Tₖ(x)| ≤ ε` on `[-1, 1]`. -/
theorem checkRe_sound_real {Φ t : List ℚ} {ε : ℚ} {n : ℕ} (h : checkRe Φ t ε n = true) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |((qspPoly (Φ.map (↑))).1.eval (x : ℂ)).re -
        ∑ k ∈ Finset.range t.length, (t.getD k 0 : ℝ) * (T ℝ k).eval x| ≤ ε := by
  intro x hx
  have h1 := checkRe_sound h x hx
  rw [eval_target_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  exact h1

end QSVT.Certificate
