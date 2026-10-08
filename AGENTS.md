# Guidance for AI coding agents (lean-qsvt)

Conventions for agents working in this repository. The plan is `00note/plan.md`, the
formal specification with theorem IDs (QSP-3, SVT-7, ...) is `00note/formal-spec.md`,
the dated log is `PROGRESS.md`. Humans follow the same rules.

## Repository and git

- Development branch: `ss`. Never commit to `main`.
- Subagents never run `git add/commit/push`; the parent session commits. Report the list of
  files you created or changed instead.
- One agent per disjoint file set. Never edit a file another agent owns in the same wave.
- `00note/` holds private notes (Japanese). Do not publish it anywhere.

## Build

- Toolchain `leanprover/lean4:v4.34.1`, Mathlib tag `v4.34.1` (pinned in `lake-manifest.json`).
- After changing dependencies: `lake update` then `lake exe cache get`. Never build Mathlib
  from source; if the cache fails, stop and report.
- Iterate with `lake env lean <file>`; finish with `lake build` (whole library, must be
  warning-free under the Mathlib standard linter set) and `lake test`.
- Tests live in `test/QSVTTest.lean`: `#guard`, `#guard_msgs`, and
  `#guard_msgs in #print axioms <main theorem>` audits (expected axioms: `propext`,
  `Classical.choice`, `Quot.sound` only).

## Lean conventions

- `relaxedAutoImplicit = false`: declare every variable.
- No `axiom`. No `sorry` in committed modules unless the parent explicitly allows a listed
  work-in-progress lemma; list every remaining `sorry` in your report.
- Namespaces follow directories: `QSVT.QSP`, `QSVT.Poly`, `QSVT.Encoding`, `QSVT.SVT`,
  `QSVT.IR`, `QSVT.Circuit`, `QSVT.Certificate`.
- Separate definition modules (`Defs`/`Conventions`) from theorem modules so that
  statements can import definitions only.
- Each declaration that realizes a spec item gets a docstring starting with its ID, e.g.
  `/-- QSP-3. Evaluation theorem: ... -/`. Keep GSLW theorem numbers in docstrings.
- Header: the Mathlib header linter expects a copyright block; copy the one in
  `QSVT/QSP/Conventions.lean`.
- Prefer Mathlib names over local re-definitions; put general lemmas that belong upstream
  in `QSVT/ToMathlib/`.

## Mathlib v4.34.1 notes (pitfalls met so far)

- `Polynomial.coeff : R[X] → ℕ →₀ R`; `AddMonoidAlgebra` is a structure (`ofCoeff`).
- `Mathlib.Data.Complex.Basic` is deprecated in favour of `Mathlib.Basic.Complex.Basic`;
  `if_pos`/`if_neg` deprecated in favour of `ite_eq_left`/`ite_eq_right`.
- `!![…]` and `Matrix.mul_fin_two` are in `Mathlib.LinearAlgebra.Matrix.Notation`.
- There is no SVD in Mathlib: use the SVD-free definitions of `00note/formal-spec.md` §4.

## Reporting

- Final report under 40 lines: what was proved, what is left (`sorry` list), files, build
  and test status with timings, API names discovered. Do not paste file contents.
- Append a dated entry to `PROGRESS.md` (Japanese) only when the parent asks for it.
