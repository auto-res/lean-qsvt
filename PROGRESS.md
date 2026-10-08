# PROGRESS

進捗ログ（新しいものを上に）．計画は [00note/plan.md](00note/plan.md)，仕様 ID は
[00note/formal-spec.md](00note/formal-spec.md) を参照．

## 2026-10-08 — Phase 0: プロジェクト骨組みの作成

### 環境
- Lean ツールチェーン: `leanprover/lean4:v4.34.1`（`lean-toolchain` に固定）．
- Mathlib: `leanprover-community/mathlib` タグ `v4.34.1`
  （commit `d13f23b723b8a846827a245b89c10fc7d3f11612`）．`lake-manifest.json` に固定．
- `lakefile.toml`: パッケージ `lean-qsvt`，`defaultTargets = ["QSVT"]`，
  `relaxedAutoImplicit = false`，`weak.linter.mathlibStandardSet = true`，
  `pp.unicode.fun = true`，`maxSynthPendingDepth = 3`，
  header linter のライセンス行を MIT に設定（`weak.linter.style.header.license`）．
  ライブラリ `QSVT`（`QSVT/`）と テストライブラリ `QSVTTest`（`test/`，`testDriver`）．
- `.gitignore`: `.lake/`, `*.olean`, `.DS_Store`, `site/`, `__pycache__/`．

### ビルド状況（ローカル，macOS）
- `lake update`: 273 s（Mathlib + 依存 8 パッケージの clone．post-update hook で
  `~/.cache/mathlib` から 8907 ファイルを展開，約 40 s）．
- `lake exe cache get`: 6 s（ダウンロード 0 件，すべてローカルキャッシュ済）．
- `lake build`: 成功，21 s（1967 ジョブ，Mathlib は全てキャッシュ）．
- `lake test`: 成功，8 s．
- Mathlib をソースからビルドしていない．

### 追加したモジュール
- `QSVT.lean` — ルート（全モジュールを import）．
- `QSVT/QSP/Conventions.lean`（QSP-1）— `namespace QSVT.QSP`:
  `M₂`, `Rref`, `phaseZ`, `seqR`, `Wrot`, `seqW` の定義と補題
  `seqR_nil`, `seqR_cons`（simp），`phaseZ_mul_phaseZ`, `phaseZ_zero`,
  `phaseZ_conjTranspose`, `phaseZ_neg_mul_phaseZ`, `phaseZ_mul_phaseZ_neg`,
  `phaseZ_mem_unitaryGroup`, `Rref_conjTranspose`, `Rref_mul_Rref`,
  `Rref_mem_unitaryGroup`, `seqR_mem_unitaryGroup`．**sorry なし**．
- `QSVT/Polynomial/Parity.lean`（POLY-1, POLY-2）— `namespace QSVT.Poly`:
  `IsEven`, `IsOdd`, `evenPart`, `oddPart`（係数 `Finsupp` の `filter` で定義），
  `coeff_evenPart`, `coeff_oddPart`（simp），`evenPart_add_oddPart`,
  `isEven_evenPart`, `isOdd_oddPart`，一意性 `evenPart_eq_of_add`, `oddPart_eq_of_add`，
  `IsEven.evenPart_eq`, `IsOdd.oddPart_eq`．**sorry なし**．
- `test/QSVTTest.lean` — `example`/`#guard` による回帰テストと，
  `#guard_msgs in #print axioms` による公理監査（標準 3 公理のみ）．

### CI
- `.github/workflows/ci.yml`: `leanprover/lean-action`（sha 固定）で
  `use-mathlib-cache: true`, `build: true`, `test: true`, `lint: false`．
  push / pull_request（全ブランチ）で実行．
- ジョブ `no-sorry`: `QSVT/` 以下の `sorry` を grep して検出．当面は
  `continue-on-error: true`（開発初期の sorry を許容）．sorry-free が定着したら false に戻す．

### Mathlib v4.34.1 で気づいた API メモ
- `AddMonoidAlgebra` は構造体（`ofCoeff :: coeff : M →₀ R`）になっており，
  `Polynomial.coeff : R[X] → ℕ →₀ R`．多項式の係数フィルタは
  `⟨⟨P.toFinsupp.coeff.filter p⟩⟩` と書く．
- `Mathlib.Algebra.Polynomial.Degree.Definitions` は消滅（`Degree/Defs.lean` 等に分割）．
- `Mathlib.Data.Complex.Basic` は deprecated → `Mathlib.Basic.Complex.Basic`．
- `if_pos`/`if_neg` は deprecated → `ite_eq_left`/`ite_eq_right`．
- `Matrix.Notation`（`!![...]`, `Matrix.mul_fin_two`）は `Mathlib.LinearAlgebra.Matrix.Notation`．

### 次のアクション
- QSP-2（規約変換 `Wrot = i • phaseZ (-π/4) * Rref * phaseZ (π/4)`）と
  QSP-3（`qspPoly` と評価定理 `seqR_eval`）の定義ファイル・定理ファイルを分けて追加．
- POLY-3（`sqrtPart`，偶多項式 `= R.comp (X^2)`）．
- lean-quantum 依存可否の調査（`00note/survey.md`）．
