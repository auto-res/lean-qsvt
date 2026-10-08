# PROGRESS

進捗ログ（新しいものを上に）．計画は [00note/plan.md](00note/plan.md)，仕様 ID は
[00note/formal-spec.md](00note/formal-spec.md) を参照．

## 2026-10-09 — Phase 2a (QET) 完了，Cor 18・LCU・Chebyshev 変換が揃う（M2 達成，M3 組み立て中）

- **SVT-3 `qet`**（`QSVT/SVT/QET.lean`）: $P\,U_\Phi\,P = P_\Phi(A)\,P$ を Hermitian ブロック符号化で証明（SVD 不要，固有ベクトル単位の帰納法）．
  `qspPoly_chebPhases`（$P_{\text{cheb}(d)} = T_d$，無限個の点での一致から多項式の等式）と `qet_chebyshev`．
- SVT-4 `NormBound.lean`（$\|p(A)x\|\le\|p\|_\infty\|x\|$，作用素ノルム版も），SVT-5 `SVTransform.lean`（SVD 不要の `svTransform`，Hermitian で `aeval A p * P` に一致）．
- SVT-8 `RealPoly.lean`: `qet_real`（GSLW Cor 18）と合成子 `HermitianEncoding.qsvtReal`（出力が再び `HermitianEncoding (Anc ℋ)`）．
- ENC-2/3: `Ancilla.lean`/`LCU.lean`（1 補助 qubit = 直和 `WithLp 2 (ℋ × ℋ)`，2 項 LCU），`Register.lean`/`LCUm.lean`
  （$m$ レジスタ = `PiLp 2`，`matOp`/`selectOp`，Householder 状態準備，`lcu_complex`）．
  注: `topLeft` の名前衝突（Ancilla と Register）を `regTopLeft` への改名で解消．パイプ経由のビルド確認で失敗が隠れた反省から，
  以後は `lake build` の終了コードを直接見る．
- POLY-6 `ChebCoeff.lean`: 計算可能な Gauss 有理係数多項式と単項式→Chebyshev 変換（`#eval` 可，`decide +kernel` で検算）．
- 進行中: `Pipeline/ChebLCU.lean`（Route A: `routeA` 定理 = G2 の最初の達成），`QSP/Conversion.lean`，`QSP/Perturb.lean`．
- 規模: Lean 約 6,000 行，全モジュール sorry なし，公理は標準 3 つのみ．`lake build` 増分 6 s．

## 2026-10-08 — Phase 0 完了，Phase 1 (QSP) 完了，Phase 2a (QET) 組み立て中

subagent による並列開発（1 エージェント＝1 ファイル集合，親がコミット）で進めた．
全モジュール sorry なし，公理は標準 3 つのみ（各テストファイルで `#print axioms` 監査）．

### Phase 0（済）
- リポジトリを `auto-res/lean-qsvt` へ移管．開発ブランチ `ss`（`00note/prompt.md` は `ss` のみ）．
- 調査 `00note/survey.md`: LeanCert v4.34.1 採用（kernel 検証の区間演算），lean-quantum は
  v4.34.1 で `QuantumChannel` が壊れるため `QuantumState` 相当を `QSVT/Operator/Basic.lean` に複製，
  Mathlib に SVD 無しを確認．ツール選定は `00note/tooling.md`．
- 数値検算 `tools/phases/`: GSLW 式 (16) の符号誤りを発見（正: $W=i\,e^{-i\pi/4\sigma_z}Re^{-i\pi/4\sigma_z}$），
  反射規約の多項式再帰を確定（$Q$ は左下成分），pyqsp / qsppack の規約を記録．

### Phase 1（済）: `QSVT/QSP/`
- QSP-3 `Poly.lean`, `Structure.lean`: `qspPoly` と評価定理 `seqR_eval`，次数・parity・単位恒等式，`qspPoly_neg`．
- QSP-4 `Chebyshev.lean`: `chebPhases d` で `seqR` の全行列が $[[T_d, U_{d-1}s],[\pm U_{d-1}s, \pm T_d]]$．
- QSP-5 `Endpoints.lean`: $x=\pm1, 0$ の閉形式．

### 多項式層（済）: `QSVT/Polynomial/`
- `Parity.lean`（parity 補題を集約），`SqrtPart.lean`（`evenRoot`/`oddRoot`），`SupNorm.lean`，
  `Chebyshev.lean`（`ChebSeries`，`supNorm_toPoly_le_l1`）．

### Phase 2a（進行中）: `QSVT/Encoding/`, `QSVT/SVT/`
- ENC-1 `Projected.lean`（射影は `P`/`P'`），SVT-2 `PhaseOp.lean`，SVT-1 `AltSeq.lean`．
- SVT-3 部品: `EigenBasis.lean`（ran P 上の固有基底，`ext_of_eigenVec`），`TwoVector.lean`
  （関係式 (R0)–(R5)，`altSeq_apply_eigen`，`proj_altSeq_apply_eigen`）．
  注: Hermitian の場合でも $\psi^\perp$（$U^\dagger$ 側）と $\tilde\psi^\perp$（$U$ 側）は位相だけ異なり得るので両方を使う．
- 進行中: `QET.lean`（`qet`: $P\,U_\Phi\,P = P_\Phi(A)\,P$），`NormBound.lean`（SVT-4），`SVTransform.lean`（SVT-5），
  `Ancilla.lean`/`LCU.lean`（D8: 補助 qubit を直和で表現，2 項 LCU）．

### ビルド
- `lake build` 2775 ジョブ，増分 6 s．`lake test` 8 s．

### 次のアクション
- `qet` 完成後: Cor 18（`SVT-8`，実多項式）を `lcu2` と `qspPoly_neg` で組み立てる．
- Route A（CERT-A）: `ChebSeries` の各 $T_k$ を `chebPhases k` の QET で実装し，$m$ 項 LCU（`PiLp`）で合成．
- IR-1/2: コンビネータとコスト関数．QSP-2 の Lean 化は Route B 着手時．

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
