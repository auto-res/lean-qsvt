# lean-qsvt

量子特異値変換 (Quantum Singular Value Transformation, QSVT) を Lean 4 + Mathlib で実装し，
その正しさを形式的に証明するプロジェクトです．
QSP（1 qubit の量子信号処理）の構造定理から始め，ブロック符号化・交代列・QSVT 定理
（Gilyén–Su–Low–Wiebe 2019）を経て，位相角パイプラインと回路コンパイラまでを目標とします．

- 計画: [00note/plan.md](00note/plan.md)
- 形式化仕様（定義・定理の ID 一覧）: [00note/formal-spec.md](00note/formal-spec.md)
- 進捗ログ: [PROGRESS.md](PROGRESS.md)

## ディレクトリ

- `QSVT/` — Lean ソース（`QSVT.lean` がルート）
  - `QSVT/Operator/` — 作用素の語彙（`Qudit`, `L ℋ`, `†`, `IsProjective`；lean-quantum から複製）
  - `QSVT/Polynomial/` — parity，偶奇根 `evenRoot`/`oddRoot`，$[-1,1]$ 上 sup ノルム，Chebyshev 級数，
    計算可能な Chebyshev 変換（`ChebQC.ofMonomials`）
  - `QSVT/QSP/` — 1 qubit QSP: 規約（反射 $R$・回転 $W$），多項式再帰と評価定理，Chebyshev 閉形式位相，
    端点公式，規約変換，摂動評価，位相の存在定理
  - `QSVT/Encoding/` — 射影ユニタリ符号化，補助 qubit（直和 `Anc`），$m$ レジスタ（`Reg`），LCU
  - `QSVT/SVT/` — 位相作用素，交代列，固有基底，**QET 定理 `qet`**，実多項式版 `qet_real`，ノルム評価，`svTransform`
  - `QSVT/Pipeline/` — Route A（Chebyshev-LCU による exact なパイプライン，`routeA`）
  - `QSVT/Circuit/` — $C_\Pi\mathrm{NOT}$ ガジェット（GSLW Lemma 19），原始ゲート列と資源数
  - `QSVT/IR/` — 抽象プログラム IR（`Expr`，`denote`，`spec`，健全性，クエリ数）
- `test/` — 回帰テスト（`lake test`）
- `00note/` — 計画・仕様・調査メモ
- `tools/` — 位相角ソルバーなどの外部ツール（untrusted）

## ビルド

Lean ツールチェーンは `lean-toolchain`（`leanprover/lean4:v4.34.1`）に固定しています．
[elan](https://github.com/leanprover/elan) を入れておけば自動で取得されます．

```sh
lake exe cache get   # Mathlib のビルド済みキャッシュを取得（必須．ソースからビルドしない）
lake build           # QSVT ライブラリをビルド
lake test            # test/ 以下のテストをビルド
```

## 主要な結果（すべて sorry なし，公理は `propext`, `Classical.choice`, `Quot.sound` のみ）

| 内容 | 定理 | ファイル |
|---|---|---|
| QSP 評価定理: $\mathrm{seqR}(\Phi,x) = [[P_\Phi, Q_\Phi^*(-x)s],[Q_\Phi s, P_\Phi^*(-x)]]$ | `seqR_eval` | `QSVT/QSP/Structure.lean` |
| Chebyshev の閉形式位相（GSLW Lemma 9） | `seqR_chebPhases_eq` | `QSVT/QSP/Chebyshev.lean` |
| 回転規約↔反射規約（GSLW Cor 8 の対応，式 (16) の符号修正済） | `seqW_eq_seqR`, `seqW_apply_zero_zero_eq` | `QSVT/QSP/Conversion.lean` |
| 位相の存在（GSLW Thm 3 ⇐） | `exists_phases`, `exists_phases_R` | `QSVT/QSP/Existence.lean` |
| **QET**: $P\,U_\Phi\,P = P_\Phi(A)\,P$（Hermitian ブロック符号化，SVD 不要） | `qet`, `qet_chebyshev` | `QSVT/SVT/QET.lean` |
| 実多項式版（GSLW Cor 18）と合成子 `qsvtReal` | `qet_real`, `qsvtReal_encoded` | `QSVT/SVT/RealPoly.lean` |
| $\|p(A)x\| \le \|p\|_\infty \|x\|$ | `norm_aeval_apply_le` | `QSVT/SVT/NormBound.lean` |
| $m$ 項 LCU と Householder 状態準備 | `topLeft_lcu`, `lcu_complex` | `QSVT/Encoding/LCUm.lean` |
| **Route A**: 計算可能な入力多項式 $f$ から $f(A)P/\|c\|_1$ の符号化（exact） | `routeA` | `QSVT/Pipeline/ChebLCU.lean` |
| 位相作用素のガジェット（GSLW Lemma 19）と資源数 | `gadget_eq`, `denote_compileQsvtReal`, `oracleCount_compileAltSeq` | `QSVT/Circuit/` |

### 使い方の例（Route A）

```lean
import QSVT
open QSVT.Pipeline QSVT.Poly

-- 入力: 4x³ − 3x（Gauss 有理係数，次数順）
def l : PolyQC := [(0,0), (-3,0), (0,0), (4,0)]
#eval ChebQC.ofMonomials l        -- [(0,0),(0,0),(0,0),(1,0)]  (= T₃)

-- 任意の Hermitian ブロック符号化 E に対し，`chebLCU E (chebCoeffs l)` は
-- 補助レジスタ上のユニタリで，P で圧縮した左上ブロックが (1/‖c‖₁)·(4A³−3A)·P に一致する:
example (E : QSVT.Encoding.HermitianEncoding ℋ) (h : l1 (chebCoeffs l) ≠ 0) :=
  routeA E l h
```

## 方針

- `relaxedAutoImplicit = false`，Mathlib 標準 linter セットを有効化．
- 公理（`axiom`）は使わない．定義と定理はモジュールを分ける．
- `sorry` は使わない（CI の `no-sorry` ジョブで検出）．各テストファイルで `#print axioms` を監査する．
