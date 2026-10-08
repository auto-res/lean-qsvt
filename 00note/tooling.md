# 開発支援ツールの選定

- 作成日: 2026-10-08．prompt.md の「必要に応じて LeanArchitect などを利用．今回は形式化が目的ではないので別のツールがよいかも」への回答．
- 方針: 本プロジェクトは「定理の形式化」(L0–L1) と「言語・コンパイラ・数値証明書」(L2–L4) の二層構造なので，層ごとに道具を分ける．

## 採用（Phase 0 で導入済み）

| 用途 | ツール | 状態 |
|---|---|---|
| ビルド・キャッシュ | `lake` + Mathlib cache（`lake exe cache get`） | 導入済．初回 `lake update` 273 s，以後 `lake build` 10–20 s |
| CI | `leanprover/lean-action`（Mathlib cache 有効，build + test，lint off）＋ `no-sorry` ジョブ | `.github/workflows/ci.yml` |
| テスト | `lake test`（`test/QSVTTest.lean`）: `#guard`, `#guard_msgs`, `#print axioms` 監査 | 導入済 |
| 作業規約 | `AGENTS.md`（subagent 向け），`PROGRESS.md`（日付付きログ） | 導入済 |
| 数値検算（untrusted） | Python（numpy/sympy，pyqsp または QSPPACK）: `tools/phases/` | Agent B が整備中 |

## 条件付き採用（後続フェーズ）

| 用途 | ツール | 導入時期・条件 |
|---|---|---|
| 定理の依存グラフ・blueprint | **LeanArchitect**（`@[blueprint]` 注釈）+ leanblueprint | Phase 2a で SVT 層の定理が固まった時点で，L0–L1 の定理モジュールにのみ注釈．L2–L4（IR・回路・証明書）には付けない．Lean v4.34.1 用タグが無い（v4.34.0 まで）ため，互換性を確認してから |
| API ドキュメント | `doc-gen4` | Phase 4（IR のコンビネータが公開 API になる時点） |
| 言語マニュアル | Verso（`verso-*` のテンプレートが手元にある） | Phase 7（DSL の表面構文が決まってから） |
| 性質ベーステスト | `plausible`（Mathlib 経由で利用可） | Phase 3（証明書検査器）と Phase 5（回路 `denote`）の計算可能部分に |
| 検証付き区間演算 | LeanCert（第一候補）/ girving/interval | Phase 3 Route B．採否は `survey.md` §A の結果で決定 |
| 回路の数値照合 | Qiskit（状態ベクトル）と `denote` の比較スクリプト | Phase 5 |

## 不採用

| ツール | 理由 |
|---|---|
| Comparator（テンプレートの challenge/solution 方式） | 論文の定理を sorry 付きで再掲する方式は「言語＋コンパイラ」の検証には合わない．代替として `#print axioms` 監査と `compile_correct` のインスタンス化テストで担保 |
| LeanArchitect を全層に適用 | 形式化以外の層（IR・回路・ツール）には blueprint の意味が薄く，注釈コストだけ増える |
