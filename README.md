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
  - `QSVT/QSP/` — QSP の規約（`Rref`, `phaseZ`, `seqR`, `Wrot`, `seqW`）と補題
  - `QSVT/Polynomial/` — 多項式の偶奇（parity）と偶奇分解
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

## 方針

- `relaxedAutoImplicit = false`，Mathlib 標準 linter セットを有効化．
- 公理（`axiom`）は使わない．定義と定理はモジュールを分ける．
- 開発初期は `sorry` を許容するが，CI の `no-sorry` ジョブで検出する．
