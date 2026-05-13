# Prompt: relyNoUndo の 2 sorry を閉じる

`DbAppProgramLogic/Transformer/LogStorageExample/TransactionProofs.lean` の以下 2 sorry を閉じてください:

```
TransactionProofs.lean:941  theorem relyNoUndo_R_archive : relyNoUndo R_archive := by sorry
TransactionProofs.lean:945  theorem relyNoUndo_R_select (q : Nat) : relyNoUndo (R_select q) := by sorry
```

`relyNoUndo` 定義 (TransactionProofs.lean:152):
```lean
def relyNoUndo (R : Rely) : Prop :=
  ∀ A B, Logic.MultiStep R A B → Logic.MultiStep R B A → A = B
```

これは `Database = List Row` の **構造的等価** を要求する。

## 前提理解 (paper 1710.09844v2.pdf)

- 用途: `stableIsolation_snapshot_*_of_noUndo` 経由で `IsolationSpec.snapshot.exec/.commit` の
  `Logic.stableIsolation` を導出する (TransactionProofs.lean:155, 166)。
- paper p.27:16 の `stable(R, I_ss)` 議論の Lean 化。論文では reachability/monotonicity を
  implicit に使う、と Logic.lean:135 のコメントにある。

## R / G の定義 (Spec.lean)

```
R_archive  := G_insert ∨ ∃ q, G_select q
R_select q := G_insert ∨ G_archive
```

G_* の中身:
- `G_insert`:  `storageShape oldDb cut next ∧ storageShape newDb cut (next+1) ∧ sameResultRows ∧ ...`
  → **next 厳密 +1, cut 保存, resultRows 保存**
- `G_archive`: `storageShape oldDb cut next ∧ storageShape newDb cut' next ∧ cut ≤ cut' ∧ ...`
  → **next 保存, cut 単調増, resultRows 保存**
- `G_select q`: `sameStorageShape ∧ sameResultRowsExcept q ∧ ∃ k, resultRows[q] grow by prefix k ∧ ...`
  → **storageShape 保存, resultRows[q] 単調増**

## 詰まり

G_* は **content-only**: 「変更対象以外の行を保存」とは書いていない。
- 例: G_insert は log 行 1 つ追加と言うが、無関係な行 (del=true 履歴、user-defined 行など) の保存は言わない。
- 結果: 論理的内容が同じでも **list 順/無関係行で差が出る** A, B が R 相互到達可能。
- `Database = List Row` の構造的等価には決定力が足りない。

## 単調性は確立可能 (中間目標)

R_archive (もしくは R_select q) の MultiStep 双方向で:
- **next 等値** (G_insert 単調 + 両方向 0 ステップから)
- **cut 等値**
- **storageShape 等値** (= 全 storage 行のテーブル/id/値が等しい)
- **resultRows[q] for all q 等値** (相互包含から)
- **wellFormedTableFields 等値** (相互保存)
- **archiveKeyFreshness 等値**

これらは G_* の単調性補題から組み立てる:
- `G_insert_strictly_increments_next : G_insert A B → next(B) = next(A) + 1`
- `G_archive_preserves_next : G_archive A B → next(A) = next(B)`
- `G_archive_monotone_cut : G_archive A B → cut(A) ≤ cut(B)`
- `G_select_preserves_storageShape : G_select q A B → sameStorageShape A B`
- ...

## 必要な追加ステップ (3 つの選択肢)

### 選択肢 (A): G_* tightening

各 G に「変更対象以外の行を bit-for-bit 保存」の clause を追加:
```lean
def G_insertCore : Guarantee :=
  fun oldDb newDb =>
    ∃ cut next newRow,
      storageShape oldDb cut next ∧
      storageShape newDb cut (next + 1) ∧
      newDb = oldDb ++ [newRow] ∧  -- ← 追加: list-level delta
      newRow.key? = some (logTable, next) ∧
      sameResultRows oldDb newDb ∧
      ...
```

similarly for G_archive (rows removed/added as explicit deltas) and G_select (result rows added).

**影響**: G_* を使う既存 lemma (例: `G_insert_preserves_logSystemInv` (Spec.lean:212),
`paperInfer_insertLogBody_*` 等) の証明が再調整必要。中規模 refactor。

**利点**: relyNoUndo が monotonicity + delta tracking で機械的に閉じる。

### 選択肢 (B): relyNoUndoAt with invariant

```lean
def relyNoUndoAt (R : Rely) (I : Assertion) : Prop :=
  ∀ A B, I A → I B → MultiStep R A B → MultiStep R B A → A = B
```

`stableIsolation_snapshot_*_of_noUndo` を refactor して I=logSystemInv hypothesis を取る形に変更。
caller (TransactionProofs.lean:1099 et al.) で I=logSystemInv hypothesis を chain する。

**追加 invariant が必要**: logSystemInv だけでは database を一意決定できない (list 順問題)。
canonical form (sorted by key, no duplicate keys, etc.) の lemma を追加するか、
**logSystemInv_canonical** という追加 invariant を導入する必要あり。

**影響**: 上流 (stableIsolation 系) の signature 変更。中〜大規模。

### 選択肢 (C): stableIsolation 側を緩める

`Logic.stableIsolation` の結論を strict list-equal から logical-equal に弱める。
ただし `IsolationSpec.snapshot.exec` の定義 (= `baseDb = finalDb`) との整合性のために、
snapshot のセマンティクス自体に手を入れる必要が出る可能性。**大規模**。

## 推奨アプローチ: 選択肢 (B) — `relyNoUndoAt` with invariant

G_* spec を触らず、`relyNoUndo` 側に invariant を入れる方向で進める。

### Step 1: `relyNoUndoAt` を導入

`TransactionProofs.lean:152` の既存 `relyNoUndo` の隣に追加 (もしくは置換):

```lean
def relyNoUndoAt (R : Rely) (I : Assertion) : Prop :=
  ∀ A B, I A → I B → MultiStep R A B → MultiStep R B A → A = B
```

互換性のため `relyNoUndo R := relyNoUndoAt R (fun _ => True)` として、既存 `relyNoUndo` も
`relyNoUndoAt` 経由で再定義する。

### Step 2: G_* 単調性補題 (Spec.lean に追加)

```lean
theorem G_insert_strictly_increments_next {oldDb newDb : Database} (h : G_insert oldDb newDb) :
    ∃ cut next, storageShape oldDb cut next ∧ storageShape newDb cut (next + 1)

theorem G_archive_preserves_next {oldDb newDb : Database} (h : G_archive oldDb newDb) :
    ∃ cut cut' next, storageShape oldDb cut next ∧ storageShape newDb cut' next ∧ cut ≤ cut'

theorem G_select_preserves_storageShape {oldDb newDb : Database} {q : Nat}
    (h : G_select q oldDb newDb) : sameStorageShape oldDb newDb
-- (resultRows[q] grows by prefix k)
```

これらは G_*Core の定義をほぼそのまま開いただけ。trivial。

### Step 3: R_archive / R_select 単調性の MultiStep 版

```lean
theorem R_archive_multiStep_monotone_next
    {oldDb newDb : Database} (hReach : MultiStep R_archive oldDb newDb)
    {cutO nextO cutN nextN : Nat}
    (hOld : storageShape oldDb cutO nextO)
    (hNew : storageShape newDb cutN nextN) :
    nextO ≤ nextN
-- 同じく cut, resultRows[q] for all q
```

induction on MultiStep を G_* 単調性で進める。

### Step 4: logSystemInv 下で DB が一意決定される補題

これが**鍵**。logSystemInv だけでは弱いので、追加の補題:

```lean
/-- logSystemInv + same storageShape + same resultRows[q] for all q + same wellFormedTableFields
→ database equality (as lists). -/
theorem database_unique_under_logSystemInv
    {A B : Database} (hInvA : logSystemInv A) (hInvB : logSystemInv B)
    {cut next : Nat}
    (hShapeA : storageShape A cut next) (hShapeB : storageShape B cut next)
    (hResults : ∀ q n, resultRowFor A q n ↔ resultRowFor B q n)
    (hKeyFresh : ∀ row, row ∈ A ↔ row ∈ B) :  -- 必要に応じて補強
    A = B
```

`Database = List Row` の構造的等価には list 順 + 重複 + del=true 行の保持が必要。
logSystemInv からそのレベルが言えるかは要検証 — 言えなければ追加 invariant (例:
`databaseCanonical`) を導入し、`relyNoUndoAt R logSystemInvCanonical` の形にする。

**簡易フォールバック**: もし list 等価が無理なら、`sameDatabaseContent` という弱い等価関係を
導入し、`relyNoUndoAt` の結論を `sameDatabaseContent A B` に変える。
ただし `stableIsolation` 側 (Logic.lean:138) の要求と整合させる必要あり。

### Step 5: relyNoUndoAt の証明

`R_archive` の場合: induction on MultiStep R_archive (forward) + 単調性で next/cut/resultRows 等値、
backward の MultiStep でも同様、最後に Step 4 の lemma で list 等値。

`R_select q` の場合も同様。

### Step 6: stableIsolation_snapshot_*_of_noUndo を refactor

```lean
theorem stableIsolation_snapshot_exec_of_noUndo
    {R : Rely} {I : Assertion}
    (hNoUndo : relyNoUndoAt R I)
    (hStableI : Logic.stableAssertion R I)  -- I が R-stable で midDb にも propagate
    (hInvBase : ...) :  -- baseDb satisfies I (caller から)
    Logic.stableIsolation R (IsolationSpec.snapshot (σ := Database)).exec
```

新たに I の propagation を要求するが、caller は logSystemInv を満たす状態を渡しているはず
なので chainable。

### Step 7: caller (TransactionProofs.lean:1099 et al.) の更新

`globalValid_snapshot_of_paperObligations_post` 内で `relyNoUndoAt R logSystemInv` を呼び、
`logSystemInv` の R-stability を `logSystemInv_stable_R_archive` / `_R_select` から chain する。

### 影響範囲まとめ

- 新規: `relyNoUndoAt`, G_* 単調性補題群, MultiStep 単調性, database 一意決定 (or 弱化)。
- 修正: `stableIsolation_snapshot_*_of_noUndo`, `globalValid_snapshot_of_paperObligations_post`,
  `relyNoUndo_R_archive` / `_R_select` (sorry 閉鎖)。
- 既存 G_*Core spec は不変 (memory `feedback_no_weakening` 準拠)。

## 関連 commit / 直前の作業

- `e01daf4` Close selectLazy gap + add wrap-aware per-rule soundness — 直近の commit。
  `Logic.localValid_select_collectInvariant` 等を追加 (selectLazy 用)。relyNoUndo とは別軸。
- `docs/PAPERINFER_REDESIGN.md` Step 5 — relyNoUndo の対応方針メモ。

## 検証

```
lake build
```

期待される結果: TransactionProofs.lean:941, 945 の sorry が消える。例側の
`paperInfer_*_final` 経由で `selectAllLogTxnSpec_final` 等が sorryAx-free。

`mcp__lean-lsp__lean_verify` で `DbAppProgramLogic.Transformer.LogStorageExample.TransactionProofs.selectAllLogTxnSpec_final` の
axioms に `sorryAx` が含まれないことを確認。

## ユーザーの設計原則 (絶対遵守、memory より)

- **「証明できないとき、定理を弱めない」** (`feedback_no_weakening`): 上流の def を直す方向。
- **`viaLocalValid` 濫用 NG**: ad-hoc な制限禁止 (この sorry には直接関係しないが要注意)。
- **False rely descent 回避** (`feedback_false_rely_descent`): wrap-aware soundness を使う。
- **`LEAN4_GUARDRAILS_BYPASS=1` 不可** (`feedback_no_guardrail_bypass`): push/PR が blocked のときは
  ユーザーに確認する。
- **lean-lsp を積極的に使う**: `mcp__lean-lsp__lean_goal` / `_diagnostic_messages` / `_multi_attempt`
  で証明 state を逐次確認。

## ブランチ

現在: `refinement-commit-log` (e01daf4 で wrap-based redesign を commit 済み)。
relyNoUndo refactor は別ブランチを切ることを推奨。
