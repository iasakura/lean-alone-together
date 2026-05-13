# Prompt: archive / selectAll の `paperInfer_*_final` を構築子経由に refactor

`DbAppProgramLogic/Transformer/LogStorageExample/TransactionProofs.lean` の以下 2 theorem を `viaLocalValid` 経由から **PaperInfer 構築子のみ + `PaperInfer.conseqF`** での組み立てに refactor。
docs/PAPERINFER_REDESIGN.md の Step 4 (paper-faithful な VCG refactor) の完了に対応。

## 対象

```
TransactionProofs.lean:1787  paperInfer_archiveLogBody_indexed_final
TransactionProofs.lean:2645  paperInfer_selectAllLogBody_final
```

両方とも `PaperInfer.viaLocalValid + Logic.localValid_of_stutterRely + Logic.localValid_select_false_pinVd` の False rely descent パターンを使用。doc Step 4 と memory `feedback_false_rely_descent` に従い除去する。

## 既に揃っている infrastructure (commit `5b25fe6`, `118f62d` 等)

| 補題/combinator | 場所 | 用途 |
|---|---|---|
| `Logic.localValid_select_collectInvariant` | Logic.lean | SELECT body の pre に `collectSelected = some sel` を組み込む変種 |
| `PaperInfer.conseqF` | InferenceSoundness.lean | 派生 F-weakening combinator (`viaLocalValid + sound + localValid_conseq` を内部カプセル化)。pointwise F-equiv 用 |
| `PaperInfer.conseqF_withInv` | InferenceSoundness.lean | invariant-aware F-weakening。F-equiv が `I vd` 下のみ成立する場合用 (例: `LazyF ↔ archiveLogEffect` は `logSystemInv vd` 下のみ成立) |
| `paperInferenceSound_*_wrapped` | Paper/Select/Foreach.lean | per-rule wrapped soundness |
| `logSystemInvAtNext_no_log_at_next` | Spec.lean | 静的 log freshness (insertLog 用) |
| `archiveKeysFreshFrom_no_archive_at` | Spec.lean | 静的 archive freshness (archiveLog 用) |

参考: insertLogBody の refactor 完成例 — commit `c21c891`、`paperInfer_insertLogBody_indexed_final` 参照。

## archive refactor 戦略

### body 構造

```
archiveLogBody i =
  .select logsVar rowVar (isLogExpr rowVar)
    (.ite (.setNonempty (.var logsVar))
       (archiveCompactBody i)        -- letE loVar (letE hi0Var (seq insert delete))
       .skip)
```

### Step A. body PaperInfer (per selected) を構築

`_via_lazy` の body 内側 (line ~1564 から ~1750 あたり) を、以下の構造に書き直す:

```lean
intro selected
-- After Command.subst logsVar (.lit (.set selected)):
-- .ite (.setNonempty (.lit (.set selected)))
--   (compactBody[logsVar→selected])  ← letE loVar (...) ...
--   .skip
refine PaperInfer.ite (env := emptySymEnv)
  (cond := .setNonempty (.lit (.set selected)))
  (FThen := FThenSelected) (FElse := SetLanguage.empty)
  hStable ?hThen ?hElse
case hElse => exact PaperInfer.skip ?_  -- skip with post stability
case hThen =>
  -- compactBody[logsVar→selected] = letE loVar (.setMinField (.lit (.set selected)) idField)
  --   (letE hi0Var (.setMaxField (.lit (.set selected)) idField)
  --     (seq (.insert archiveRecord) (.delete rowVar archiveDeletePredicate)))
  cases hMinEval : Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) with
  | none => exact absurd_or_skip  -- letE_none case is vacuous under PaperInfer
  | some loVal =>
    refine PaperInfer.letE (env := emptySymEnv)
      (x := loVar) (expr := .setMinField (.lit (.set selected)) idField)
      (value := loVal) hStable hMinEval ?innerLet
    -- innerLet : LocalValid ... (subst loVar loVal body) (post Fctxt F)
    -- Build via PaperInfer.sound applied to a sub-PaperInfer (= another PaperInfer.letE)
    have hSubPi : PaperInfer R txnId I Fctxt (subst loVar loVal innerBody) F_inner := by
      cases hMaxEval : ... 
      | some hi0Val =>
        refine PaperInfer.letE ... hMaxEval ?inner2
        ... -- PaperInfer.seq + .insert + .delete
    exact PaperInfer.sound hStableI hSubPi
```

**鍵となる pattern**: 各 PaperInfer.letE で `hBody : LocalValid ...` が必要 → 内側を別の PaperInfer で組み立てて `PaperInfer.sound hStableI` で LocalValid に変換。

### Step B. F shape の bridge

PaperInfer.ite の出力 F = `.ite (formulaOfExpr cond) FThenSelected SetLanguage.empty`。
これは `archiveLogEffect_with_selected sel` とは別の SetExpr。

denote-同値 (集合として等価) は: 
- `.ite (cond) FThenSelected empty` 評価
- `archiveLogEffect_with_selected sel`

を同じ vd で比較。selected が空 → cond false → empty。selected 非空 → cond true → FThenSelected, この場合 archive insert + delete をする → archiveLogEffect_with_selected の existential が成立 (selectedLitMin/Max が some)。

`PaperInfer.conseqF hStableI hBodyPi hFEq` で bridge。`hFEq` は denote 同値性の compact 証明。

### Step C. selectLazy で wrap

```lean
refine PaperInfer.selectLazy (env := emptySymEnv)
  (Fbody := archiveLogEffect_with_selected (archiveTxnId i) i)
  ?hStable ?hCollectStable ?hBody
case hCollectStable => 
  intro localDb visibleDb visibleDb' hR
  have := relyMod_snapshot_exec_silent ld vd vd' hR
  rw [this]
case hStable => exact transformerPre_stable_relyMod_snapshot _ _
case hBody =>
  intro selected
  -- Step A + Step B を組み合わせて
  -- PaperInfer R txnId I Fctxt (subst body sel) (archiveLogEffect_with_selected sel)
  ...
```

### Step D. `_indexed_final` の F を archiveLogEffect に bridge

`_via_lazy_pure` の出力 F は LazyF:
```
∃ sel, collectSelected vd ... = some sel ∧ archiveLogEffect_with_selected sel ld vd out
```

`_indexed_final` の目標 F は `archiveLogEffect (archiveTxnId i) i` (直接形)。
両者は denote 同値 (logSystemInv 下: selected = collectSelected log rows, selectedLitMin sel = selectedLogMin vd 等)。

**注意: pointwise には等価でない** (iff の逆方向は `collectSelected vd` の成功を要し、これは `logSystemInv vd` 下のみ言える)。したがって `PaperInfer.conseqF` (pointwise 版) ではなく **`PaperInfer.conseqF_withInv`** を使う。

```
PaperInfer.conseqF_withInv hStableI_archiveInv _via_lazy_pure hLazyF_to_archiveLogEffect
```

`hLazyF_to_archiveLogEffect` は型:
```
∀ ld vd, (logSystemInv vd ∧ archiveKeysFreshFrom i vd) →
  transformerPost empty LazyF ld vd → 
  transformerPost empty (archiveLogEffect (archiveTxnId i) i) ld vd
```

これを示すための補題群 (要実装):
- `selectedLitMin_eq_selectedLogMin`: `collectSelected vd rowVar (isLogExpr) = some sel → selectedLitMin sel = some lo ↔ selectedLogMin vd lo`
- `selectedLitMax_eq_selectedLogMax`: 同様
- `collectSelected_succeeds_under_invariant`: `logSystemInv vd → ∃ sel, collectSelected vd rowVar (isLogExpr) = some sel` (静的に decidable)
- `archiveLogEffect_with_selected_eq_archiveLogEffect`: `collectSelected vd = some sel → archiveLogEffect_with_selected sel ld vd row ↔ archiveLogEffect ld vd row`

これら 4 補題 + iff bridging で `hLazyF_to_archiveLogEffect` を組み立て。~80-150 LOC。

## selectAll refactor 戦略

`archiveLogBody` とほぼ同じだが内側は **`.foreach`**:

```
selectAllLogBody q =
  .select entriesVar rowVar (isLogExpr rowVar)
    (.foreach (.var entriesVar) doneVar entryVar
       (.ite (...predicate on entry...)
          (.insert resultRecord)
          .skip))
```

### 追加ポイント

- `PaperInfer.foreach` で body (per records) PaperInfer を構築。各 record で `.ite + .insert + .skip`。
- `.foreachRuntime` の per-iteration body を `PaperInfer.foreach` で受け取る形に組み立て。
- 個別 result row の freshness は `logSystemInv` の resultPrefixAll + per-q index から導出。

具体的構造は archive と同じパターン (PaperInfer.X の cascade + PaperInfer.sound bridge + PaperInfer.conseqF for F shape)。

## 実装順序

1. **archive の body PaperInfer (Step A)** から開始。各 PaperInfer.X 構築子で `?hStable`, `?hClosed`, `?hFresh` 等を都度 lean-lsp で確認しながら埋める。
2. **Step B (conseqF で F bridge)** で archive 完成。
3. **Step C (selectLazy で wrap)** で `_via_lazy_pure` 完成。
4. **Step D (`_indexed_final` の F bridge)** で archive 完了。
5. **selectAll** を同様に。

## 検証

```
lake build
mcp__lean-lsp__lean_verify DbAppProgramLogic.Transformer.LogStorageExample.archiveLogIndexedTxnSpec_final
mcp__lean-lsp__lean_verify DbAppProgramLogic.Transformer.LogStorageExample.selectAllLogTxnSpec_final
```

axioms に `sorryAx` が含まれないこと。

## 既存知見 / 注意

- `_via_lazy` (現存) の body の False rely descent 部分が ~250 行ある。これを PaperInfer 構築子で書き直すと、cascade な PaperInfer.sound 呼び出しで類似サイズ (~250-400 行) になる見込み。
- `PaperInfer.conseqF` は内部に `viaLocalValid` を含む派生 combinator なので、最終 artifact の axioms には sorry が無い限り問題なし。
- `Logic.localValid_*_false` 系の combinators (localValid_let_false, _ite_false 等) は body 内で使わない方針 (False rely descent 回避)。
- letE の hBody は `PaperInfer.sound hStableI` で LocalValid に変換。hStableI は `archiveIndexedInv_stable_R_archive i` を BiAssertion 形に lifting。

## 範囲外

- `transformerPostWrapped` の定義変更や `paperInfer_*_wrapped` 構造の刷新 (= doc Step 2-3 の "sound_wrapped を直接 induction で") は別タスク。
- relyNoUndo の 2 sorry は別 prompt (`docs/PROMPT_relyNoUndo.md`) で対応。

## 参考 commit

- `c21c891` Refactor paperInfer_insertLogBody_indexed_final — 完成例。
- `5b25fe6` Add PaperInfer.conseqF combinator and archive freshness lemma — 本タスクの基盤。
- `e01daf4` Close selectLazy gap — selectLazy 関連の wrap infrastructure。

## ブランチ

現在 `refinement-commit-log`。refactor は新ブランチを推奨。
