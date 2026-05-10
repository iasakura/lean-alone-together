# LogStorageExample: SI/RC handoff

This session pivoted to SI (`IsolationSpec.snapshot`) because RC + body-snapshot
aggregates broke the `transformerPost` `iff` (see *Architectural problem* below).
Two infrastructure pieces landed (path-aware `stableIsolation` and SI stability
lemmas via `relyNoUndo`); the actual SI bridge for archive/select is not yet
constructed. The user explicitly noted the spec **should** still hold under
RC and wants to retry RC in a separate session.

## What landed in this session

* **`stableIsolation` is path-aware** (`Logic.lean:132`, commit `768758a`):
  takes an additional `MultiStep R baseDb midDb` premise so monotonicity
  arguments can be threaded. `txnRuntimeFwd_sound{,_post}`,
  `txnProgramFwd_sound{,_post}`, `execIsolation_of_future_ready`,
  `commitIsolation_of_future_ready` were updated to thread the reachability
  proof. Existing RC users (`AppWorkflowExample`, `Examples`,
  `AuditLogExample`, `globalValid_readCommitted_of_paperObligations`) just
  need one extra `_` in `intro` patterns; their proofs remain trivial.
* **SI stability lemmas via `relyNoUndo`** (`TransactionProofs.lean`,
  commit `326a2d5`): introduces
  `relyNoUndo R := ∀ A B, MultiStep R A B → MultiStep R B A → A = B` and
  proves `stableIsolation R IsolationSpec.snapshot.{exec,commit}` under
  it. This matches the precise form of the paper's `stable(R, I_ss)`
  argument (p.27:16).

## What's still needed for the SI bridge

1. **Resolve the list-equality vs content-equality gap for
   `relyNoUndo`.**

   `relyNoUndo R := ∀ A B, MultiStep R A B → MultiStep R B A → A = B`
   uses *list* equality on `Database = List Row`. R_archive's
   guarantees `G_insert` and `G_select q` are stated as shape
   predicates over rows (storageShape, sameResultRowsExcept, etc.)
   that do *not* pin down list structure. In particular,
   `G_select q (A, A.permute)` holds with `k = 0` for any
   permutation, so `relyNoUndo R_archive` is **false in general**:
   take any non-trivial permutation pair.

   Resolutions, in order of likely tractability:

   1. **Tighten `G_insert` / `G_select`** to require list-structural
      properties (e.g., "newDb is oldDb ++ [logRow]" for G_insert;
      "newDb is oldDb ++ [resultRows]" for G_select). This still
      doesn't capture flush's clobber semantics for the counter
      row in insert, so it may need to be even more specific
      ("newDb is oldDb minus old counter + [newCounter, logRow]").
   2. **Weaken `IsolationSpec.snapshot.exec` from `prev = curr` to
      content equality**, then weaken `relyNoUndo` accordingly.
      `IsolationSpec` lives in `Semantics.lean` so this is a more
      upstream change.
   3. **Bypass `stableIsolation` for SI** entirely: write a custom
      `txnGlobalValid_of_localValid_post_si` that takes a different
      stability hypothesis. Largest refactor of the three.

2. **Build `globalValid_snapshot_of_paperObligations_post`** (and
   `_pre` variant) using the new stability lemmas. **Done in this
   session** (commit `13e2b8d`); takes `relyNoUndo R` as a hypothesis
   and produces `Logic.GlobalValid Ipre R (.txn txnId IsolationSpec.snapshot body) G Ipost`.

3. **Switch `archiveLogIndexedTxnSpec` (and possibly
   `selectAllLogTxnSpec`) to `IsolationSpec.snapshot`** in
   `Spec.lean:142-152` and `Model.lean:399-403`. Update
   `archiveLogTxnSpec_of_paperObligations` /
   `archiveLogIndexedTxnSpec_of_indexedPaperObligations` to call the
   new snapshot bridges.

4. **Prove `paperInfer_archiveLogBody_indexed_final`** under the SI
   rely. Under SI, `relyMod R IsolationSpec.snapshot.exec` forces
   `visibleDb = visibleDb'` for any rely step seen by the body, so
   the body sees a frozen visibleDb. The
   `localValid_*` composition (or direct PaperInfer constructors)
   should now go through with strict F definitions because
   `selectedLogMin/Max` at body-end visibleDb agree with what the
   body computed at select-time.

5. **Same for `paperInfer_selectAllLogBody_final`** (subject to step (1)
   working out for `R_select q`).

## The architectural problem (why naive RC fails here)

## The architectural problem (why naive RC fails here)

The `PaperInfer` → `LocalValid` → `GlobalValid` pipeline runs:

```
PaperInfer R txnId I empty body F
  ↓ PaperInfer.sound_with_invariant            (InferenceSoundness.lean:82)
LocalValid R txnId (transformerPre I empty) body (transformerPostI I empty F)
  ↓ transformerPostI_to_txnSnapshotPost        (SnapshotPost.lean:56)
LocalValid R txnId (...) body (txnSnapshotPost I R F)
  ↓ txnGlobalValid_of_localValid_post          (Logic.lean)
GlobalValid I R (.txn ...) G I
```

Inside `transformerPost` (`Transformer/Basic.lean:536-540`):

```lean
def transformerPost (Fctxt F : SetLanguage.SetExpr) : BiAssertion :=
  fun localDb visibleDb =>
    ∀ row,
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) (.union Fctxt F) row ↔
        row ∈ localDb
```

Two crucial points:

1. **`F` is denoted at `Env.ofDatabases [] visibleDb`** with `visibleDb` =
   `finalCfg.visibleDb` (the body-end visibleDb, call it `V_end`).
   - F's `globalDb` argument = V_end.
   - F's `_localDb` argument = `[]` always — *not* the body-accumulated localDb.
2. The `iff` requires `denote(V_end) F` to **exactly equal** body-end localDb.

So `F` must be a denotational **function from `V_end` to body-end `localDb`**.

`archiveLogBody` and `selectAllLogBody` violate this: their `loVar`/`hi0Var` (or selected
`entriesVar`) are frozen at *select-time visibleDb* (`V_start`). Under RC, `R_archive`
fires `G_insert` between select and body-end, so V_start and V_end disagree on
`selectedLogMax`. Strict F: `iff` backward fails (our row not denoted at V_end).
Existentially-relaxed F: `iff` forward fails (F denotes multiple archive rows, localDb has
one). Pure relaxation can't fix uniqueness because F's `_localDb` is hard-coded to `[]`,
so F cannot peek at the body's actual writes to pin `hi0`.

## RC retry plan: bypass `PaperInfer` for archive/select

Replace the middle two segments of the pipeline (PaperInfer.sound + the
`transformerPostI_to_txnSnapshotPost` conversion) with a custom direct construction:

```
〔archive 専用〕LocalValid R txnId (...) archiveLogBody (txnSnapshotPost I R archiveLogEffect)
  ↓ txnGlobalValid_of_localValid_post  (unchanged from current pipeline)
GlobalValid I R (.txn ...) G I
```

The trick is that `txnSnapshotPost` existentially quantifies `snapshotDb`, so the proof
can pick `snapshotDb := V_start` (the visibleDb captured at the moment of `.select`),
where `selectedLogMin/Max` *do* match the body's `loVar`/`hi0Var` exactly, and F's
denotation is `iff`-tight against body-end localDb.

### Concrete steps

1. **Custom LocalValid theorem** (skip `PaperInfer` entirely):

   ```lean
   theorem localValid_archiveLogBody_snapshotPost (i : Nat) :
       Logic.LocalValid
         (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).exec)
         (archiveTxnId i)
         (fun localDb visibleDb => localDb = [] ∧ Iinfer visibleDb)
         (archiveLogBody i)
         (txnSnapshotPost Iinfer R_archive (archiveLogEffect (archiveTxnId i) i))
   ```

   Proof outline:
   - Apply `localValid_select` from `Logic.lean:1469`. Its `hBody` premise gives:
     ```
     ∀ localDb visibleDb selected,
       P localDb visibleDb →
       Semantics.collectSelected visibleDb source predicate = some selected →
       LocalValid R txnId P (Command.subst binder (.lit (.set selected)) body) Q
     ```
     Here `visibleDb` is **V_start** (the select-time visibleDb). Capture it in scope.
   - Continue with `localValid_ite`, `localValid_letE`×2, `localValid_seq`,
     `localValid_insert`, `localValid_delete`. The intermediate Q's track
     "txnSnapshotPost-with-snapshotDb=V_start, with the cumulative effect so far".
   - At leaves, use `Database.disjointIds` / `Semantics.insertFresh` / `collectDeleted`
     hypotheses fed by the composition rules to discharge the per-write obligations.
   - The `MultiStep R_archive V_start visibleDb_end` side-condition: V_start →
     visibleDb_end is reached entirely by rely steps (since `IsolationSpec.readCommitted`
     `exec` is True everywhere — local steps don't change visibleDb, only rely does).

2. **Custom bridge** that takes the `localValid_..._snapshotPost` LocalValid and feeds
   `Logic.txnGlobalValid_of_localValid_post` directly. Pattern this on
   `globalValid_readCommitted_of_paperObligations_post`
   (`TransactionProofs.lean:83`), but replace the PaperInfer-derived LocalValid with
   the custom one. `qstable` and `guarantee` obligations stay unchanged — they already
   operate on `txnSnapshotPost`.

3. **Re-use everything that's already closed**:
   - `archiveLogIndexedEffect_qstable_final` (TransactionProofs.lean ~672) — qstable.
   - `archiveLogIndexedEffect_guarantee_final` (~1407) — guarantee bridge,
     uses `selectedLogMin_exists` / `selectedLogMax_exists` for constructive witnesses.
   - `selectedLogMin_exists` / `selectedLogMax_exists` (~1175, 1257) — finite-set min/max.
   - `archiveLogEffect_local_has_logKey`, `archiveLogSnapshotPost_local_logKey_implies_snap_log`
     — local-row characterizations.
   - `R_archive_multiStep_storageShape` (Spec.lean ~498) — storageShape evolution under
     R_archive.
   - `archiveLogSnapshotPost_local_row_key` (~338) — local row's key is archive-or-log.

4. **Repeat for `selectAllLogBody`**: write `localValid_selectAllLogBody_snapshotPost`
   following the same pattern. The body uses nested `.foreach`, so the proof needs
   `localValid_foreach`/`_foreachStart`/`_foreachDone`/`_foreachNext` from Logic.lean
   (~1652, 1696, 1748, 1792). The `entriesVar` is frozen at select-time exactly like
   `logsVar`.

### What needs care

- **Threading the snapshot through composition**: each `localValid_*` premise gets a
  fresh `localDb`/`visibleDb` pair. The intermediate Q must say "∃ snap (= V_start),
  reachable, denote(snap) F_partial = localDb_partial". Pick a single `Q-builder` lemma
  to keep the snapshot bound consistently.
- **Stability**: `txnSnapshotPost` is stable under `R_archive`-only steps (the snapshot
  doesn't move; reachability extends). Inside `localValid_*`'s `hStable` premise this
  is straightforward; build a small reusable `txnSnapshotPost_stable_relyMod_exec` lemma.
- **`.select` substitution semantics**: `Command.subst logsVar (.lit (.set selected))`
  rewrites occurrences of `.var logsVar` inside `archiveCompactBody`. Verify the substituted
  body matches what `Expr.eval` does for `setMinField`/`setMaxField` on `.lit (.set selected)`.
- **`R_archive` may not preserve `selectedLogMin V_start`**: if a *different* archive
  somehow committed a partial range during exec, the min could move. R_archive currently
  excludes other archives (= `G_insert ∨ ∃ q, G_select q`), so this isn't an issue, but
  worth re-checking when committing the proof.

## Files / line pointers (verify against `git log` before relying)

```
DbAppProgramLogic/Transformer/LogStorageExample/
  Model.lean              tables, records, predicates, storageShape, logSystemInv
  Spec.lean               TxnSpec, R/G, R_archive stability, multistep storageShape
  SnapshotPost.lean       txnSnapshotPost + stable_readCommitted + weaken
  Effects.lean            native_decide checkpoints
  TransactionProofs.lean  PaperObligations, paperInfer_*, *Effect_guarantee_final, archive bridge
  Final.lean              selectAllLog_returnsPrefix_final (depends on the body proofs)

DbAppProgramLogic/
  Logic.lean              localValid_* composition rules (1229-1900-ish)
  Semantics.lean          Command/Row/RecordLit, IsolationSpec.readCommitted (~721-722)
  Transformer/Basic.lean  transformerPre/Post (~529-540)
  Transformer/Inference.lean  PaperInfer inductive (~29)
  Transformer/InferenceSoundness.lean  PaperInfer.sound_with_invariant
  Transformer/InferenceCapstone.lean   PaperInfer.globalValid_txn{,Par}
```

## Notes for the next session

- The previous SI pivot (this session) modified isolation in `Spec.lean` and may have
  forked `globalValid_readCommitted_of_paperObligations` into a `_snapshot` variant. For
  the RC retry, you have two options:
  1. Branch off a new `rc-retry` branch from the pre-SI commit and start fresh.
  2. Re-introduce RC alongside the SI variant, parameterizing the bridge by isolation.
- `archive/log-storage-example-v1` branch holds the original (pre-rewrite) v1 of this
  example for reference; not relevant to RC retry.
