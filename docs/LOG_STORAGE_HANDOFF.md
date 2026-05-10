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

1. **Prove `relyNoUndo R_archive`** (and `relyNoUndo (R_select q)` if
   the select pivot is desired).

   Sketch for `R_archive = G_insert ∨ ∃ q, G_select q`: under any
   `R_archive` step, `next` is non-decreasing (G_insert strictly
   advances; G_select preserves via `sameStorageShape`). Result rows
   for any q can only grow under R_archive (G_select adds, G_insert
   preserves via `sameResultRows`). With both directions multistepping,
   `next` and result rows must be equal at both ends, forcing all
   intermediate steps to be no-op. Then `db = db'` follows from the
   record-set equality on storage + result tables.

   Note `R_select q = G_insert ∨ G_archive`: G_archive is *not*
   monotonic in row-set (it adds delete markers; flush would remove
   logs, but that's at commit). For SI purposes, G_archive's effect
   on visible during another worker's body run is the post-flush
   state, which removes log rows. So `R_select` may NOT satisfy
   `relyNoUndo`. SI for select probably requires a separate
   argument or accepting it can't be done.

2. **Build `globalValid_snapshot_of_paperObligations_post`** (and
   `_pre` variant) using the new stability lemmas.

   Pattern after `globalValid_readCommitted_of_paperObligations_post`
   (`TransactionProofs.lean:83`); replace
   `IsolationSpec.readCommitted Database` with `IsolationSpec.snapshot`,
   replace the trivial `stableIsolation` proofs with applications of
   `stableIsolation_snapshot_exec_of_noUndo` /
   `stableIsolation_snapshot_commit_of_noUndo` fed by step (1).

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
