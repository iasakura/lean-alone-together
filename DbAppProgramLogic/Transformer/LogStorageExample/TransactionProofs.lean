import DbAppProgramLogic.Transformer.InferenceCapstone
import DbAppProgramLogic.Transformer.LogStorageExample.SnapshotPost
import DbAppProgramLogic.Transformer.LogStorageExample.Spec

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Single-transaction proof leaves

`Final.lean` is top-down. This file names the three leaf theorems and factors
each through explicit `PaperInfer` obligations. The `sorry`s here mark the
remaining proof work; they are isolated to the inner-effect/guarantee bridges
that depend on the concrete shape of `Database.flush` and `inferEffect`.
-/

open SetLanguage

/-- Paper-style obligations sufficient to prove one read-committed transaction
specification. -/
structure TxnPaperObligations
    (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (body : Semantics.Program) where
  effect : SetLanguage.SetExpr
  infer :
    PaperInfer
      (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
      txnId I SetLanguage.empty body effect
  qstable :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost I R effect)
  guarantee :
    ∀ localDb visibleDb,
      txnSnapshotPost I R effect localDb visibleDb →
        G visibleDb (Database.flush localDb visibleDb)

theorem globalValid_readCommitted_of_paperObligations
    {R : Rely} {I : Assertion} {G : Guarantee}
    {txnId : TxnId} {body : Semantics.Program}
    (hStableI : Logic.stableAssertion R I)
    (hPreserve : ∀ db db', I db → G db db' → I db')
    (hObligations : TxnPaperObligations R I G txnId body) :
    Logic.GlobalValid I R
      (.txn txnId (IsolationSpec.readCommitted Database) body)
      G I := by
  have hExecStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).exec := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hCommitStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).commit := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hStableIBi :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        (fun _ visibleDb => I visibleDb) :=
    stableBiAssertion_relyMod_of_stableAssertion
      (IsolationSpec.readCommitted Database) hStableI
  have hLocalBase :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId (transformerPre I SetLanguage.empty) body
        (transformerPostI I SetLanguage.empty hObligations.effect) :=
    PaperInfer.sound_with_invariant hStableIBi hObligations.infer
  have hLocal :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId (fun localDb visibleDb => localDb = [] ∧ I visibleDb) body
        (txnSnapshotPost I R hObligations.effect) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        (transformerPre_empty_iff I localDb visibleDb).mpr hPre)
      hLocalBase
      (transformerPostI_to_txnSnapshotPost I R hObligations.effect)
  exact Logic.txnGlobalValid_of_localValid
    hStableI hExecStable hCommitStable
    (fun _ _ => Iff.rfl)
    hLocal hObligations.qstable hObligations.guarantee hPreserve

theorem globalValid_readCommitted_of_paperObligations_post
    {R : Rely} {Iinfer Ipre Ipost : Assertion} {G : Guarantee}
    {txnId : TxnId} {body : Semantics.Program}
    (_hStableInfer : Logic.stableAssertion R Iinfer)
    (hStablePre : Logic.stableAssertion R Ipre)
    (hStablePost : Logic.stableAssertion R Ipost)
    (hPreToInfer : ∀ db, Ipre db → Iinfer db)
    (hObligations : TxnPaperObligations R Iinfer G txnId body)
    (hCommitPost :
      ∀ localDb visibleDb,
        Ipre visibleDb →
          txnSnapshotPost Iinfer R hObligations.effect localDb visibleDb →
            Ipost (Database.flush localDb visibleDb)) :
    Logic.GlobalValid Ipre R
      (.txn txnId (IsolationSpec.readCommitted Database) body)
      G Ipost := by
  have hExecStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).exec := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hCommitStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).commit := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hStableIBi :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        (fun _ visibleDb => Iinfer visibleDb) :=
    stableBiAssertion_relyMod_of_stableAssertion
      (IsolationSpec.readCommitted Database) _hStableInfer
  have hLocalBase :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId (transformerPre Iinfer SetLanguage.empty) body
        (transformerPostI Iinfer SetLanguage.empty hObligations.effect) :=
    PaperInfer.sound_with_invariant hStableIBi hObligations.infer
  have hLocalInfer :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId (fun localDb visibleDb => localDb = [] ∧ Iinfer visibleDb) body
        (txnSnapshotPost Iinfer R hObligations.effect) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        (transformerPre_empty_iff Iinfer localDb visibleDb).mpr hPre)
      hLocalBase
      (transformerPostI_to_txnSnapshotPost Iinfer R hObligations.effect)
  have hLocal :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId (fun localDb visibleDb => localDb = [] ∧ Ipre visibleDb) body
        (txnSnapshotPost Iinfer R hObligations.effect) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        ⟨hPre.1, hPreToInfer visibleDb hPre.2⟩)
      hLocalInfer
      (fun _ _ hPost => hPost)
  exact Logic.txnGlobalValid_of_localValid_post
    hStablePre hStablePost hExecStable hCommitStable
    (fun _ _ => Iff.rfl)
    hLocal hObligations.qstable hObligations.guarantee hCommitPost

/-! ## Snapshot-isolation variants of the bridges

Under SI (`IsolationSpec.snapshot`), the body sees a frozen visible
database during exec, which lets us discharge the
"`F` is a function of body-end `globalDb`" requirement of
`transformerPost`. The isolation-stability condition is satisfied
when `R` admits no round-trips: if `MultiStep R A B` and
`MultiStep R B A`, then `A = B`. This is the form in which the paper's
`stable(R, I_ss)` argument actually holds (p.27:16). -/

def relyNoUndo (R : Rely) : Prop :=
  ∀ A B, Logic.MultiStep R A B → Logic.MultiStep R B A → A = B

theorem stableIsolation_snapshot_exec_of_noUndo
    {R : Rely} (hNoUndo : relyNoUndo R) :
    Logic.stableIsolation R (IsolationSpec.snapshot (σ := Database)).exec := by
  intro localDb baseDb midDb finalDb hReach hI hR
  -- hI : IsolationSpec.snapshot.exec localDb baseDb finalDb = (baseDb = finalDb)
  have hEq : baseDb = finalDb := hI
  subst hEq
  have hReachBack : Logic.MultiStep R midDb baseDb := Logic.MultiStep.tail Logic.MultiStep.refl hR
  have hMidEq : baseDb = midDb := hNoUndo baseDb midDb hReach hReachBack
  exact ⟨hMidEq, hMidEq.symm⟩

theorem stableIsolation_snapshot_commit_of_noUndo
    {R : Rely} (hNoUndo : relyNoUndo R) :
    Logic.stableIsolation R (IsolationSpec.snapshot (σ := Database)).commit := by
  intro localDb baseDb midDb finalDb hReach hI hR
  have hEq : baseDb = finalDb := hI
  subst hEq
  have hReachBack : Logic.MultiStep R midDb baseDb := Logic.MultiStep.tail Logic.MultiStep.refl hR
  have hMidEq : baseDb = midDb := hNoUndo baseDb midDb hReach hReachBack
  exact ⟨hMidEq, hMidEq.symm⟩

/-- Snapshot-isolation variant of `TxnPaperObligations`. The body's
`PaperInfer` derivation is over SI's local rely (which forces `visibleDb` to
remain frozen during exec); this is essential for archive-style bodies
whose writes depend on the body-start snapshot. -/
structure TxnPaperObligationsSI
    (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (body : Semantics.Program) where
  effect : SetLanguage.SetExpr
  infer :
    PaperInfer
      (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
      txnId I SetLanguage.empty body effect
  qstable :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).commit)
      (txnSnapshotPost I R effect)
  guarantee :
    ∀ localDb visibleDb,
      txnSnapshotPost I R effect localDb visibleDb →
        G visibleDb (Database.flush localDb visibleDb)

/-- Snapshot-isolation variant of `globalValid_readCommitted_of_paperObligations_post`.
Requires `relyNoUndo R` (no round-trips under R) which discharges the
isolation-stability conditions for `IsolationSpec.snapshot`. The body's
`PaperInfer` derivation is taken under SI's local rely (so the body sees a
frozen `visibleDb` during exec). -/
theorem globalValid_snapshot_of_paperObligations_post
    {R : Rely} {Iinfer Ipre Ipost : Assertion} {G : Guarantee}
    {txnId : TxnId} {body : Semantics.Program}
    (hNoUndo : relyNoUndo R)
    (hStableInfer : Logic.stableAssertion R Iinfer)
    (hStablePre : Logic.stableAssertion R Ipre)
    (hStablePost : Logic.stableAssertion R Ipost)
    (hPreToInfer : ∀ db, Ipre db → Iinfer db)
    (hObligations : TxnPaperObligationsSI R Iinfer G txnId body)
    (hCommitPost :
      ∀ localDb visibleDb,
        Ipre visibleDb →
          txnSnapshotPost Iinfer R hObligations.effect localDb visibleDb →
            Ipost (Database.flush localDb visibleDb)) :
    Logic.GlobalValid Ipre R
      (.txn txnId IsolationSpec.snapshot body)
      G Ipost := by
  have hExecStable :
      Logic.stableIsolation R (IsolationSpec.snapshot (σ := Database)).exec :=
    stableIsolation_snapshot_exec_of_noUndo hNoUndo
  have hCommitStable :
      Logic.stableIsolation R (IsolationSpec.snapshot (σ := Database)).commit :=
    stableIsolation_snapshot_commit_of_noUndo hNoUndo
  have hStableIBi :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
        (fun _ visibleDb => Iinfer visibleDb) := by
    intro localDb v v' hI hStep
    rcases hStep with ⟨_baseDb, hR, _, _⟩
    exact hStableInfer _ _ hI hR
  have hLocalSI :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
        txnId (transformerPre Iinfer SetLanguage.empty) body
        (transformerPostI Iinfer SetLanguage.empty hObligations.effect) :=
    PaperInfer.sound_with_invariant hStableIBi hObligations.infer
  have hLocalInfer :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
        txnId (fun localDb visibleDb => localDb = [] ∧ Iinfer visibleDb) body
        (txnSnapshotPost Iinfer R hObligations.effect) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        (transformerPre_empty_iff Iinfer localDb visibleDb).mpr hPre)
      hLocalSI
      (transformerPostI_to_txnSnapshotPost Iinfer R hObligations.effect)
  have hLocal :
      Logic.LocalValid
        (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
        txnId (fun localDb visibleDb => localDb = [] ∧ Ipre visibleDb) body
        (txnSnapshotPost Iinfer R hObligations.effect) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        ⟨hPre.1, hPreToInfer visibleDb hPre.2⟩)
      hLocalInfer
      (fun _ _ hPost => hPost)
  exact Logic.txnGlobalValid_of_localValid_post
    hStablePre hStablePost hExecStable hCommitStable
    (fun _ _ => Iff.rfl)
    hLocal hObligations.qstable hObligations.guarantee hCommitPost

abbrev InsertLogPaperObligations (i : Nat) :=
  TxnPaperObligations R_insert (logSystemInvAtNext i) G_insert
    (insertTxnId i) (insertLogBody i)

abbrev ArchiveLogPaperObligations (i : Nat) :=
  TxnPaperObligationsSI R_archive logSystemInv G_archive
    (archiveTxnId i) (archiveLogBody i)

abbrev SelectAllLogPaperObligations (q : Nat) :=
  TxnPaperObligationsSI (R_select q) logSystemInv (G_select q)
    (selectTxnId q) (selectAllLogBody q)

/-! ## Concrete symbolic effects -/

def emptySymEnv : SymEnv :=
  { scalarVars := [], setVars := [] }

def insertCounterUpdateExpr (i : Nat) : Expr :=
  .withUpdates (.var rowVar)
    [(nextField, .int (i + 1))]

/-- Effect of `insertLogBody i`: insert log row `i` and update the counter to
`i+1`. -/
def insertLogEffect (txnId : TxnId) (i : Nat) : SetLanguage.SetExpr :=
  .union
    (insertedRowSet txnId emptySymEnv (logRecordExpr (.int i)))
    (updateSetExpr txnId [] rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar))

def selectedLogRow (globalDb : Database) (row : Row) (n : Int) : Prop :=
  row ∈ globalDb ∧ row.key? = some (logTable, n)

def selectedLogMin (globalDb : Database) (lo : Int) : Prop :=
  (∃ row, selectedLogRow globalDb row lo) ∧
    ∀ row n, selectedLogRow globalDb row n → lo ≤ n

def selectedLogMax (globalDb : Database) (hi : Int) : Prop :=
  (∃ row, selectedLogRow globalDb row hi) ∧
    ∀ row n, selectedLogRow globalDb row n → n ≤ hi

def archiveLogInsertEffect (txnId : TxnId) (i : Nat) : SetLanguage.SetExpr :=
  fun _localDb globalDb out =>
    ∃ lo hi0,
      selectedLogMin globalDb lo ∧
        selectedLogMax globalDb hi0 ∧
        out = archiveRow txnId i lo (hi0 + 1)

def archiveLogDeleteEffect (txnId : TxnId) : SetLanguage.SetExpr :=
  fun _localDb globalDb out =>
    ∃ src n lo hi0,
      selectedLogMin globalDb lo ∧
        selectedLogMax globalDb hi0 ∧
        selectedLogRow globalDb src n ∧
        lo ≤ n ∧
        n ≤ hi0 ∧
        out = src.markDeleted txnId

def archiveLogEffect (txnId : TxnId) (i : Nat) : SetLanguage.SetExpr :=
  .union (archiveLogInsertEffect txnId i) (archiveLogDeleteEffect txnId)

/-! ### Selected-parameterized variants for `PaperInfer.selectLazy`

These are the `Fbody : SetLit → SetExpr` forms used in the lazy SELECT
rule (paper Fig.8 ST-SELECT). `selected` is the captured collectSelected
result, and the min/max are computed from `selected` itself, not from
globalDb. This eliminates the universal-quantification mismatch that
arose when `selected` was baked into the body via `Command.subst` while
the surrounding `archiveLogEffect` recomputed min/max from globalDb. -/

private def selectedLitMin (selected : SetLit) : Option Int :=
  match Expr.eval (.setMinField (.lit (.set selected)) idField) with
  | some (.scalar (.int v)) => some v
  | _ => none

private def selectedLitMax (selected : SetLit) : Option Int :=
  match Expr.eval (.setMaxField (.lit (.set selected)) idField) with
  | some (.scalar (.int v)) => some v
  | _ => none

/-- `setMinField` on a set literal always returns `.scalar (.int _)` when it
returns `some`. Pinning this fact lets callers extract the integer value from
an opaque `loVal`. -/
private theorem setMinField_lit_eval_int {selected : SetLit} {field : FieldName} {v : Value}
    (h : Expr.eval (.setMinField (.lit (.set selected)) field) = some v) :
    ∃ lo : Int, v = .scalar (.int lo) := by
  simp only [Expr.eval, Literal.toValue] at h
  rcases hVals : Expr.collectIntFieldValues field selected with _ | values
  · simp [hVals] at h
  · rcases hMin : Expr.minInt? values with _ | m
    · simp [hVals, hMin] at h
    · simp [hVals, hMin] at h
      exact ⟨m, h.symm⟩

/-- `setMaxField` analogue. -/
private theorem setMaxField_lit_eval_int {selected : SetLit} {field : FieldName} {v : Value}
    (h : Expr.eval (.setMaxField (.lit (.set selected)) field) = some v) :
    ∃ hi : Int, v = .scalar (.int hi) := by
  simp only [Expr.eval, Literal.toValue] at h
  rcases hVals : Expr.collectIntFieldValues field selected with _ | values
  · simp [hVals] at h
  · rcases hMax : Expr.maxInt? values with _ | m
    · simp [hVals, hMax] at h
    · simp [hVals, hMax] at h
      exact ⟨m, h.symm⟩

/-- The archive-delete predicate (after substitution of `lo`/`hi0`) holds on a
row iff its visible record has table = `logTable` and id in `[lo, hi0]`. -/
private theorem satisfiesPredicate_archiveDelete_iff (src : Row) (lo hi0 : Int) :
    Semantics.satisfiesPredicate rowVar
        (Expr.binop BinOp.and
          (Expr.binop BinOp.eq ((Expr.var rowVar).proj tableField)
            (Expr.lit (.scalar (.int logTable))))
          (Expr.binop BinOp.and
            (Expr.binop BinOp.le (Expr.lit (.scalar (.int lo)))
              ((Expr.var rowVar).proj idField))
            (Expr.binop BinOp.le ((Expr.var rowVar).proj idField)
              (Expr.lit (.scalar (.int hi0))))))
        src.visible = some true ↔
      rowFieldInt? src tableField = some logTable ∧
        ∃ n, rowFieldInt? src idField = some n ∧ lo ≤ n ∧ n ≤ hi0 := by
  simp only [Semantics.satisfiesPredicate, Semantics.instantiateRecord,
    Expr.subst, Expr.subst_lit, Expr.eval, Literal.toValue,
    rowFieldInt?, tableField, idField, rowVar, ↓reduceIte]
  cases hT : src.visible.lookup? "table" with
  | none => simp [hT]
  | some tlit =>
    cases tlit with
    | bool _ => simp [hT]
    | int tableVal =>
      cases hI : src.visible.lookup? "id" with
      | none =>
        simp [hT, hI]
        intro h
        split at h <;> simp_all
      | some ilit =>
        cases ilit with
        | bool b =>
          simp [hT, hI]
          intro h
          split at h <;> simp_all
        | int idVal =>
          simp [hT, hI]
          by_cases hTab : tableVal = logTable
          · subst hTab
            simp
            constructor
            · intro h
              by_cases hLo : lo ≤ idVal
              · simp [hLo] at h
                exact ⟨hLo, h⟩
              · simp [hLo] at h
            · rintro ⟨hLo, hHi⟩
              simp [hLo, hHi]
          · simp [hTab]

/-- Under `collectSelected vd "row" isLogExpr = some selected` and
wellFormedness, membership in `selected` corresponds to log rows in `vd`. -/
private theorem mem_selected_iff_log_row
    {vd : Database} {selected : SetLit}
    (hSelect : Semantics.collectSelected vd rowVar (isLogExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) (rec : RecordLit) :
    rec ∈ selected ↔
      ∃ row, row ∈ vd ∧ (∃ n : Int, row.key? = some (logTable, n)) ∧
        row.visible = rec := by
  rw [Semantics.mem_collectSelected_iff hSelect]
  constructor
  · rintro ⟨sr, hSrMem, hSat, hVis⟩
    have hTab : rowFieldInt? sr tableField = some logTable :=
      (satisfiesPredicate_isTableExpr_iff sr logTable).mp hSat
    have hKey : ∃ n, sr.key? = some (logTable, n) := by
      rcases hWF sr hSrMem with ⟨t, n, hSrKey, hSrTab⟩
      rw [hSrTab] at hTab
      have hTEq : t = logTable := Option.some.inj hTab
      exact ⟨n, hTEq ▸ hSrKey⟩
    exact ⟨sr, hSrMem, hKey, hVis⟩
  · rintro ⟨sr, hSrMem, ⟨n, hKey⟩, hVis⟩
    have hTab : rowFieldInt? sr tableField = some logTable :=
      rowFieldInt?_tableField_of_key_wellFormed hWF hSrMem hKey
    have hSat : Semantics.satisfiesPredicate rowVar (isLogExpr rowVar) sr.visible =
        some true :=
      (satisfiesPredicate_isTableExpr_iff sr logTable).mpr hTab
    exact ⟨sr, hSrMem, hSat, hVis⟩

/-- Storage-entry analogue of `mem_selected_iff_log_row`: under wellFormedness,
`rec ∈ selected` (where selected comes from `collectSelected` over
`isStorageEntryExpr`) iff `rec = row.visible` for some `row ∈ vd` with key
in {logTable, archiveTable}. -/
private theorem mem_selected_iff_storage_entry
    {vd : Database} {selected : SetLit}
    (hSelect : Semantics.collectSelected vd rowVar (isStorageEntryExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) (rec : RecordLit) :
    rec ∈ selected ↔
      ∃ row, row ∈ vd ∧
        ((∃ n : Int, row.key? = some (logTable, n)) ∨
          (∃ n : Int, row.key? = some (archiveTable, n))) ∧
        row.visible = rec := by
  rw [Semantics.mem_collectSelected_iff hSelect]
  constructor
  · rintro ⟨sr, hSrMem, hSat, hVis⟩
    have hTabOr := (satisfiesPredicate_isStorageEntryExpr_iff sr).mp hSat
    have hKey : (∃ n, sr.key? = some (logTable, n)) ∨
        (∃ n, sr.key? = some (archiveTable, n)) := by
      rcases hWF sr hSrMem with ⟨t, n, hSrKey, hSrTab⟩
      rcases hTabOr with hLog | hArch
      · rw [hSrTab] at hLog
        have hTEq : t = logTable := Option.some.inj hLog
        exact Or.inl ⟨n, hTEq ▸ hSrKey⟩
      · rw [hSrTab] at hArch
        have hTEq : t = archiveTable := Option.some.inj hArch
        exact Or.inr ⟨n, hTEq ▸ hSrKey⟩
    exact ⟨sr, hSrMem, hKey, hVis⟩
  · rintro ⟨sr, hSrMem, hKey, hVis⟩
    have hTabOr : rowFieldInt? sr tableField = some logTable ∨
        rowFieldInt? sr tableField = some archiveTable := by
      rcases hKey with ⟨n, hLog⟩ | ⟨n, hArch⟩
      · exact Or.inl (rowFieldInt?_tableField_of_key_wellFormed hWF hSrMem hLog)
      · exact Or.inr (rowFieldInt?_tableField_of_key_wellFormed hWF hSrMem hArch)
    have hSat : Semantics.satisfiesPredicate rowVar (isStorageEntryExpr rowVar) sr.visible =
        some true :=
      (satisfiesPredicate_isStorageEntryExpr_iff sr).mpr hTabOr
    exact ⟨sr, hSrMem, hSat, hVis⟩

/-- For a log row, its visible record's `intField? idField` equals the
log id from its key. -/
private theorem intField?_idField_of_log_row {row : Row} {n : Int}
    (hKey : row.key? = some (logTable, n)) :
    Expr.intField? row.visible idField = some n := by
  have h := rowFieldInt?_idField_of_key hKey
  unfold Expr.intField? rowFieldInt? at *
  exact h

/-- Under `wellFormedTableFields vd`, every row's `isLogExpr` predicate
evaluates definitively (some bool). -/
private theorem satisfiesPredicate_isLogExpr_succeeds_of_wellFormed
    {vd : Database} (hWF : wellFormedTableFields vd) (row : Row) (hMem : row ∈ vd) :
    ∃ b, Semantics.satisfiesPredicate rowVar (isLogExpr rowVar) row.visible = some b := by
  rcases hWF row hMem with ⟨t, n, hKey, hTab⟩
  -- Extract the lookup directly: rowFieldInt? = some t ↔ lookup? = some (.int t).
  have hLookup : row.visible.lookup? tableField = some (.int t) := by
    unfold rowFieldInt? at hTab
    cases h : row.visible.lookup? tableField with
    | none => rw [h] at hTab; cases hTab
    | some lit =>
        rw [h] at hTab
        cases lit with
        | int v => simp at hTab; rw [hTab]
        | _ => cases hTab
  refine ⟨decide (t = logTable), ?_⟩
  unfold Semantics.satisfiesPredicate isLogExpr isTableExpr eqExpr fieldExpr
  simp [Semantics.instantiateRecord, Expr.subst, Expr.eval, Literal.toValue,
    Expr.int, hLookup]

/-- Under `wellFormedTableFields vd`, `collectSelected vd rowVar (isLogExpr rowVar)`
succeeds (returns some). This is the static "predicate evaluates definitively"
witness needed to bridge `LazyF → archiveLogEffect` (the `LazyF` existential
over `selected` requires `collectSelected` to succeed). -/
private theorem collectSelected_logs_succeeds_of_wellFormed
    {vd : Database} (hWF : wellFormedTableFields vd) :
    ∃ sel, Semantics.collectSelected vd rowVar (isLogExpr rowVar) = some sel := by
  unfold Semantics.collectSelected
  induction vd with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      have hHead : head ∈ (head :: tail) := List.mem_cons_self
      rcases satisfiesPredicate_isLogExpr_succeeds_of_wellFormed hWF head hHead with ⟨bHead, hHeadSat⟩
      have hWFTail : wellFormedTableFields tail := fun row hMem => hWF row (List.mem_cons_of_mem _ hMem)
      rcases ih hWFTail with ⟨tailSel, hTailGo⟩
      refine ⟨if bHead then head.visible :: tailSel else tailSel, ?_⟩
      simp only [Semantics.collectSelected.go, hHeadSat, hTailGo,
        Bind.bind, Option.bind, Option.some_bind, pure, Pure.pure]

/-- Under `wellFormedTableFields vd`, every row's `isStorageEntryExpr` predicate
evaluates definitively (some bool). Analogous to
`satisfiesPredicate_isLogExpr_succeeds_of_wellFormed`. -/
private theorem satisfiesPredicate_isStorageEntryExpr_succeeds_of_wellFormed
    {vd : Database} (hWF : wellFormedTableFields vd) (row : Row) (hMem : row ∈ vd) :
    ∃ b, Semantics.satisfiesPredicate rowVar (isStorageEntryExpr rowVar) row.visible = some b := by
  rcases hWF row hMem with ⟨t, n, _hKey, hTab⟩
  have hLookup : row.visible.lookup? tableField = some (.int t) := by
    unfold rowFieldInt? at hTab
    cases h : row.visible.lookup? tableField with
    | none => rw [h] at hTab; cases hTab
    | some lit =>
        rw [h] at hTab
        cases lit with
        | int v => simp at hTab; rw [hTab]
        | _ => cases hTab
  by_cases hLog : t = logTable
  · refine ⟨true, ?_⟩
    unfold Semantics.satisfiesPredicate isStorageEntryExpr isLogExpr isArchiveExpr
      isTableExpr orExpr eqExpr fieldExpr
    simp [Semantics.instantiateRecord, Expr.subst, Expr.eval, Literal.toValue,
      Expr.int, hLookup, hLog]
  · by_cases hArch : t = archiveTable
    · refine ⟨true, ?_⟩
      unfold Semantics.satisfiesPredicate isStorageEntryExpr isLogExpr isArchiveExpr
        isTableExpr orExpr eqExpr fieldExpr
      have hArchNeLog : ¬ archiveTable = logTable := by decide
      simp [Semantics.instantiateRecord, Expr.subst, Expr.eval, Literal.toValue,
        Expr.int, hLookup, hLog, hArch, hArchNeLog]
    · refine ⟨false, ?_⟩
      unfold Semantics.satisfiesPredicate isStorageEntryExpr isLogExpr isArchiveExpr
        isTableExpr orExpr eqExpr fieldExpr
      simp [Semantics.instantiateRecord, Expr.subst, Expr.eval, Literal.toValue,
        Expr.int, hLookup, hLog, hArch]

/-- Analogue of `collectSelected_logs_succeeds_of_wellFormed` for storage entries
(`isStorageEntryExpr` instead of `isLogExpr`). -/
private theorem collectSelected_storageEntries_succeeds_of_wellFormed
    {vd : Database} (hWF : wellFormedTableFields vd) :
    ∃ sel, Semantics.collectSelected vd rowVar (isStorageEntryExpr rowVar) = some sel := by
  unfold Semantics.collectSelected
  induction vd with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      have hHead : head ∈ (head :: tail) := List.mem_cons_self
      rcases satisfiesPredicate_isStorageEntryExpr_succeeds_of_wellFormed hWF head hHead with
        ⟨bHead, hHeadSat⟩
      have hWFTail : wellFormedTableFields tail :=
        fun row hMem => hWF row (List.mem_cons_of_mem _ hMem)
      rcases ih hWFTail with ⟨tailSel, hTailGo⟩
      refine ⟨if bHead then head.visible :: tailSel else tailSel, ?_⟩
      simp only [Semantics.collectSelected.go, hHeadSat, hTailGo,
        Bind.bind, Option.bind, Option.some_bind, pure, Pure.pure]

/-- For each `rec ∈ selected`, `collectIntFieldValues` extracts some `n` and
that `n` appears in the produced values list. -/
private theorem mem_collectIntFieldValues_of_mem
    {selected : SetLit} {values : List Int} {rec : RecordLit}
    (hValues : Expr.collectIntFieldValues idField selected = some values)
    (hMem : rec ∈ selected) :
    ∃ n, Expr.intField? rec idField = some n ∧ n ∈ values := by
  induction selected generalizing values with
  | nil => cases hMem
  | cons head tail ih =>
      simp [Expr.collectIntFieldValues, Bind.bind, Option.bind] at hValues
      cases hHd : Expr.intField? head idField with
      | none => simp [hHd] at hValues
      | some headN =>
          cases hTl : Expr.collectIntFieldValues idField tail with
          | none => simp [hHd, hTl] at hValues
          | some tailVals =>
              simp [hHd, hTl] at hValues
              subst hValues
              rcases List.mem_cons.mp hMem with hHead | hTail
              · subst hHead
                exact ⟨headN, hHd, List.mem_cons_self⟩
              · rcases ih hTl hTail with ⟨n, hN, hMem'⟩
                exact ⟨n, hN, List.mem_cons_of_mem _ hMem'⟩

/-- Each value in `values` corresponds to some `rec ∈ selected` whose
`intField? idField` produced it. -/
private theorem exists_mem_selected_of_mem_values
    {selected : SetLit} {values : List Int} {v : Int}
    (hValues : Expr.collectIntFieldValues idField selected = some values)
    (hMem : v ∈ values) :
    ∃ rec, rec ∈ selected ∧ Expr.intField? rec idField = some v := by
  induction selected generalizing values with
  | nil =>
      simp [Expr.collectIntFieldValues] at hValues
      subst hValues
      cases hMem
  | cons head tail ih =>
      simp [Expr.collectIntFieldValues, Bind.bind, Option.bind] at hValues
      cases hHd : Expr.intField? head idField with
      | none => simp [hHd] at hValues
      | some headN =>
          cases hTl : Expr.collectIntFieldValues idField tail with
          | none => simp [hHd, hTl] at hValues
          | some tailVals =>
              simp [hHd, hTl] at hValues
              subst hValues
              rcases List.mem_cons.mp hMem with hHead | hTail
              · subst hHead
                exact ⟨head, List.mem_cons_self, hHd⟩
              · rcases ih hTl hTail with ⟨rec, hRecMem, hRec⟩
                exact ⟨rec, List.mem_cons_of_mem _ hRecMem, hRec⟩

/-- If every `rec ∈ selected` has an integer idField, `collectIntFieldValues`
succeeds. -/
private theorem collectIntFieldValues_succeeds_of_each_intField
    {selected : SetLit}
    (hEach : ∀ rec, rec ∈ selected → ∃ n, Expr.intField? rec idField = some n) :
    ∃ values, Expr.collectIntFieldValues idField selected = some values := by
  induction selected with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      rcases hEach head List.mem_cons_self with ⟨headN, hHd⟩
      have hTailEach : ∀ rec, rec ∈ tail → ∃ n, Expr.intField? rec idField = some n :=
        fun rec hMem => hEach rec (List.mem_cons_of_mem _ hMem)
      rcases ih hTailEach with ⟨tailVals, hTl⟩
      refine ⟨headN :: tailVals, ?_⟩
      simp [Expr.collectIntFieldValues, hHd, hTl, Bind.bind, Option.bind]

/-- `collectIntFieldValues` succeeds when each `rec ∈ selected` comes from a
log row in `vd` (via `collectSelected`) under wellFormedness. -/
private theorem collectIntFieldValues_log_succeeds
    {vd : Database} {selected : SetLit}
    (hSelect : Semantics.collectSelected vd rowVar (isLogExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) :
    ∃ values, Expr.collectIntFieldValues idField selected = some values := by
  refine collectIntFieldValues_succeeds_of_each_intField (fun rec hMem => ?_)
  rcases (mem_selected_iff_log_row hSelect hWF rec).mp hMem with
    ⟨row, _, ⟨n, hKey⟩, hVis⟩
  refine ⟨n, ?_⟩
  rw [← hVis]
  exact intField?_idField_of_log_row hKey

/-- Auxiliary: `List.foldl min init l` is ≤ `init`. -/
private theorem foldl_min_le_init (init : Int) (l : List Int) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
      simp only [List.foldl]
      have h₁ := ih (min init x)
      have h₂ : min init x ≤ init := Int.min_le_left _ _
      omega

/-- Auxiliary: `List.foldl min init l` is ≤ every element of `l`. -/
private theorem foldl_min_le_mem : ∀ (init : Int) (l : List Int) (y : Int), y ∈ l →
    l.foldl min init ≤ y
  | _, [], _, hMem => absurd hMem List.not_mem_nil
  | init, x :: xs, y, hMem => by
      simp only [List.foldl]
      rcases List.mem_cons.mp hMem with rfl | hy
      · have h₁ := foldl_min_le_init (min init y) xs
        have h₂ : min init y ≤ y := Int.min_le_right _ _
        omega
      · exact foldl_min_le_mem (min init x) xs y hy

/-- Auxiliary: `List.foldl min init l` equals `init` or some element of `l`. -/
private theorem foldl_min_eq_init_or_mem : ∀ (init : Int) (l : List Int),
    l.foldl min init = init ∨ ∃ y ∈ l, l.foldl min init = y
  | _, [] => Or.inl rfl
  | init, x :: xs => by
      simp only [List.foldl]
      rcases foldl_min_eq_init_or_mem (min init x) xs with hEq | ⟨y, hyMem, hyEq⟩
      · by_cases h : init ≤ x
        · have hMin : min init x = init := Int.min_eq_left h
          left; rw [hEq, hMin]
        · have h' : x ≤ init := by omega
          have hMin : min init x = x := Int.min_eq_right h'
          right
          refine ⟨x, List.mem_cons_self, ?_⟩
          rw [hEq, hMin]
      · right
        exact ⟨y, List.mem_cons_of_mem _ hyMem, hyEq⟩

private theorem foldl_min_mem (init : Int) (l : List Int) :
    l.foldl min init ∈ init :: l := by
  rcases foldl_min_eq_init_or_mem init l with hEq | ⟨y, hyMem, hyEq⟩
  · rw [hEq]; exact List.mem_cons_self
  · rw [hyEq]; exact List.mem_cons_of_mem _ hyMem

/-! Max analogues. -/

private theorem foldl_max_ge_init (init : Int) (l : List Int) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
      simp only [List.foldl]
      have h₁ := ih (max init x)
      have h₂ : init ≤ max init x := Int.le_max_left _ _
      omega

private theorem foldl_max_ge_mem : ∀ (init : Int) (l : List Int) (y : Int), y ∈ l →
    y ≤ l.foldl max init
  | _, [], _, hMem => absurd hMem List.not_mem_nil
  | init, x :: xs, y, hMem => by
      simp only [List.foldl]
      rcases List.mem_cons.mp hMem with rfl | hy
      · have h₁ := foldl_max_ge_init (max init y) xs
        have h₂ : y ≤ max init y := Int.le_max_right _ _
        omega
      · exact foldl_max_ge_mem (max init x) xs y hy

private theorem foldl_max_eq_init_or_mem : ∀ (init : Int) (l : List Int),
    l.foldl max init = init ∨ ∃ y ∈ l, l.foldl max init = y
  | _, [] => Or.inl rfl
  | init, x :: xs => by
      simp only [List.foldl]
      rcases foldl_max_eq_init_or_mem (max init x) xs with hEq | ⟨y, hyMem, hyEq⟩
      · by_cases h : x ≤ init
        · have hMax : max init x = init := Int.max_eq_left h
          left; rw [hEq, hMax]
        · have h' : init ≤ x := by omega
          have hMax : max init x = x := Int.max_eq_right h'
          right
          refine ⟨x, List.mem_cons_self, ?_⟩
          rw [hEq, hMax]
      · right
        exact ⟨y, List.mem_cons_of_mem _ hyMem, hyEq⟩

private theorem foldl_max_mem (init : Int) (l : List Int) :
    l.foldl max init ∈ init :: l := by
  rcases foldl_max_eq_init_or_mem init l with hEq | ⟨y, hyMem, hyEq⟩
  · rw [hEq]; exact List.mem_cons_self
  · rw [hyEq]; exact List.mem_cons_of_mem _ hyMem

private theorem maxInt?_eq_some_iff (values : List Int) (hi : Int) :
    Expr.maxInt? values = some hi ↔
      hi ∈ values ∧ ∀ v ∈ values, v ≤ hi := by
  cases values with
  | nil => simp [Expr.maxInt?]
  | cons head tail =>
      simp [Expr.maxInt?]
      constructor
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases foldl_max_eq_init_or_mem head tail with hEq | ⟨y, hyMem, hyEq⟩
          · left; exact hEq
          · right; rw [hyEq]; exact hyMem
        · exact foldl_max_ge_init _ _
        · intro v hMem
          exact foldl_max_ge_mem _ _ _ hMem
      · rintro ⟨hMem, hUB_head, hUB_tail⟩
        have hMax_eq_or_mem := foldl_max_eq_init_or_mem head tail
        have hMax_ge_hi : hi ≤ tail.foldl max head := by
          rcases hMem with rfl | hMem
          · exact foldl_max_ge_init _ _
          · exact foldl_max_ge_mem _ _ _ hMem
        have hMax_le_hi : tail.foldl max head ≤ hi := by
          rcases hMax_eq_or_mem with hEq | ⟨y, hyMem, hyEq⟩
          · rw [hEq]; exact hUB_head
          · rw [hyEq]; exact hUB_tail _ hyMem
        omega

/-- `Expr.minInt?` characterization: the returned value is a member, and a
lower bound for every member. -/
private theorem minInt?_eq_some_iff (values : List Int) (lo : Int) :
    Expr.minInt? values = some lo ↔
      lo ∈ values ∧ ∀ v ∈ values, lo ≤ v := by
  cases values with
  | nil => simp [Expr.minInt?]
  | cons head tail =>
      simp [Expr.minInt?]
      constructor
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases foldl_min_eq_init_or_mem head tail with hEq | ⟨y, hyMem, hyEq⟩
          · left; exact hEq
          · right; rw [hyEq]; exact hyMem
        · exact foldl_min_le_init _ _
        · intro v hMem
          exact foldl_min_le_mem _ _ _ hMem
      · rintro ⟨hMem, hLB_head, hLB_tail⟩
        have hMin_eq_or_mem := foldl_min_eq_init_or_mem head tail
        have hMin_le_lo : tail.foldl min head ≤ lo := by
          rcases hMem with rfl | hMem
          · exact foldl_min_le_init _ _
          · exact foldl_min_le_mem _ _ _ hMem
        have hLo_le_min : lo ≤ tail.foldl min head := by
          rcases hMin_eq_or_mem with hEq | ⟨y, hyMem, hyEq⟩
          · rw [hEq]; exact hLB_head
          · rw [hyEq]; exact hLB_tail _ hyMem
        omega

/-- The bridge: under `collectSelected vd "row" isLogExpr = some selected` and
wellFormedness, `selectedLitMin selected = some lo` is equivalent to
`selectedLogMin vd lo`. Both characterise "lo = min log id in vd". -/
private theorem selectedLitMin_iff_selectedLogMin
    {vd : Database} {selected : SetLit} {lo : Int}
    (hSelect : Semantics.collectSelected vd rowVar (isLogExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) :
    selectedLitMin selected = some lo ↔ selectedLogMin vd lo := by
  rcases collectIntFieldValues_log_succeeds hSelect hWF with ⟨values, hValues⟩
  have hLitMin_iff : selectedLitMin selected = some lo ↔
      Expr.minInt? values = some lo := by
    unfold selectedLitMin
    simp only [Expr.eval, Literal.toValue, hValues, Bind.bind, Option.bind, Option.some_bind]
    cases hMin : Expr.minInt? values with
    | none =>
        simp [hMin]
    | some m =>
        simp [hMin]
  rw [hLitMin_iff, minInt?_eq_some_iff]
  unfold selectedLogMin selectedLogRow
  constructor
  · rintro ⟨hMem, hLB⟩
    -- lo ∈ values: get the rec and log row witness for lo
    rcases exists_mem_selected_of_mem_values hValues hMem with ⟨rec, hRecMem, hRecField⟩
    rcases (mem_selected_iff_log_row hSelect hWF rec).mp hRecMem with
      ⟨row, hRowMem, ⟨n, hKey⟩, hVis⟩
    -- intField? row.visible idField = some n; and = some lo from hRecField (since rec = row.visible)
    have hN : n = lo := by
      have hHas := intField?_idField_of_log_row hKey
      rw [hVis] at hHas
      rw [hHas] at hRecField
      exact Option.some.inj hRecField
    subst hN
    refine ⟨⟨row, hRowMem, hKey⟩, ?_⟩
    intro row' n' ⟨hRow'Mem, hKey'⟩
    -- row'.visible ∈ selected with intField? = some n'
    have hRecMem' : row'.visible ∈ selected :=
      (mem_selected_iff_log_row hSelect hWF row'.visible).mpr
        ⟨row', hRow'Mem, ⟨n', hKey'⟩, rfl⟩
    rcases mem_collectIntFieldValues_of_mem hValues hRecMem' with ⟨n'', hN''Field, hN''Mem⟩
    have hN''_eq : n'' = n' := by
      have hHas := intField?_idField_of_log_row hKey'
      rw [hHas] at hN''Field
      exact (Option.some.inj hN''Field).symm
    subst hN''_eq
    exact hLB _ hN''Mem
  · rintro ⟨⟨row, hRowMem, hKey⟩, hMin⟩
    -- selectedLogMin: row witnesses min, and lo is LB for log ids
    have hVisMem : row.visible ∈ selected :=
      (mem_selected_iff_log_row hSelect hWF row.visible).mpr
        ⟨row, hRowMem, ⟨lo, hKey⟩, rfl⟩
    rcases mem_collectIntFieldValues_of_mem hValues hVisMem with ⟨n, hNField, hNMem⟩
    have hN_eq_lo : n = lo := by
      have hHas := intField?_idField_of_log_row hKey
      rw [hHas] at hNField
      exact (Option.some.inj hNField).symm
    subst hN_eq_lo
    refine ⟨hNMem, ?_⟩
    intro v hVMem
    rcases exists_mem_selected_of_mem_values hValues hVMem with ⟨rec', hRecMem', hRecField'⟩
    rcases (mem_selected_iff_log_row hSelect hWF rec').mp hRecMem' with
      ⟨row', hRow'Mem, ⟨n', hKey'⟩, hVis'⟩
    have hN'_eq_v : n' = v := by
      have hHas := intField?_idField_of_log_row hKey'
      rw [hVis'] at hHas
      rw [hHas] at hRecField'
      exact Option.some.inj hRecField'
    subst hN'_eq_v
    exact hMin row' n' ⟨hRow'Mem, hKey'⟩

/-- Max analogue of `selectedLitMin_iff_selectedLogMin`. -/
private theorem selectedLitMax_iff_selectedLogMax
    {vd : Database} {selected : SetLit} {hi : Int}
    (hSelect : Semantics.collectSelected vd rowVar (isLogExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) :
    selectedLitMax selected = some hi ↔ selectedLogMax vd hi := by
  rcases collectIntFieldValues_log_succeeds hSelect hWF with ⟨values, hValues⟩
  have hLitMax_iff : selectedLitMax selected = some hi ↔
      Expr.maxInt? values = some hi := by
    unfold selectedLitMax
    simp only [Expr.eval, Literal.toValue, hValues, Bind.bind, Option.bind, Option.some_bind]
    cases hMax : Expr.maxInt? values with
    | none => simp [hMax]
    | some m => simp [hMax]
  rw [hLitMax_iff, maxInt?_eq_some_iff]
  unfold selectedLogMax selectedLogRow
  constructor
  · rintro ⟨hMem, hUB⟩
    rcases exists_mem_selected_of_mem_values hValues hMem with ⟨rec, hRecMem, hRecField⟩
    rcases (mem_selected_iff_log_row hSelect hWF rec).mp hRecMem with
      ⟨row, hRowMem, ⟨n, hKey⟩, hVis⟩
    have hN : n = hi := by
      have hHas := intField?_idField_of_log_row hKey
      rw [hVis] at hHas
      rw [hHas] at hRecField
      exact Option.some.inj hRecField
    subst hN
    refine ⟨⟨row, hRowMem, hKey⟩, ?_⟩
    intro row' n' ⟨hRow'Mem, hKey'⟩
    have hRecMem' : row'.visible ∈ selected :=
      (mem_selected_iff_log_row hSelect hWF row'.visible).mpr
        ⟨row', hRow'Mem, ⟨n', hKey'⟩, rfl⟩
    rcases mem_collectIntFieldValues_of_mem hValues hRecMem' with ⟨n'', hN''Field, hN''Mem⟩
    have hN''_eq : n'' = n' := by
      have hHas := intField?_idField_of_log_row hKey'
      rw [hHas] at hN''Field
      exact (Option.some.inj hN''Field).symm
    subst hN''_eq
    exact hUB _ hN''Mem
  · rintro ⟨⟨row, hRowMem, hKey⟩, hMax⟩
    have hVisMem : row.visible ∈ selected :=
      (mem_selected_iff_log_row hSelect hWF row.visible).mpr
        ⟨row, hRowMem, ⟨hi, hKey⟩, rfl⟩
    rcases mem_collectIntFieldValues_of_mem hValues hVisMem with ⟨n, hNField, hNMem⟩
    have hN_eq_hi : n = hi := by
      have hHas := intField?_idField_of_log_row hKey
      rw [hHas] at hNField
      exact (Option.some.inj hNField).symm
    subst hN_eq_hi
    refine ⟨hNMem, ?_⟩
    intro v hVMem
    rcases exists_mem_selected_of_mem_values hValues hVMem with ⟨rec', hRecMem', hRecField'⟩
    rcases (mem_selected_iff_log_row hSelect hWF rec').mp hRecMem' with
      ⟨row', hRow'Mem, ⟨n', hKey'⟩, hVis'⟩
    have hN'_eq_v : n' = v := by
      have hHas := intField?_idField_of_log_row hKey'
      rw [hVis'] at hHas
      rw [hHas] at hRecField'
      exact Option.some.inj hRecField'
    subst hN'_eq_v
    exact hMax row' n' ⟨hRow'Mem, hKey'⟩

def archiveLogInsertEffect_with_selected
    (txnId : TxnId) (i : Nat) (selected : SetLit) : SetLanguage.SetExpr :=
  fun _localDb _globalDb out =>
    ∃ lo hi0,
      selectedLitMin selected = some lo ∧
      selectedLitMax selected = some hi0 ∧
      out = archiveRow txnId i lo (hi0 + 1)

def archiveLogDeleteEffect_with_selected
    (txnId : TxnId) (selected : SetLit) : SetLanguage.SetExpr :=
  fun _localDb globalDb out =>
    ∃ src n lo hi0,
      selectedLitMin selected = some lo ∧
      selectedLitMax selected = some hi0 ∧
      src ∈ globalDb ∧ src.key? = some (logTable, n) ∧
      lo ≤ n ∧ n ≤ hi0 ∧
      out = src.markDeleted txnId

def archiveLogEffect_with_selected (txnId : TxnId) (i : Nat) (selected : SetLit) :
    SetLanguage.SetExpr :=
  .union (archiveLogInsertEffect_with_selected txnId i selected)
    (archiveLogDeleteEffect_with_selected txnId selected)

def selectLogResultEffect (txnId : TxnId) (q : Nat) (entry : Row) :
    SetLanguage.SetExpr :=
  fun _localDb _globalDb out =>
    ∃ n,
      (∃ id, entry.key? = some (logTable, id)) ∧
        rowFieldInt? entry idField = some n ∧
        out = resultRowLit txnId q n

def selectArchiveResultEffect (txnId : TxnId) (q : Nat) (entry : Row) :
    SetLanguage.SetExpr :=
  fun _localDb _globalDb out =>
    ∃ lo hi n,
      (∃ id, entry.key? = some (archiveTable, id)) ∧
        rowFieldInt? entry loField = some lo ∧
        rowFieldInt? entry hiField = some hi ∧
        lo ≤ n ∧
        n < hi ∧
        out = resultRowLit txnId q n

def selectEntryResultEffect (txnId : TxnId) (q : Nat) (entry : Row) :
    SetLanguage.SetExpr :=
  .union (selectLogResultEffect txnId q entry) (selectArchiveResultEffect txnId q entry)

def selectedStorageEntriesSet : SetLanguage.SetExpr :=
  globalSelectionSet emptySymEnv rowVar (isStorageEntryExpr rowVar)

def selectAllLogEffect (txnId : TxnId) (q : Nat) : SetLanguage.SetExpr :=
  SetLanguage.SetExpr.bind selectedStorageEntriesSet
    (fun entry => selectEntryResultEffect txnId q entry)

/-- `selectAllLogEffect_with_selected`: parametrized over the captured
`selected` SetLit (= what `collectSelected` returns). The iteration is over
entries in `selected`, and for each we look up the source row in `globalDb`
to apply `selectEntryResultEffect`. Used as the `Fbody` for
`PaperInfer.selectLazy` in `paperInfer_selectAllLogBody_via_lazy`. -/
def selectAllLogEffect_with_selected (txnId : TxnId) (q : Nat) (selected : SetLit) :
    SetLanguage.SetExpr :=
  fun localDb globalDb row =>
    ∃ entry, entry ∈ selected ∧
      ∃ srcRow, srcRow ∈ globalDb ∧ srcRow.visible = entry ∧
        selectEntryResultEffect txnId q srcRow localDb globalDb row

theorem selectedStorageEntriesSet_denote_iff (db : Database) (row : Row) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) selectedStorageEntriesSet row ↔
      row ∈ db ∧ (rowFieldInt? row tableField = some logTable ∨
        rowFieldInt? row tableField = some archiveTable) := by
  unfold selectedStorageEntriesSet emptySymEnv
  rw [globalSelectionSet_closed_denote_iff]
  exact and_congr_right (fun _ => satisfiesPredicate_isStorageEntryExpr_iff row)

theorem rowFieldInt?_tableField_eq_table?_int_some {row : Row} {table : TableName}
    (h : rowFieldInt? row tableField = some table) :
    row.visible.table? = some table := by
  unfold rowFieldInt? tableField at h
  unfold RecordLit.table?
  cases hL : row.visible.lookup? "table" with
  | none => rw [hL] at h; cases h
  | some lit =>
    cases lit with
    | int v =>
      rw [hL] at h; simp at h
      simp [hL, h]
    | _ => rw [hL] at h; cases h

/-! ## Bridges from obligations to txnSpec -/

/-- TODO: prove `relyNoUndo R_archive` from R_archive's monotonicity in `next`
and result rows. The current spec of G_insert/G_select is content-only, so
list equality may need to be derived via additional structural arguments
or by tightening G's. Stubbed for now to allow the rest of the SI pipeline
to compose. -/
theorem relyNoUndo_R_archive : relyNoUndo R_archive := by
  sorry

/-- Same caveat as `relyNoUndo_R_archive`. -/
theorem relyNoUndo_R_select (q : Nat) : relyNoUndo (R_select q) := by
  sorry

/-- Under False rely, a `.letE` with non-evaluating expression is stuck — no
multistep transition leaves it. -/
private theorem localMultiStep_false_from_letE_none
    (txnId : TxnId) {x : VarName} {expr : Expr}
    {body : Semantics.Program}
    (hNone : Expr.eval expr = none)
    {localDb visibleDb : Database}
    {finalCfg : LocalConfig (IsolationSpec Database)}
    (h : Logic.LocalMultiStep (fun _ _ _ => False) txnId (IsolationSpec Database)
      ⟨(.letE x expr body : Semantics.Program), localDb, visibleDb⟩ finalCfg) :
    finalCfg = ⟨(.letE x expr body : Semantics.Program), localDb, visibleDb⟩ := by
  induction h with
  | refl => rfl
  | tail _hPrev hLast ih =>
      cases ih
      exfalso
      rcases Logic.localInterleavedStep_let_inv hLast with ⟨_val, hEval, _⟩ | ⟨_, _, hRely⟩
      · rw [hEval] at hNone; cases hNone
      · exact hRely

/-- `LocalValid` for a `.letE` whose expression doesn't evaluate is vacuously
true under False rely (the body never reaches skip). -/
private theorem localValid_letE_none_false (txnId : TxnId)
    (P Q : BiAssertion) (x : VarName) (expr : Expr)
    (body : Semantics.Program)
    (hNone : Expr.eval expr = none) :
    Logic.LocalValid (fun _ _ _ => False) txnId P (.letE x expr body) Q := by
  intro localDb visibleDb finalCfg _hP hMulti hSkip
  have hEq := localMultiStep_false_from_letE_none txnId hNone hMulti
  cases hEq
  cases hSkip

/-- `collectSelected.go` returning `some []` implies no row in `db` matches. -/
private theorem collectSelected_go_empty_no_match
    {db : Database} {x : VarName} {predicate : Expr}
    (h : Semantics.collectSelected.go x predicate db = some []) :
    ∀ row, row ∈ db →
      Semantics.satisfiesPredicate x predicate row.visible = some false := by
  induction db with
  | nil => intro row hMem; cases hMem
  | cons head tail ih =>
      intro row hMem
      cases hKeep : Semantics.satisfiesPredicate x predicate head.visible with
      | none =>
          simp [Semantics.collectSelected.go, hKeep] at h
      | some keep =>
          cases hRest : Semantics.collectSelected.go x predicate tail with
          | none =>
              simp [Semantics.collectSelected.go, hKeep, hRest] at h
          | some rest =>
              cases keep with
              | true =>
                  -- if-true: head.visible :: rest = [], absurd
                  simp [Semantics.collectSelected.go, hKeep, hRest] at h
              | false =>
                  -- if-false: rest = []
                  have hRestEmpty : rest = [] := by
                    simpa [Semantics.collectSelected.go, hKeep, hRest] using h
                  subst hRestEmpty
                  rcases List.mem_cons.mp hMem with rfl | hTail
                  · exact hKeep
                  · exact ih hRest row hTail

/-- `collectSelected db x predicate = some []` implies no row in `db` satisfies
the predicate. -/
private theorem collectSelected_empty_no_match
    {db : Database} {x : VarName} {predicate : Expr}
    (h : Semantics.collectSelected db x predicate = some []) :
    ∀ row, row ∈ db →
      Semantics.satisfiesPredicate x predicate row.visible = some false := by
  exact collectSelected_go_empty_no_match (by simpa [Semantics.collectSelected] using h)

/-- Under SI's local rely, env steps are silent on visible: `v = v'`. -/
theorem relyMod_snapshot_exec_silent {R : Rely} :
    ∀ localDb v v',
      Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec localDb v v' →
        v' = v := by
  intro _ v v' hStep
  rcases hStep with ⟨baseDb, _hR, hI, hI'⟩
  -- hI : baseDb = v ; hI' : baseDb = v'
  exact hI'.symm.trans hI

/-- transformerPre is trivially stable under SI's silent local rely. -/
theorem transformerPre_stable_relyMod_snapshot {R : Rely}
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
      (transformerPre I Fctxt) := by
  intro localDb v v' hPre hStep
  have hEq := relyMod_snapshot_exec_silent localDb v v' hStep
  rw [hEq]
  exact hPre

/-- transformerPost is trivially stable under SI's silent local rely. -/
theorem transformerPost_stable_relyMod_snapshot {R : Rely}
    (Fctxt F : SetLanguage.SetExpr) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
      (transformerPost Fctxt F) := by
  intro localDb v v' hPost hStep
  have hEq := relyMod_snapshot_exec_silent localDb v v' hStep
  rw [hEq]
  exact hPost

theorem archiveLogTxnSpec_of_paperObligations (i : Nat)
    (hObligations : ArchiveLogPaperObligations i) :
    archiveLogTxnSpec i := by
  have hCommitPost :
      ∀ localDb visibleDb,
        logSystemInv visibleDb →
          txnSnapshotPost logSystemInv R_archive hObligations.effect localDb visibleDb →
            logSystemInv (Database.flush localDb visibleDb) := by
    intro localDb visibleDb _hPre hPost
    have hG : G_archive visibleDb (Database.flush localDb visibleDb) :=
      hObligations.guarantee localDb visibleDb hPost
    rcases hPost with ⟨snapDb', hSnapInv', hReach', _⟩
    have hVisInv : logSystemInv visibleDb :=
      logSystemInv_stable_multiStep logSystemInv_stable_R_archive hReach' hSnapInv'
    exact G_archive_preserves_logSystemInv hVisInv hG
  have hMain := globalValid_snapshot_of_paperObligations_post
    (R := R_archive) (Iinfer := logSystemInv) (Ipre := logSystemInv) (Ipost := logSystemInv)
    (G := G_archive) (txnId := archiveTxnId i) (body := archiveLogBody i)
    relyNoUndo_R_archive
    logSystemInv_stable_R_archive
    logSystemInv_stable_R_archive
    logSystemInv_stable_R_archive
    (fun _ h => h)
    hObligations
    hCommitPost
  simpa [archiveLogTxnSpec, txnSpecValid, txnSpecProgram, archiveLogSpec,
    ArchiveLogPaperObligations]
    using hMain

theorem selectAllLogTxnSpec_of_paperObligations (q : Nat)
    (hObligations : SelectAllLogPaperObligations q) :
    selectAllLogTxnSpec q := by
  have hCommitPost :
      ∀ localDb visibleDb,
        logSystemInv visibleDb →
          txnSnapshotPost logSystemInv (R_select q) hObligations.effect localDb visibleDb →
            logSystemInv (Database.flush localDb visibleDb) := by
    intro localDb visibleDb _hPre hPost
    have hG : G_select q visibleDb (Database.flush localDb visibleDb) :=
      hObligations.guarantee localDb visibleDb hPost
    rcases hPost with ⟨snapDb', hSnapInv', hReach', _⟩
    have hVisInv : logSystemInv visibleDb :=
      logSystemInv_stable_multiStep (logSystemInv_stable_R_select q) hReach' hSnapInv'
    exact G_select_preserves_logSystemInv hVisInv hG
  have hMain := globalValid_snapshot_of_paperObligations_post
    (R := R_select q) (Iinfer := logSystemInv) (Ipre := logSystemInv) (Ipost := logSystemInv)
    (G := G_select q) (txnId := selectTxnId q) (body := selectAllLogBody q)
    (relyNoUndo_R_select q)
    (logSystemInv_stable_R_select q)
    (logSystemInv_stable_R_select q)
    (logSystemInv_stable_R_select q)
    (fun _ h => h)
    hObligations
    hCommitPost
  simpa [selectAllLogTxnSpec, txnSpecValid, txnSpecProgram, selectAllLogSpec,
    SelectAllLogPaperObligations]
    using hMain

theorem insertLogIndexedTxnSpec_of_indexedPaperObligations (i : Nat)
    (hObligations : InsertLogPaperObligations i) :
    insertLogIndexedTxnSpec i := by
  simpa [insertLogIndexedTxnSpec, txnSpecValid, txnSpecProgram, insertLogIndexedSpec,
    insertLogTxn]
    using
      globalValid_readCommitted_of_paperObligations_post
        (logSystemInvAtNext_stable_R_insert i)
        (logSystemInvAtNext_stable_R_insert i)
        (logSystemInvAtNext_stable_R_insert (i + 1))
        (fun _ hInv => hInv)
        hObligations
        (fun localDb visibleDb hInv hPost =>
          G_insert_preserves_logSystemInvAtNext_succ hInv
            (hObligations.guarantee localDb visibleDb hPost))

/-! ## Local-row characterizations of `selectAllLogEffect` -/

theorem selectAllLogSnapshotPost_local_rows_are_results
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ row, row ∈ localDb → ∃ n : Int, row = resultRowLit (selectTxnId q) q n := by
  intro row hMem
  rcases hPost with ⟨snapshotDb, _hSnapshotInv, _hReach, hRows⟩
  have hDenote :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (selectAllLogEffect (selectTxnId q) q) row :=
    (hRows row).2 hMem
  simp [selectAllLogEffect, selectEntryResultEffect, selectLogResultEffect,
    selectArchiveResultEffect] at hDenote
  rcases hDenote with ⟨_entry, _hEntry, hOut⟩
  rcases hOut with hLog | hArchive
  · rcases hLog with ⟨n, _hKey, _hN, hRow⟩
    exact ⟨n, hRow⟩
  · rcases hArchive with ⟨_lo, _hi, n, _hKey, _hLo, _hHi, _hLe, _hLt, hRow⟩
    exact ⟨n, hRow⟩

theorem selectAllLogSnapshotPost_local_keyDom_results
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ key, key ∈ localDb.keyDom → ∃ n : Int, key = (resultTable q, n) := by
  intro key hKeyDom
  unfold Database.keyDom at hKeyDom
  simp [List.mem_filterMap] at hKeyDom
  rcases hKeyDom with ⟨row, hMem, hKey⟩
  rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row hMem with
    ⟨n, hEq⟩
  subst hEq
  rw [resultRowLit_key?] at hKey
  exact ⟨n, (Option.some.inj hKey).symm⟩

/-! ## Local-row characterization of `archiveLogEffect` -/

theorem markDeleted_key? (row : Row) (txnId : TxnId) :
    (row.markDeleted txnId).key? = row.key? := by
  simp [Row.key?, Row.markDeleted]

theorem archiveLogSnapshotPost_local_row_key
    (i : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)
        localDb visibleDb) :
    ∀ row, row ∈ localDb →
      row.key? = some (archiveTable, (i : Int)) ∨
        ∃ n : Int, row.key? = some (logTable, n) := by
  intro row hMem
  rcases hPost with ⟨snapshotDb, _hSnapshotInv, _hReach, hRows⟩
  have hDenote :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (archiveLogEffect (archiveTxnId i) i) row :=
    (hRows row).2 hMem
  simp [archiveLogEffect, archiveLogInsertEffect, archiveLogDeleteEffect,
    SetLanguage.denote_union] at hDenote
  rcases hDenote with hInsert | hDelete
  · rcases hInsert with ⟨lo, hi0, _hMin, _hMax, hRow⟩
    subst hRow
    exact Or.inl (archiveRow_key? (archiveTxnId i) i lo (hi0 + 1))
  · rcases hDelete with ⟨src, n, _lo, _hi0, _hMin, _hMax, hSel, _hLo, _hHi, hRow⟩
    rcases hSel with ⟨_hMem, hKey⟩
    subst hRow
    exact Or.inr ⟨n, (markDeleted_key? src (archiveTxnId i)).trans hKey⟩

/-- Local rows of the select transaction live alive (they are result rows
returned by the body, not delete markers). -/
theorem selectAllLogSnapshotPost_local_rows_live
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ row, row ∈ localDb → liveRow row := by
  intro row hMem
  rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row hMem with
    ⟨n, hEq⟩
  subst hEq
  simp [liveRow, resultRowLit, Row.fromInsert]

/-- Result-row literal n-injection. -/
theorem resultRowLit_n_inj {txnId : TxnId} {q : Nat} {n m : Int}
    (h : resultRowLit txnId q n = resultRowLit txnId q m) : n = m := by
  have hKey : (resultRowLit txnId q n).key? = (resultRowLit txnId q m).key? := by rw [h]
  rw [resultRowLit_key?, resultRowLit_key?] at hKey
  exact (Prod.mk.inj (Option.some.inj hKey)).2

/-- Resolve `resultRowFor localDb q n` to membership of `resultRowLit (selectTxnId q) q n`. -/
theorem selectAllLogSnapshotPost_local_resultRowFor_iff
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ n : Int, resultRowFor localDb q n ↔
      resultRowLit (selectTxnId q) q n ∈ localDb := by
  intro n
  constructor
  · rintro ⟨row, hMem, _hLive, hKey⟩
    rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row hMem with
      ⟨m, hEq⟩
    subst hEq
    have hEqKey : (resultRowLit (selectTxnId q) q m).key? = some (resultTable q, n) := hKey
    rw [resultRowLit_key?] at hEqKey
    have hPair : (resultTable q, m) = (resultTable q, n) := Option.some.inj hEqKey
    have : m = n := (Prod.mk.inj hPair).2
    subst this
    exact hMem
  · intro hMem
    refine ⟨resultRowLit (selectTxnId q) q n, hMem, ?_, ?_⟩
    · simp [liveRow, resultRowLit, Row.fromInsert]
    · exact resultRowLit_key? (selectTxnId q) q n

/-- The denotation of `selectAllLogEffect` at the snapshot, restricted to result-row
literals, characterizes exactly `expandedLog snapshot`. -/
theorem selectAllLogEffect_resultRowLit_iff_expanded
    (q : Nat) (snapshotDb : Database) (n : Int)
    (hSnapshotInv : logSystemInv snapshotDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (selectAllLogEffect (selectTxnId q) q) (resultRowLit (selectTxnId q) q n) ↔
      expandedLog snapshotDb n := by
  rcases hSnapshotInv with ⟨_cut, _next, hShape, _hResults, hWFTable⟩
  rcases hShape with ⟨_hCut, _hCounter, _hCounterAtZero, _hHaveNext,
    hStorageLive, _hLiveLog, _hArchive, _hIntervals⟩
  unfold selectAllLogEffect
  rw [SetLanguage.denote_bind]
  constructor
  · rintro ⟨entry, hEntry, hOut⟩
    rw [selectedStorageEntriesSet_denote_iff] at hEntry
    rcases hEntry with ⟨hMem, _hTable⟩
    rw [show selectEntryResultEffect (selectTxnId q) q entry =
      .union (selectLogResultEffect (selectTxnId q) q entry)
        (selectArchiveResultEffect (selectTxnId q) q entry) from rfl] at hOut
    rw [SetLanguage.denote_union] at hOut
    rcases hOut with hLog | hArchiveCase
    · change (∃ m, (∃ id, entry.key? = some (logTable, id)) ∧
        rowFieldInt? entry idField = some m ∧
          resultRowLit (selectTxnId q) q n = resultRowLit (selectTxnId q) q m) at hLog
      rcases hLog with ⟨m, ⟨id, hEntryKey⟩, hN, hRow⟩
      have hMNeq : n = m := resultRowLit_n_inj hRow
      subst hMNeq
      have hLive : liveRow entry := hStorageLive entry hMem (Or.inr (Or.inl ⟨id, hEntryKey⟩))
      have hIdEq : id = n := by
        have hExtract := rowFieldInt?_idField_of_key hEntryKey
        rw [hN] at hExtract
        exact (Option.some.inj hExtract).symm
      subst hIdEq
      exact Or.inl ⟨entry, hMem, hLive, hEntryKey⟩
    · change (∃ lo hi m, (∃ id, entry.key? = some (archiveTable, id)) ∧
        rowFieldInt? entry loField = some lo ∧
          rowFieldInt? entry hiField = some hi ∧
          lo ≤ m ∧ m < hi ∧
          resultRowLit (selectTxnId q) q n = resultRowLit (selectTxnId q) q m) at hArchiveCase
      rcases hArchiveCase with ⟨lo, hi, m, ⟨id, hEntryKey⟩, hLo, hHi, hLe, hLt, hRow⟩
      have : n = m := resultRowLit_n_inj hRow
      subst this
      have hLive : liveRow entry :=
        hStorageLive entry hMem (Or.inr (Or.inr ⟨id, hEntryKey⟩))
      exact Or.inr ⟨entry, id, lo, hi, hMem, hLive, hEntryKey, hLo, hHi, hLe, hLt⟩
  · intro hExpanded
    rcases hExpanded with hLog | hArchiveCase
    · rcases hLog with ⟨entry, hMem, _hLive, hEntryKey⟩
      have hTableF : rowFieldInt? entry tableField = some logTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWFTable hMem hEntryKey
      refine ⟨entry, ?_, ?_⟩
      · rw [selectedStorageEntriesSet_denote_iff]
        exact ⟨hMem, Or.inl hTableF⟩
      · change (∃ m, (∃ id, entry.key? = some (logTable, id)) ∧
          rowFieldInt? entry idField = some m ∧
            resultRowLit (selectTxnId q) q n = resultRowLit (selectTxnId q) q m) ∨ _
        left
        refine ⟨n, ⟨n, hEntryKey⟩, rowFieldInt?_idField_of_key hEntryKey, rfl⟩
    · rcases hArchiveCase with ⟨entry, id, lo, hi, hMem, _hLive, hEntryKey, hLo, hHi, hLe, hLt⟩
      have hTableF : rowFieldInt? entry tableField = some archiveTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWFTable hMem hEntryKey
      refine ⟨entry, ?_, ?_⟩
      · rw [selectedStorageEntriesSet_denote_iff]
        exact ⟨hMem, Or.inr hTableF⟩
      · change _ ∨ (∃ lo' hi' m, (∃ id, entry.key? = some (archiveTable, id)) ∧
          rowFieldInt? entry loField = some lo' ∧
            rowFieldInt? entry hiField = some hi' ∧
            lo' ≤ m ∧ m < hi' ∧
            resultRowLit (selectTxnId q) q n = resultRowLit (selectTxnId q) q m)
        right
        exact ⟨lo, hi, n, ⟨id, hEntryKey⟩, hLo, hHi, hLe, hLt, rfl⟩

theorem selectAllLogSnapshotPost_local_result_prefix
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∃ k : Nat, ∀ n : Nat,
      resultRowLit (selectTxnId q) q n ∈ localDb ↔ n < k := by
  rcases hPost with ⟨snapshotDb, hSnapshotInv, _hReach, hRows⟩
  rcases logSystemInv_expandedLog_prefix hSnapshotInv with ⟨k, hPrefix⟩
  refine ⟨k, ?_⟩
  intro n
  rw [← hRows (resultRowLit (selectTxnId q) q n),
    selectAllLogEffect_resultRowLit_iff_expanded q snapshotDb n hSnapshotInv,
    hPrefix n]

theorem selectAllLogSnapshotPost_local_result_expanded_visible
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ n : Nat,
      resultRowLit (selectTxnId q) q n ∈ localDb → expandedLog visibleDb n := by
  rcases hPost with ⟨snapshotDb, hSnapshotInv, hReach, hRows⟩
  intro n hMem
  have hSnapshotExpanded : expandedLog snapshotDb n :=
    (selectAllLogEffect_resultRowLit_iff_expanded q snapshotDb n hSnapshotInv).1
      ((hRows _).2 hMem)
  exact R_select_multiStep_preserves_expandedLog hReach hSnapshotInv hSnapshotExpanded



/-! ## PaperInfer / stability helpers -/

theorem stable_transformerPre_empty_readCommitted
    {R : Rely} {I : Assertion}
    (hStableI : Logic.stableAssertion R I) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
      (transformerPre I SetLanguage.empty) := by
  intro localDb visibleDb visibleDb' hPre hStep
  rcases (transformerPre_empty_iff I localDb visibleDb).mp hPre with ⟨hLocal, hInv⟩
  rcases hStep with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
  exact (transformerPre_empty_iff I localDb visibleDb').mpr ⟨hLocal, hStableI _ _ hInv hR⟩

theorem stable_transformerPost_empty_insertedRowSet
    {R : LocalRely} (txnId : TxnId) (expr : Expr) :
    Logic.stableBiAssertion R
      (transformerPost SetLanguage.empty
        (insertedRowSet txnId emptySymEnv expr)) := by
  intro localDb visibleDb visibleDb' hPost _hStep
  intro row
  specialize hPost row
  simpa [transformerPost, SetLanguage.denote_union, SetLanguage.empty,
    insertedRowSet, emptySymEnv] using hPost

theorem stable_transformerPre_empty_union_insertedRowSet_readCommitted
    {R : Rely} {I : Assertion}
    (hStableI : Logic.stableAssertion R I)
    (txnId : TxnId) (expr : Expr) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
      (transformerPre I
        (.union SetLanguage.empty (insertedRowSet txnId emptySymEnv expr))) := by
  intro localDb visibleDb visibleDb' hPre hStep
  rcases hPre with ⟨hRows, hInv⟩
  rcases hStep with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
  refine ⟨?_, hStableI _ _ hInv hR⟩
  intro row
  specialize hRows row
  simpa [SetLanguage.denote_union, SetLanguage.empty, insertedRowSet, emptySymEnv]
    using hRows

/-- Reusable PaperInfer derivation for `insertLogBody i` under any stable
invariant. The `viaLocalValid` escape hatch is used for the inner `.insert`
because the generic `PaperInfer.insert` rule needs a syntactic freshness
side-condition that is not directly available; the operational
`Logic.localValid_insert` gets `insertFresh` from the runtime step instead. -/
theorem paperInfer_insertLogBody_of_stable
    (R : Rely) (I : Assertion) (txnId : TxnId) (i : Nat)
    (hStableI : Logic.stableAssertion R I) :
    PaperInfer
      (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
      txnId I SetLanguage.empty (insertLogBody i)
      (insertLogEffect txnId i) := by
  let inserted := insertedRowSet txnId emptySymEnv (logRecordExpr (.int i))
  let updated := updateSetExpr txnId [] rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar)
  have hStablePre :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        (transformerPre I SetLanguage.empty) :=
    stable_transformerPre_empty_readCommitted hStableI
  have hLeft :
      PaperInfer
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId I SetLanguage.empty
        (.insert (logRecordExpr (.int i))) inserted := by
    refine PaperInfer.viaLocalValid ?_
    refine Logic.localValid_insert
      (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
      txnId
      (transformerPre I SetLanguage.empty)
      (transformerPost SetLanguage.empty inserted)
      (logRecordExpr (.int i))
      hStablePre
      ?_
    intro localDb visibleDb record hPre hEval _hFresh
    rcases (transformerPre_empty_iff I localDb visibleDb).mp hPre with ⟨hLocal, _hInv⟩
    subst hLocal
    intro row
    simp [transformerPost, SetLanguage.denote_union, SetLanguage.empty, inserted]
    exact denote_insertedRowSet txnId emptySymEnv (logRecordExpr (.int i))
      visibleDb row record (by rfl) (by simpa [emptySymEnv] using hEval)
  have hStableMid :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        (transformerPost SetLanguage.empty inserted) :=
    stable_transformerPost_empty_insertedRowSet txnId (logRecordExpr (.int i))
  have hStableRightPre :
      Logic.stableBiAssertion
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        (transformerPre I (.union SetLanguage.empty inserted)) :=
    stable_transformerPre_empty_union_insertedRowSet_readCommitted
      hStableI txnId (logRecordExpr (.int i))
  have hRight :
      PaperInfer
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId I (.union SetLanguage.empty inserted)
        (.update rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar))
        updated :=
    PaperInfer.update
      (env := []) (source := rowVar) (updateExpr := insertCounterUpdateExpr i)
      (predicate := isCounterExpr rowVar) hStableRightPre
  have hSeq :
      PaperInfer
        (Logic.relyMod R (IsolationSpec.readCommitted Database).exec)
        txnId I SetLanguage.empty
        (.seq (.insert (logRecordExpr (.int i)))
          (.update rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar)))
        (.union inserted updated) :=
    PaperInfer.seq hLeft hStableMid hRight
  simpa [insertLogBody, insertLogEffect, insertCounterUpdateExpr, inserted, updated]
    using hSeq

/-! ## Final remaining obligations -/

/-- `paperInfer_insertLogBody_indexed_final` built **without** `viaLocalValid`,
using only `PaperInfer.insert` / `PaperInfer.update` / `PaperInfer.seq` constructors.

The static freshness witness required by `PaperInfer.insert` is discharged from
the `logSystemInvAtNext i` invariant: under that invariant, the log key
`(logTable, i)` is fresh in the visible database (no live log row at index `i`
since the live range is `[cut, i)`). This is `logSystemInvAtNext_no_log_at_next`. -/
theorem paperInfer_insertLogBody_indexed_final (i : Nat) :
    PaperInfer
      (Logic.relyMod R_insert (IsolationSpec.readCommitted Database).exec)
      (insertTxnId i) (logSystemInvAtNext i) SetLanguage.empty (insertLogBody i)
      (insertLogEffect (insertTxnId i) i) := by
  let R := Logic.relyMod R_insert (IsolationSpec.readCommitted Database).exec
  let I := logSystemInvAtNext i
  let txnId := insertTxnId i
  let inserted := insertedRowSet txnId emptySymEnv (logRecordExpr (.int i))
  let updated := updateSetExpr txnId [] rowVar
    (insertCounterUpdateExpr i) (isCounterExpr rowVar)
  have hStableI : Logic.stableAssertion R_insert I := logSystemInvAtNext_stable_R_insert i
  have hStablePre : Logic.stableBiAssertion R (transformerPre I SetLanguage.empty) :=
    stable_transformerPre_empty_readCommitted hStableI
  -- LEFT: PaperInfer.insert with static freshness from logSystemInvAtNext i.
  have hLeft :
      PaperInfer R txnId I SetLanguage.empty
        (.insert (logRecordExpr (.int i))) inserted := by
    refine PaperInfer.insert (env := emptySymEnv) (expr := logRecordExpr (.int i))
      hStablePre ?_ ?_
    · intro visibleDb row
      rfl
    · intro localDb visibleDb record hPre hEval
      rcases (transformerPre_empty_iff I localDb visibleDb).mp hPre with ⟨hLocal, hInv⟩
      subst hLocal
      have hRecordKey : record.key? = some (logTable, (i : Int)) := by
        have hEvalNorm : Expr.eval (logRecordExpr (.int i)) = some (.record record) := by
          simpa [instantiateSymExpr, emptySymEnv] using hEval
        unfold logRecordExpr at hEvalNorm
        simp [Expr.eval, Literal.toValue] at hEvalNorm
        -- After simp, the equality `record = {explicit fields}` is destructured
        -- via Option.some.injEq and Value.record.injEq, substituting record.
        rcases hEvalNorm with ⟨⟩
        rfl
      unfold Semantics.insertFresh
      rw [hRecordKey]
      simp only []
      have hNoKeyVis : ¬ Database.hasKey visibleDb (logTable, (i : Int)) :=
        logSystemInvAtNext_no_log_at_next hInv
      intro hConcat
      apply hNoKeyVis
      simpa using hConcat
  have hStableMid : Logic.stableBiAssertion R (transformerPost SetLanguage.empty inserted) :=
    stable_transformerPost_empty_insertedRowSet txnId (logRecordExpr (.int i))
  have hStableRightPre :
      Logic.stableBiAssertion R (transformerPre I (.union SetLanguage.empty inserted)) :=
    stable_transformerPre_empty_union_insertedRowSet_readCommitted hStableI txnId
      (logRecordExpr (.int i))
  have hRight :
      PaperInfer R txnId I (.union SetLanguage.empty inserted)
        (.update rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar)) updated :=
    PaperInfer.update (env := []) (source := rowVar)
      (updateExpr := insertCounterUpdateExpr i) (predicate := isCounterExpr rowVar)
      hStableRightPre
  have hSeq :
      PaperInfer R txnId I SetLanguage.empty
        (.seq (.insert (logRecordExpr (.int i)))
          (.update rowVar (insertCounterUpdateExpr i) (isCounterExpr rowVar)))
        (.union inserted updated) :=
    PaperInfer.seq hLeft hStableMid hRight
  simpa [insertLogBody, insertLogEffect, insertCounterUpdateExpr, inserted, updated]
    using hSeq

/-- Helper: `stableBiAssertion` for the archive's invariant under SI's silent
rely. The underlying rely doesn't change `visibleDb`, so any vd-only assertion
is trivially stable. -/
private theorem archiveIndexedInv_stableBi
    {R : Rely} (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.snapshot (σ := Database)).exec)
      (fun (_ : Database) vd => logSystemInv vd ∧ archiveKeysFreshFrom i vd) := by
  intro localDb v v' hI hStep
  have hEq := relyMod_snapshot_exec_silent localDb v v' hStep
  rw [hEq]
  exact hI

/-- `selectedStorageEntriesSet` doesn't reference `localDb`, so its application
form `(ld, vd, entry)` is equivalent to `entry ∈ vd ∧ satisfiesPredicate
isStorageEntry entry.visible = some true` regardless of `ld`. -/
private theorem selectedStorageEntriesSet_apply_iff
    (ld vd : Database) (entry : Row) :
    selectedStorageEntriesSet ld vd entry ↔
      entry ∈ vd ∧
        Semantics.satisfiesPredicate rowVar (isStorageEntryExpr rowVar) entry.visible = some true := by
  unfold selectedStorageEntriesSet globalSelectionSet SetLanguage.SetExpr.bind
    SetLanguage.SetExpr.globalDb
  constructor
  · rintro ⟨mid, hMidMem, hBody⟩
    by_cases hCond :
        evalSymExprAtRow emptySymEnv rowVar mid (isStorageEntryExpr rowVar) =
          some (Value.scalar (ScalarLit.bool true))
    · simp [hCond, SetLanguage.singleton, SetLanguage.empty] at hBody
      subst hBody
      refine ⟨hMidMem, ?_⟩
      unfold Semantics.satisfiesPredicate
      unfold evalSymExprAtRow at hCond
      simp only [emptySymEnv, instantiateSymExpr_noScalars] at hCond
      rw [hCond]
      rfl
    · simp [hCond, SetLanguage.singleton, SetLanguage.empty] at hBody
  · rintro ⟨hMem, hSat⟩
    refine ⟨entry, hMem, ?_⟩
    have hCond :
        evalSymExprAtRow emptySymEnv rowVar entry (isStorageEntryExpr rowVar) =
          some (Value.scalar (ScalarLit.bool true)) := by
      unfold evalSymExprAtRow
      simp only [emptySymEnv, instantiateSymExpr_noScalars]
      unfold Semantics.satisfiesPredicate at hSat
      cases hE : Expr.eval (Semantics.instantiateRecord rowVar entry.visible (isStorageEntryExpr rowVar)) with
      | none => rw [hE] at hSat; cases hSat
      | some v =>
          cases v with
          | scalar lit =>
              cases lit with
              | bool b =>
                  rw [hE] at hSat
                  simp at hSat
                  subst hSat
                  rfl
              | _ => rw [hE] at hSat; cases hSat
          | _ => rw [hE] at hSat; cases hSat
    simp [hCond, SetLanguage.singleton]

/-- Pointwise denote-equivalence between `LazyF_select` (existential over
`selected` storage entries) and `selectAllLogEffect`, at a vd satisfying
`logSystemInv`. Mirrors `lazyF_iff_archiveLogEffect_at_invariant`. -/
private theorem lazyF_select_iff_selectAllLogEffect_at_invariant
    {q : Nat} {ld vd : Database} (hInv : logSystemInv vd) (row : Row) :
    (∃ selected,
        Semantics.collectSelected vd rowVar
            (instantiateSymExpr emptySymEnv [rowVar] (isStorageEntryExpr rowVar)) = some selected ∧
        selectAllLogEffect_with_selected (selectTxnId q) q selected ld vd row) ↔
      selectAllLogEffect (selectTxnId q) q ld vd row := by
  have hInstNop :
      instantiateSymExpr emptySymEnv [rowVar] (isStorageEntryExpr rowVar) =
        isStorageEntryExpr rowVar := by
    simp [instantiateSymExpr, emptySymEnv]
  rw [hInstNop]
  have hWF : wellFormedTableFields vd := by
    rcases hInv with ⟨_, _, _, _, hWF⟩; exact hWF
  unfold selectAllLogEffect SetLanguage.SetExpr.bind
  unfold selectAllLogEffect_with_selected
  constructor
  · rintro ⟨sel, hSelect, entry, hEntry, srcRow, hSrcMem, hVis, hEffect⟩
    refine ⟨srcRow, ?_, hEffect⟩
    rw [selectedStorageEntriesSet_apply_iff]
    refine ⟨hSrcMem, ?_⟩
    -- Need: satisfiesPredicate isStorageEntry srcRow.visible = some true.
    rcases (mem_selected_iff_storage_entry hSelect hWF entry).mp hEntry with
      ⟨srcRow', _hSrcMem', hKeyOr, hVis'⟩
    have hVisEq : srcRow.visible = srcRow'.visible := hVis.trans hVis'.symm
    -- satisfiesPredicate depends only on the record (.visible), not the row's other fields.
    refine (satisfiesPredicate_isStorageEntryExpr_iff srcRow).mpr ?_
    have hKeyEq : Row.key? srcRow = Row.key? srcRow' := by
      unfold Row.key?; rw [hVisEq]
    rcases hKeyOr with ⟨n, hLog⟩ | ⟨n, hArch⟩
    · exact Or.inl (rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem (hKeyEq ▸ hLog))
    · exact Or.inr (rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem (hKeyEq ▸ hArch))
  · rintro ⟨entryRow, hStorage, hEffect⟩
    rw [selectedStorageEntriesSet_apply_iff] at hStorage
    rcases hStorage with ⟨hEntryRowMem, hSat⟩
    rcases collectSelected_storageEntries_succeeds_of_wellFormed hWF with ⟨sel, hSelect⟩
    refine ⟨sel, hSelect, entryRow.visible, ?_, entryRow, hEntryRowMem, rfl, hEffect⟩
    refine (mem_selected_iff_storage_entry hSelect hWF entryRow.visible).mpr
      ⟨entryRow, hEntryRowMem, ?_, rfl⟩
    have hTabOr : rowFieldInt? entryRow tableField = some logTable ∨
        rowFieldInt? entryRow tableField = some archiveTable :=
      (satisfiesPredicate_isStorageEntryExpr_iff entryRow).mp hSat
    rcases hWF entryRow hEntryRowMem with ⟨t, n, hKey, hTab⟩
    rcases hTabOr with hLog | hArch
    · rw [hTab] at hLog
      have hTEq : t = logTable := Option.some.inj hLog
      subst hTEq
      exact Or.inl ⟨n, hKey⟩
    · rw [hTab] at hArch
      have hTEq : t = archiveTable := Option.some.inj hArch
      subst hTEq
      exact Or.inr ⟨n, hKey⟩

/-- Pointwise denote-equivalence between `LazyF` (existential over `selected`)
and `archiveLogEffect`, at a vd satisfying `logSystemInv`. Used as the bridge
hypothesis for `PaperInfer.conseqF_withInv` in `paperInfer_archiveLogBody_indexed_final`. -/
private theorem lazyF_iff_archiveLogEffect_at_invariant
    {i : Nat} {ld vd : Database} (hInv : logSystemInv vd) (row : Row) :
    (∃ selected,
        Semantics.collectSelected vd rowVar
            (instantiateSymExpr emptySymEnv [rowVar] (isLogExpr rowVar)) = some selected ∧
        archiveLogEffect_with_selected (archiveTxnId i) i selected ld vd row) ↔
      archiveLogEffect (archiveTxnId i) i ld vd row := by
  -- instantiateSymExpr emptySymEnv [rowVar] (isLogExpr rowVar) = isLogExpr rowVar (emptySymEnv has no scalars).
  have hInstNop :
      instantiateSymExpr emptySymEnv [rowVar] (isLogExpr rowVar) = isLogExpr rowVar := by
    simp [instantiateSymExpr, emptySymEnv]
  rw [hInstNop]
  have hWF : wellFormedTableFields vd := by
    rcases hInv with ⟨_, _, _, _, hWF⟩
    exact hWF
  constructor
  · -- LazyF → archiveLogEffect: use selectedLitMin/Max ↔ selectedLogMin/Max bridges.
    rintro ⟨selected, hSelect, hEff⟩
    unfold archiveLogEffect_with_selected at hEff
    unfold archiveLogEffect
    simp only [SetLanguage.SetExpr.union] at hEff ⊢
    rcases hEff with hIns | hDel
    · -- Insert effect: ∃ lo hi0, selectedLitMin = some lo ∧ selectedLitMax = some hi0 ∧ row = archiveRow ...
      left
      unfold archiveLogInsertEffect_with_selected at hIns
      unfold archiveLogInsertEffect
      rcases hIns with ⟨lo, hi0, hLitMin, hLitMax, hRow⟩
      refine ⟨lo, hi0, ?_, ?_, hRow⟩
      · exact (selectedLitMin_iff_selectedLogMin hSelect hWF).mp hLitMin
      · exact (selectedLitMax_iff_selectedLogMax hSelect hWF).mp hLitMax
    · -- Delete effect: ∃ src n lo hi0, selectedLitMin/Max + log row in vd + range + markDeleted
      right
      unfold archiveLogDeleteEffect_with_selected at hDel
      unfold archiveLogDeleteEffect
      rcases hDel with ⟨src, n, lo, hi0, hLitMin, hLitMax, hSrcMem, hSrcKey, hLo, hHi, hOut⟩
      refine ⟨src, n, lo, hi0, ?_, ?_, ⟨hSrcMem, hSrcKey⟩, hLo, hHi, hOut⟩
      · exact (selectedLitMin_iff_selectedLogMin hSelect hWF).mp hLitMin
      · exact (selectedLitMax_iff_selectedLogMax hSelect hWF).mp hLitMax
  · -- archiveLogEffect → LazyF: get selected via collectSelected_logs_succeeds.
    intro hEff
    rcases collectSelected_logs_succeeds_of_wellFormed hWF with ⟨selected, hSelect⟩
    refine ⟨selected, hSelect, ?_⟩
    unfold archiveLogEffect at hEff
    unfold archiveLogEffect_with_selected
    simp only [SetLanguage.SetExpr.union] at hEff
    simp only [SetLanguage.SetExpr.union]
    rcases hEff with hIns | hDel
    · left
      unfold archiveLogInsertEffect at hIns
      unfold archiveLogInsertEffect_with_selected
      rcases hIns with ⟨lo, hi0, hLogMin, hLogMax, hRow⟩
      refine ⟨lo, hi0, ?_, ?_, hRow⟩
      · exact (selectedLitMin_iff_selectedLogMin hSelect hWF).mpr hLogMin
      · exact (selectedLitMax_iff_selectedLogMax hSelect hWF).mpr hLogMax
    · right
      unfold archiveLogDeleteEffect at hDel
      unfold archiveLogDeleteEffect_with_selected
      rcases hDel with ⟨src, n, lo, hi0, hLogMin, hLogMax, ⟨hSrcMem, hSrcKey⟩, hLo, hHi, hOut⟩
      refine ⟨src, n, lo, hi0, ?_, ?_, hSrcMem, hSrcKey, hLo, hHi, hOut⟩
      · exact (selectedLitMin_iff_selectedLogMin hSelect hWF).mpr hLogMin
      · exact (selectedLitMax_iff_selectedLogMax hSelect hWF).mpr hLogMax

/-- Lazy variant: PaperInfer for `archiveLogBody` with the lazy F
(produced by `PaperInfer.selectLazy`). The body's `Fbody selected` is
parameterised over `selected`, so the universal LocalValid quantification
over inner `(ld', vd')` no longer mismatches — body's writes and Fbody's
denotation are both pinned via `selected`, with vd' only contributing
the log-row source for delete markers in both. -/
theorem paperInfer_archiveLogBody_indexed_via_lazy (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty (archiveLogBody i)
      (fun localDb globalDb out =>
        ∃ selected,
          Semantics.collectSelected globalDb rowVar
              (instantiateSymExpr emptySymEnv [rowVar] (isLogExpr rowVar)) = some selected ∧
          archiveLogEffect_with_selected (archiveTxnId i) i selected localDb globalDb out) := by
  unfold archiveLogBody
  refine PaperInfer.selectLazy
    (env := emptySymEnv)
    (Fbody := archiveLogEffect_with_selected (archiveTxnId i) i)
    ?_ ?_ ?_
  · -- stability of transformerPre under SI's local rely (silent → trivial)
    exact transformerPre_stable_relyMod_snapshot _ _
  · -- hCollectStable: under SI silent rely, R doesn't change vd, so
    -- collectSelected is trivially preserved.
    intro localDb visibleDb visibleDb' hR
    have := relyMod_snapshot_exec_silent localDb visibleDb visibleDb' hR
    rw [this]
  · -- per-`selected` body PaperInfer
    -- Fbody is parameterised by selected; archiveCompactBody[logsVar→selected]
    -- has its writes pinned to `selected` (lo/hi from selectedLitMin/Max),
    -- so universal LocalValid over (ld', vd') matches Fbody(selected) on both sides.
    intro selected
    refine PaperInfer.viaLocalValid ?_
    refine Logic.localValid_of_stutterRely ?_ relyMod_snapshot_exec_silent
    -- Now goal: LocalValid (False rely) txnId
    --   (transformerPre Iinfer empty) (subst body) (transformerPost empty (Fbody selected))
    -- Decompose via localValid_ite_false, branching on setNonempty.
    refine Logic.localValid_ite_false (archiveTxnId i) _ _ _ _ _ ?_ ?_
    · -- True branch: nonempty selected → archiveCompactBody runs.
      -- archiveCompactBody[logsVar→selected] decomposes to:
      --   letE loVar (setMinField selected idField)
      --     (letE hi0Var (setMaxField selected idField)
      --       (seq (insert archiveRow ...) (delete log markers in [lo, hi])))
      intro _hEvalTrue
      simp only [Command.subst, Expr.subst, archiveCompactBody, archiveDeletePredicate,
        archiveRecordExpr, isLogExpr, isTableExpr, eqExpr, fieldExpr, andExpr,
        leExpr, addExpr, if_true, if_false]
      -- Case on whether setMinField evaluates. If none, body stuck (vacuous).
      cases hMinEval :
          Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) with
      | none =>
          exact localValid_letE_none_false (archiveTxnId i) _ _ loVar _ _ hMinEval
      | some loVal =>
          -- loVal = .scalar (.int lo). Apply localValid_let_false then recurse to hi0Var.
          refine Logic.localValid_let_false (archiveTxnId i) _ _ loVar _ _ loVal hMinEval ?_
          -- Now goal has Command.subst loVar loVal.toExpr (inner letE).
          cases hMaxEval :
              Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) with
          | none =>
              -- Substituted body is `.letE hi0Var (.setMaxField ...) ...`. Eval is hMaxEval.
              -- But wait — Command.subst loVar loVal.toExpr replaces loVar in the body, not the
              -- expr of inner letE which references hi0Var. So the inner letE's expr is unchanged
              -- (setMaxField doesn't reference loVar).
              exact localValid_letE_none_false (archiveTxnId i) _ _ hi0Var _ _ hMaxEval
          | some hi0Val =>
              refine Logic.localValid_let_false (archiveTxnId i) _ _ hi0Var _ _ hi0Val hMaxEval ?_
              -- Simplify the substituted body: var-name decidable equalities propagate.
              simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
                Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr,
                logsVar, loVar, hi0Var, rowVar, idField, tableField, loField, hiField,
                show ("logs" : VarName) ≠ "lo" from by decide,
                show ("logs" : VarName) ≠ "hi0" from by decide,
                show ("logs" : VarName) ≠ "row" from by decide,
                show ("lo" : VarName) ≠ "hi0" from by decide,
                show ("lo" : VarName) ≠ "row" from by decide,
                show ("hi0" : VarName) ≠ "row" from by decide,
                if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
                Expr.int]
              -- Extract integer values from loVal/hi0Val. setMinField/setMaxField
              -- always return `.scalar (.int _)` when they succeed.
              obtain ⟨lo, hLoVal⟩ := setMinField_lit_eval_int hMinEval
              obtain ⟨hi0, hHi0Val⟩ := setMaxField_lit_eval_int hMaxEval
              subst hLoVal
              subst hHi0Val
              -- Pin the selectedLitMin/Max characterizations from hMinEval/hMaxEval.
              have hSelMin : selectedLitMin selected = some lo := by
                simp [selectedLitMin, hMinEval]
              have hSelMax : selectedLitMax selected = some hi0 := by
                simp [selectedLitMax, hMaxEval]
              -- Decompose seq into insert step + delete step.
              -- Intermediate post: insert produces archiveRow only AND vd still
              -- satisfies the invariant (which gives wellFormedTableFields for
              -- the delete-step predicate-evaluation reasoning).
              refine Logic.localValid_seq_false (archiveTxnId i)
                (transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) SetLanguage.empty)
                (fun ld vd =>
                  transformerPost SetLanguage.empty
                      (archiveLogInsertEffect_with_selected (archiveTxnId i) i selected) ld vd ∧
                    logSystemInv vd ∧ archiveKeysFreshFrom i vd)
                (transformerPost SetLanguage.empty
                  (archiveLogEffect_with_selected (archiveTxnId i) i selected))
                _ _ ?_ ?_
              · -- Insert step
                refine Logic.localValid_insert_false (archiveTxnId i) _ _ _ ?_
                intro ld vd record hPre hEval _hFresh
                rcases hPre with ⟨hLocal, hInv⟩
                refine ⟨?_, hInv⟩
                -- ld = [] from transformerPre on empty
                have hLdEmpty : ld = [] := by
                  cases ld with
                  | nil => rfl
                  | cons row rest =>
                      have := (hLocal row).mpr List.mem_cons_self
                      simp [SetLanguage.denote, SetLanguage.empty] at this
                subst hLdEmpty
                -- record value is archiveRecord i lo (hi0+1)
                simp only [Expr.eval, Value.toExpr, Literal.toValue,
                  Expr.evalFieldValues, Bind.bind, Option.bind, Option.some_bind,
                  Pure.pure] at hEval
                injection hEval with hEval
                injection hEval with hEval
                have hRecord : record = archiveRecord i lo (hi0 + 1) := by
                  rw [← hEval]
                  simp [archiveRecord, tableField, idField, loField, hiField]
                subst hRecord
                -- Goal: union empty insertEffect at vd ↔ row = archiveRow ... lo (hi0+1)
                intro row
                simp only [transformerPost, List.nil_append, List.mem_singleton,
                  SetLanguage.denote, SetLanguage.SetExpr.union, SetLanguage.empty,
                  archiveLogInsertEffect_with_selected, false_or]
                constructor
                · rintro ⟨lo', hi0', hMin', hMax', hOut⟩
                  rw [hSelMin] at hMin'
                  rw [hSelMax] at hMax'
                  cases hMin'; cases hMax'
                  exact hOut
                · intro hRow
                  exact ⟨lo, hi0, hSelMin, hSelMax, hRow⟩
              · -- Delete step
                refine Logic.localValid_delete_false (archiveTxnId i) _ _ _ _ ?_
                intro ld vd removed hPre' hCollect _hDisjoint
                rcases hPre' with ⟨hPre, hInv, _hKeysFresh⟩
                have hWF : wellFormedTableFields vd := by
                  rcases hInv with ⟨_, _, _, _, hWF⟩
                  exact hWF
                -- hPre says ld denotes insertEffect at vd (membership). Combine with
                -- mem_collectDeleted_iff for `removed`, then show union iff for the post.
                simp only [transformerPost, SetLanguage.denote,
                  SetLanguage.SetExpr.union, SetLanguage.empty,
                  archiveLogInsertEffect_with_selected, archiveLogDeleteEffect_with_selected,
                  archiveLogEffect_with_selected, false_or] at hPre ⊢
                intro row
                -- Goal: row matches insertEffect ∨ deleteEffect at vd ↔ row ∈ ld ++ removed
                rw [List.mem_append]
                constructor
                · rintro (hIns | hDel)
                  · -- row matches insert: row = archiveRow lo (hi0+1)
                    rcases hIns with ⟨lo', hi0', hMin', hMax', hOut⟩
                    rw [hSelMin] at hMin'; rw [hSelMax] at hMax'
                    cases hMin'; cases hMax'
                    -- archiveRow ∈ ld via hPre
                    left
                    exact (hPre row).mp ⟨lo, hi0, hSelMin, hSelMax, hOut⟩
                  · -- row matches delete: row = src.markDeleted with src ∈ vd, etc.
                    rcases hDel with ⟨src, n, lo', hi0', hMin', hMax', hSrc, hKey, hLo, hHi, hOut⟩
                    rw [hSelMin] at hMin'; rw [hSelMax] at hMax'
                    cases hMin'; cases hMax'
                    right
                    rw [Semantics.mem_collectDeleted_iff hCollect]
                    refine ⟨src, hSrc, ?_, hOut⟩
                    have hTab : rowFieldInt? src tableField = some logTable :=
                      rowFieldInt?_tableField_of_key_wellFormed hWF hSrc hKey
                    have hSat :=
                      (satisfiesPredicate_archiveDelete_iff src lo hi0).mpr
                        ⟨hTab, n, rowFieldInt?_idField_of_key hKey, hLo, hHi⟩
                    exact hSat
                · rintro (hLd | hRem)
                  · -- row ∈ ld → matches insertEffect at vd
                    left
                    have := (hPre row).mpr hLd
                    exact this
                  · -- row ∈ removed → matches deleteEffect
                    right
                    rw [Semantics.mem_collectDeleted_iff hCollect] at hRem
                    rcases hRem with ⟨src, hSrc, hSat, hOut⟩
                    have hSat' := (satisfiesPredicate_archiveDelete_iff src lo hi0).mp hSat
                    rcases hSat' with ⟨hTab, n, hId, hLo, hHi⟩
                    have hKey : src.key? = some (logTable, n) :=
                      rowKey?_of_table_id_fields hTab hId
                    exact ⟨src, n, lo, hi0, hSelMin, hSelMax, hSrc, hKey, hLo, hHi, hOut⟩
    · -- False branch: empty selected → .skip. Now Fbody(selected=[]) denotes nothing.
      intro hEvalFalse
      have hSelectedEmpty : selected = [] := by
        cases hSel : selected with
        | nil => rfl
        | cons head tail =>
            exfalso
            simp [Expr.subst, Expr.eval, Literal.toValue, hSel] at hEvalFalse
      subst hSelectedEmpty
      -- Now Fbody [] denotes nothing (selectedLitMin/Max return none for empty).
      refine Logic.localValid_conseq
        (P := transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) SetLanguage.empty)
        (P' := transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) SetLanguage.empty)
        (Q' := transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) SetLanguage.empty)
        (fun _ _ h => h)
        (Logic.localValid_skip_false (archiveTxnId i) _) ?_
      intro localDb' visibleDb' hPre'
      -- This is the universal P → Q step. Now Q = transformerPost empty (Fbody []).
      -- Fbody [] = archiveLogEffect_with_selected _ _ [] denotes nothing because
      -- selectedLitMin [] / selectedLitMax [] are `none`.
      rcases hPre' with ⟨hDenote, _hInv⟩
      have hLocalEmpty : localDb' = [] := by
        cases localDb' with
        | nil => rfl
        | cons row rest =>
            have := (hDenote row).mpr List.mem_cons_self
            simp [SetLanguage.denote, SetLanguage.empty] at this
      subst hLocalEmpty
      unfold transformerPost
      intro row
      have hMinNone : selectedLitMin [] = none := by native_decide
      simp only [SetLanguage.denote_union, SetLanguage.denote_empty, false_or,
        List.not_mem_nil, iff_false]
      simp only [SetLanguage.denote, archiveLogEffect_with_selected,
        SetLanguage.SetExpr.union, archiveLogInsertEffect_with_selected,
        archiveLogDeleteEffect_with_selected]
      rintro (⟨_, _, hMin, _, _⟩ | ⟨_, _, _, _, hMin, _, _, _, _, _, _⟩) <;>
        rw [hMinNone] at hMin <;> cases hMin

/-- Helper: stability of `transformerPre I empty` under SI silent rely
(specialized for archive's invariant). -/
private theorem archive_transformerPre_stable (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        SetLanguage.empty) :=
  transformerPre_stable_relyMod_snapshot _ _

/-- Helper: stability of `transformerPost empty F` under SI silent rely. -/
private theorem archive_transformerPost_stable (F : SetLanguage.SetExpr) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (transformerPost SetLanguage.empty F) :=
  transformerPost_stable_relyMod_snapshot _ _

/-- Helper: stability of `transformerPre I (empty ∪ F)` under SI silent rely
(specialized for archive's invariant). -/
private theorem archive_transformerPre_union_stable
    (i : Nat) (F : SetLanguage.SetExpr) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        (.union SetLanguage.empty F)) :=
  transformerPre_stable_relyMod_snapshot _ _

/-- Constructor-only `PaperInfer` for the archive-row INSERT step (given
specific `lo, hi0` extracted from `setMinField` / `setMaxField` evaluation
on a non-empty `selected`). Discharges `hFresh` from `archiveKeysFreshFrom i`. -/
private theorem paperInfer_archiveInsert (i : Nat) (lo hi0 : Int) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.insert (archiveRecordExpr i (Expr.int lo) (Expr.int (hi0 + 1))))
      (insertedRowSet (archiveTxnId i) emptySymEnv
        (archiveRecordExpr i (Expr.int lo) (Expr.int (hi0 + 1)))) := by
  refine PaperInfer.insert (env := emptySymEnv)
    (expr := archiveRecordExpr i (Expr.int lo) (Expr.int (hi0 + 1)))
    (archive_transformerPre_stable i) ?closed ?fresh
  · intro vd row; rfl
  · intro ld vd record hPre hEval
    rcases (transformerPre_empty_iff _ ld vd).mp hPre with ⟨hLocal, hInv⟩
    subst hLocal
    have hRecordKey : record.key? = some (archiveTable, (i : Int)) := by
      simp [instantiateSymExpr, emptySymEnv] at hEval
      unfold archiveRecordExpr at hEval
      simp [Expr.eval, Literal.toValue] at hEval
      rcases hEval with ⟨⟩
      rfl
    unfold Semantics.insertFresh
    rw [hRecordKey]
    simp only []
    have hNoKey : ¬ Database.hasKey vd (archiveTable, (i : Int)) :=
      archiveKeysFreshFrom_no_archive_at hInv.2
    intro hConcat
    apply hNoKey
    simpa using hConcat

/-- Variant of `paperInfer_archiveInsert` for the cascade-form expression
`archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))`,
which is what arises after `Command.subst hi0Var (Value.toExpr (.scalar (.int hi0)))`
applies to `archiveRecordExpr i (Expr.int lo) (addExpr (.var hi0Var) (Expr.int 1))`. -/
private theorem paperInfer_archiveInsert_addExpr (i : Nat) (lo hi0 : Int) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
      (insertedRowSet (archiveTxnId i) emptySymEnv
        (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1)))) := by
  refine PaperInfer.insert (env := emptySymEnv)
    (expr := archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1)))
    (archive_transformerPre_stable i) ?closed ?fresh
  · intro vd row; rfl
  · intro ld vd record hPre hEval
    rcases (transformerPre_empty_iff _ ld vd).mp hPre with ⟨hLocal, hInv⟩
    subst hLocal
    have hRecordKey : record.key? = some (archiveTable, (i : Int)) := by
      simp [instantiateSymExpr, emptySymEnv] at hEval
      unfold archiveRecordExpr addExpr at hEval
      simp [Expr.eval, Literal.toValue] at hEval
      rcases hEval with ⟨⟩
      rfl
    unfold Semantics.insertFresh
    rw [hRecordKey]
    simp only []
    have hNoKey : ¬ Database.hasKey vd (archiveTable, (i : Int)) :=
      archiveKeysFreshFrom_no_archive_at hInv.2
    intro hConcat
    apply hNoKey
    simpa using hConcat

/-- Constructor-only `PaperInfer` for the archive log DELETE step (under the
seq's post-insert context with `Fctxt = .union empty insertedRowSet`). The
predicate has been pre-substituted with concrete `lo, hi0` literals. -/
private theorem paperInfer_archiveDelete
    (i : Nat) (predicate : Expr) (insertF : SetLanguage.SetExpr) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      (.union SetLanguage.empty insertF)
      (.delete rowVar predicate)
      (deleteSetExpr (archiveTxnId i) [] rowVar predicate) :=
  PaperInfer.delete (env := []) (source := rowVar) (predicate := predicate)
    (archive_transformerPre_union_stable i _)

/-- Cascade-form variant of `paperInfer_archiveSeqInsertDelete` using
`paperInfer_archiveInsert_addExpr` (with `addExpr (Expr.int hi0) (Expr.int 1)`
instead of `Expr.int (hi0 + 1)`). -/
private theorem paperInfer_archiveSeqInsertDelete_addExpr
    (i : Nat) (lo hi0 : Int) (predicate : Expr) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.seq
        (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
        (.delete rowVar predicate))
      (.union
        (insertedRowSet (archiveTxnId i) emptySymEnv
          (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
        (deleteSetExpr (archiveTxnId i) [] rowVar predicate)) := by
  refine PaperInfer.seq
    (paperInfer_archiveInsert_addExpr i lo hi0)
    (archive_transformerPost_stable _)
    (paperInfer_archiveDelete i predicate _)

/-- Constructor-only `PaperInfer` for the archive's `.seq (insert) (delete)` step.
The output F is `.union insertedRowSet deleteSetExpr` (the constructor-natural
shape from `PaperInfer.seq + PaperInfer.insert + PaperInfer.delete`). -/
private theorem paperInfer_archiveSeqInsertDelete
    (i : Nat) (lo hi0 : Int) (predicate : Expr) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.seq
        (.insert (archiveRecordExpr i (Expr.int lo) (Expr.int (hi0 + 1))))
        (.delete rowVar predicate))
      (.union
        (insertedRowSet (archiveTxnId i) emptySymEnv
          (archiveRecordExpr i (Expr.int lo) (Expr.int (hi0 + 1))))
        (deleteSetExpr (archiveTxnId i) [] rowVar predicate)) := by
  refine PaperInfer.seq
    (paperInfer_archiveInsert i lo hi0)
    (archive_transformerPost_stable _)
    (paperInfer_archiveDelete i predicate _)

/-- PaperInfer for the inner `.letE hi0Var ... (.seq insert delete)` of compactBody
(after `loVar` substitution by the outer letE). The `predicate_outer` is the
archiveDeletePredicate with `loVar` already substituted but `hi0Var` still as
a variable. -/
private theorem paperInfer_archiveLetEHi0Var
    (i : Nat) (lo hi0 : Int) (selected : SetLit)
    (hMaxEval :
      Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int hi0)))
    (predicate_outer : Expr) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
        (.seq
          (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (.var hi0Var) (Expr.int 1))))
          (.delete rowVar predicate_outer)))
      (.union
        (insertedRowSet (archiveTxnId i) emptySymEnv
          (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
        (deleteSetExpr (archiveTxnId i) [] rowVar
          (Expr.subst hi0Var (Expr.int hi0) predicate_outer))) := by
  refine PaperInfer.letE (env := emptySymEnv) (x := hi0Var)
    (expr := .setMaxField (Expr.lit (Literal.set selected)) idField)
    (value := Value.scalar (ScalarLit.int hi0))
    (archive_transformerPre_stable i) ?hEval ?hBody
  · simp [instantiateSymExpr, emptySymEnv]
    exact hMaxEval
  · -- hBody : LocalValid for substituted body.
    have hSeqPi := paperInfer_archiveSeqInsertDelete_addExpr i lo hi0
      (Expr.subst hi0Var (Expr.int hi0) predicate_outer)
    have hSubst :
        (Command.subst hi0Var (Value.toExpr (Value.scalar (ScalarLit.int hi0)))
          (.seq
            (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (.var hi0Var) (Expr.int 1))))
            (.delete rowVar predicate_outer))
            : Semantics.Program) =
          ((.seq
            (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
            (.delete rowVar (Expr.subst hi0Var (Expr.int hi0) predicate_outer)))
            : Semantics.Program) := by
      simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
        Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr, Value.toExpr,
        archiveRecordExpr, addExpr, Expr.int, hi0Var, rowVar, idField, tableField, loField, hiField,
        show ("hi0" : VarName) ≠ "row" from by decide,
        show ("hi0" : VarName) = "hi0" from rfl,
        if_true, if_false, ite_eq_left_iff, ite_eq_right_iff]
    rw [hSubst]
    exact PaperInfer.sound (archiveIndexedInv_stableBi i) hSeqPi

/-- PaperInfer for the outer `.letE loVar (.setMinField ...) (inner letE for hi0Var)`,
composing `paperInfer_archiveLetEHi0Var` via `PaperInfer.letE + PaperInfer.sound`. -/
private theorem paperInfer_archiveLetELoVar
    (i : Nat) (lo hi0 : Int) (selected : SetLit)
    (hMinEval :
      Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int lo)))
    (hMaxEval :
      Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int hi0))) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.letE loVar (.setMinField (Expr.lit (Literal.set selected)) idField)
        (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
          (.seq
            (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
            (.delete rowVar archiveDeletePredicate))))
      (.union
        (insertedRowSet (archiveTxnId i) emptySymEnv
          (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
        (deleteSetExpr (archiveTxnId i) [] rowVar
          (Expr.subst hi0Var (Expr.int hi0)
            (Expr.subst loVar (Expr.int lo) archiveDeletePredicate)))) := by
  refine PaperInfer.letE (env := emptySymEnv) (x := loVar)
    (expr := .setMinField (Expr.lit (Literal.set selected)) idField)
    (value := Value.scalar (ScalarLit.int lo))
    (archive_transformerPre_stable i) ?hEval ?hBody
  · simp [instantiateSymExpr, emptySymEnv]
    exact hMinEval
  · have hInnerLetEPi := paperInfer_archiveLetEHi0Var i lo hi0 selected hMaxEval
      (Expr.subst loVar (Expr.int lo) archiveDeletePredicate)
    have hSubst :
        (Command.subst loVar (Value.toExpr (Value.scalar (ScalarLit.int lo)))
          (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar archiveDeletePredicate)))
            : Semantics.Program) =
          ((.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (Expr.int lo) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar (Expr.subst loVar (Expr.int lo) archiveDeletePredicate))))
            : Semantics.Program) := by
      simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
        Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr, Value.toExpr,
        archiveRecordExpr, addExpr, Expr.int, loVar, hi0Var, rowVar,
        idField, tableField, loField, hiField,
        show ("lo" : VarName) ≠ "hi0" from by decide,
        show ("lo" : VarName) ≠ "row" from by decide,
        show ("lo" : VarName) = "lo" from rfl,
        if_true, if_false, ite_eq_left_iff, ite_eq_right_iff]
    rw [hSubst]
    exact PaperInfer.sound (archiveIndexedInv_stableBi i) hInnerLetEPi

/-- The constructor-natural F produced by the cascade for non-empty selected
case (when both `setMinField` / `setMaxField` evaluate). -/
private def archiveCtorF_nonempty (i : Nat) (lo hi0 : Int) : SetLanguage.SetExpr :=
  .union
    (insertedRowSet (archiveTxnId i) emptySymEnv
      (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1))))
    (deleteSetExpr (archiveTxnId i) [] rowVar
      (Expr.subst hi0Var (Expr.int hi0)
        (Expr.subst loVar (Expr.int lo) archiveDeletePredicate)))

/-- Outer `.ite (.setNonempty (.lit (.set sel))) compactBody[sel] .skip` PaperInfer
for non-empty selected (with both `setMinField` and `setMaxField` evaluating).
The output F is `.ite (formulaOfExpr setNonempty) archiveCtorF_nonempty empty`
(PaperInfer.ite's constructor-natural shape). -/
private theorem paperInfer_archiveBodySubst_nonempty
    (i : Nat) (lo hi0 : Int) (selected : SetLit)
    (hMinEval :
      Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int lo)))
    (hMaxEval :
      Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int hi0))) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.ite (.setNonempty (Expr.lit (Literal.set selected)))
        (.letE loVar (.setMinField (Expr.lit (Literal.set selected)) idField)
          (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar archiveDeletePredicate))))
        .skip)
      (.ite
        (formulaOfExpr emptySymEnv (.setNonempty (Expr.lit (Literal.set selected))))
        (archiveCtorF_nonempty i lo hi0) SetLanguage.empty) :=
  PaperInfer.ite (env := emptySymEnv)
    (cond := .setNonempty (Expr.lit (Literal.set selected)))
    (archive_transformerPre_stable i)
    (paperInfer_archiveLetELoVar i lo hi0 selected hMinEval hMaxEval)
    (PaperInfer.skip (archive_transformerPost_stable _))

/-- Outer `.ite ... compactBody[sel] .skip` PaperInfer for empty selected
(where `setMinField` returns none, making compactBody[sel] stuck via
`PaperInfer.letE_none`). -/
private theorem paperInfer_archiveBodySubst_empty
    (i : Nat) (selected : SetLit)
    (hMinNone :
      Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) = none) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.ite (.setNonempty (Expr.lit (Literal.set selected)))
        (.letE loVar (.setMinField (Expr.lit (Literal.set selected)) idField)
          (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar archiveDeletePredicate))))
        .skip)
      (.ite
        (formulaOfExpr emptySymEnv (.setNonempty (Expr.lit (Literal.set selected))))
        SetLanguage.empty SetLanguage.empty) :=
  PaperInfer.ite (env := emptySymEnv)
    (cond := .setNonempty (Expr.lit (Literal.set selected)))
    (archive_transformerPre_stable i)
    (PaperInfer.letE_none hMinNone)
    (PaperInfer.skip (archive_transformerPost_stable _))

/-- `setNonempty` formula on a non-empty SetLit literal evaluates to true. -/
private theorem formulaOfExpr_setNonempty_nonempty
    (selected : SetLit) (hNonempty : selected ≠ [])
    (ld vd : Database) :
    formulaOfExpr emptySymEnv (.setNonempty (Expr.lit (Literal.set selected))) ld vd := by
  unfold formulaOfExpr
  simp [instantiateSymExpr, emptySymEnv, Expr.eval, Literal.toValue, Expr.setNonempty]
  -- setNonempty eval: scalar (bool (selected ≠ []))
  cases selected with
  | nil => exact (hNonempty rfl).elim
  | cons _ _ => nofun

/-- `setNonempty` on empty list is false. -/
private theorem formulaOfExpr_setNonempty_empty
    (ld vd : Database) :
    ¬ formulaOfExpr emptySymEnv (.setNonempty (Expr.lit (Literal.set ([] : SetLit)))) ld vd := by
  unfold formulaOfExpr
  simp [instantiateSymExpr, emptySymEnv, Expr.eval, Literal.toValue, Expr.setNonempty]

/-- Pointwise denote-iff for the insert side of the cascade-form ctor F.
Under `selectedLitMin sel = some lo` and `selectedLitMax sel = some hi0`,
the constructor-natural `insertedRowSet` (over `archiveRecordExpr i lo (hi0+1)`)
denotes the same row-set as `archiveLogInsertEffect_with_selected sel`. -/
private theorem insertedRowSet_iff_archive_insert_with_selected
    (i : Nat) (lo hi0 : Int) (selected : SetLit)
    (hSelMin : selectedLitMin selected = some lo)
    (hSelMax : selectedLitMax selected = some hi0)
    (ld vd : Database) (row : Row) :
    (insertedRowSet (archiveTxnId i) emptySymEnv
        (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1)))) ld vd row ↔
      archiveLogInsertEffect_with_selected (archiveTxnId i) i selected ld vd row := by
  unfold insertedRowSet archiveLogInsertEffect_with_selected
  have hEval :
      Expr.eval (instantiateSymExpr emptySymEnv []
          (archiveRecordExpr i (Expr.int lo) (addExpr (Expr.int hi0) (Expr.int 1)))) =
        some (Value.record (archiveRecord i lo (hi0 + 1))) := by
    simp [instantiateSymExpr, emptySymEnv, archiveRecordExpr, addExpr, Expr.eval,
      Literal.toValue, Expr.int, Expr.evalFieldValues, Bind.bind, Option.bind, Pure.pure,
      archiveRecord]
  rw [hEval]
  constructor
  · intro hRow
    exact ⟨lo, hi0, hSelMin, hSelMax, by rw [hRow]; rfl⟩
  · rintro ⟨lo', hi0', hMin', hMax', hOut⟩
    rw [hSelMin] at hMin'; rw [hSelMax] at hMax'
    cases hMin'; cases hMax'
    rw [hOut]
    rfl

/-- Pointwise denote-iff for the delete side. Under `selectedLitMin/Max sel = some lo/hi0`
and `wellFormedTableFields vd`, the constructor-natural `deleteSetExpr`
(predicate substituted with `lo/hi0` literals) denotes the same row-set as
`archiveLogDeleteEffect_with_selected sel`. -/
private theorem deleteSetExpr_iff_archive_delete_with_selected
    (i : Nat) (lo hi0 : Int) (selected : SetLit)
    (hSelMin : selectedLitMin selected = some lo)
    (hSelMax : selectedLitMax selected = some hi0)
    (ld vd : Database) (hWF : wellFormedTableFields vd) (row : Row) :
    (deleteSetExpr (archiveTxnId i) [] rowVar
        (Expr.subst hi0Var (Expr.int hi0)
          (Expr.subst loVar (Expr.int lo) archiveDeletePredicate))) ld vd row ↔
      archiveLogDeleteEffect_with_selected (archiveTxnId i) selected ld vd row := by
  have hPredEq :
      (Expr.subst hi0Var (Expr.int hi0)
          (Expr.subst loVar (Expr.int lo) archiveDeletePredicate)) =
        (Expr.binop BinOp.and
          (Expr.binop BinOp.eq ((Expr.var rowVar).proj tableField)
            (Expr.lit (.scalar (.int logTable))))
          (Expr.binop BinOp.and
            (Expr.binop BinOp.le (Expr.lit (.scalar (.int lo)))
              ((Expr.var rowVar).proj idField))
            (Expr.binop BinOp.le ((Expr.var rowVar).proj idField)
              (Expr.lit (.scalar (.int hi0)))))) := by
    unfold archiveDeletePredicate andExpr leExpr isLogExpr isTableExpr eqExpr fieldExpr
      loVar hi0Var rowVar Expr.int
    simp [Expr.subst]
  unfold deleteSetExpr deleteSetExprWith
  unfold SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb
  unfold archiveLogDeleteEffect_with_selected
  simp only [instantiateExpr_nil]
  rw [hPredEq]
  constructor
  · rintro ⟨src, hSrc, hBody⟩
    classical
    by_cases hPred : rowPredicateFormula [] rowVar
        (Expr.binop BinOp.and
          (Expr.binop BinOp.eq ((Expr.var rowVar).proj tableField)
            (Expr.lit (.scalar (.int logTable))))
          (Expr.binop BinOp.and
            (Expr.binop BinOp.le (Expr.lit (.scalar (.int lo)))
              ((Expr.var rowVar).proj idField))
            (Expr.binop BinOp.le ((Expr.var rowVar).proj idField)
              (Expr.lit (.scalar (.int hi0)))))) src
    · have hOut : row = src.markDeleted (archiveTxnId i) := by
        simp [hPred, SetLanguage.singleton] at hBody
        exact hBody
      have hPred' :
          Semantics.satisfiesPredicate rowVar
            (Expr.binop BinOp.and
              (Expr.binop BinOp.eq ((Expr.var rowVar).proj tableField)
                (Expr.lit (.scalar (.int logTable))))
              (Expr.binop BinOp.and
                (Expr.binop BinOp.le (Expr.lit (.scalar (.int lo)))
                  ((Expr.var rowVar).proj idField))
                (Expr.binop BinOp.le ((Expr.var rowVar).proj idField)
                  (Expr.lit (.scalar (.int hi0)))))) src.visible = some true := by
        simpa [rowPredicateFormula, instantiateExpr_nil] using hPred
      have hSat := (satisfiesPredicate_archiveDelete_iff src lo hi0).mp hPred'
      rcases hSat with ⟨hTab, n, hId, hLo, hHi⟩
      have hKey : src.key? = some (logTable, n) :=
        rowKey?_of_table_id_fields hTab hId
      exact ⟨src, n, lo, hi0, hSelMin, hSelMax, hSrc, hKey, hLo, hHi, hOut⟩
    · simp [hPred, SetLanguage.empty] at hBody
  · rintro ⟨src, n, lo', hi0', hMin', hMax', hSrcMem, hKey, hLo, hHi, hOut⟩
    rw [hSelMin] at hMin'; rw [hSelMax] at hMax'
    cases hMin'; cases hMax'
    refine ⟨src, hSrcMem, ?_⟩
    classical
    have hTab : rowFieldInt? src tableField = some logTable :=
      rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem hKey
    have hId : rowFieldInt? src idField = some n :=
      rowFieldInt?_idField_of_key hKey
    have hSat :=
      (satisfiesPredicate_archiveDelete_iff src lo hi0).mpr ⟨hTab, n, hId, hLo, hHi⟩
    have hPred : rowPredicateFormula [] rowVar
        (Expr.binop BinOp.and
          (Expr.binop BinOp.eq ((Expr.var rowVar).proj tableField)
            (Expr.lit (.scalar (.int logTable))))
          (Expr.binop BinOp.and
            (Expr.binop BinOp.le (Expr.lit (.scalar (.int lo)))
              ((Expr.var rowVar).proj idField))
            (Expr.binop BinOp.le ((Expr.var rowVar).proj idField)
              (Expr.lit (.scalar (.int hi0)))))) src := by
      simpa [rowPredicateFormula, instantiateExpr_nil] using hSat
    simp [hPred, SetLanguage.singleton, SetLanguage.empty, hOut]

/-- If `setMinField` on a SetLit evaluates to a some, then `setMaxField` on the
same SetLit cannot return `none`. Used to dispatch the impossible
`min some / max none` case in the per-selected dispatch. -/
private theorem setMinField_some_setMaxField_some_unreachable
    (selected : SetLit) {lo : Int}
    (hMin : Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int lo))) :
    Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) ≠ none := by
  intro hMaxNone
  simp only [Expr.eval, Literal.toValue] at hMin hMaxNone
  cases hVals : Expr.collectIntFieldValues idField selected with
  | none => simp [hVals] at hMin
  | some values =>
    cases values with
    | nil => simp [hVals, Expr.minInt?] at hMin
    | cons v vs => simp [hVals, Expr.maxInt?] at hMaxNone

/-- Constructor-only PaperInfer for the body's per-selected case when `selected`
is non-empty. Uses `paperInfer_archiveBodySubst_nonempty` as the cascade base and
`PaperInfer.conseqF_withInv` to bridge from the constructor-natural ITE form
to `archiveLogEffect_with_selected sel`. -/
private theorem paperInfer_archiveBodyForSelected_nonempty
    (i : Nat) (selected : SetLit) (hNonempty : selected ≠ [])
    (lo hi0 : Int)
    (hMinEval :
      Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int lo)))
    (hMaxEval :
      Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) =
        some (Value.scalar (ScalarLit.int hi0))) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.ite (.setNonempty (Expr.lit (Literal.set selected)))
        (.letE loVar (.setMinField (Expr.lit (Literal.set selected)) idField)
          (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar archiveDeletePredicate))))
        .skip)
      (archiveLogEffect_with_selected (archiveTxnId i) i selected) := by
  have hSelMin : selectedLitMin selected = some lo := by simp [selectedLitMin, hMinEval]
  have hSelMax : selectedLitMax selected = some hi0 := by simp [selectedLitMax, hMaxEval]
  refine PaperInfer.conseqF_withInv
    (I := fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
    ?hStableI
    (paperInfer_archiveBodySubst_nonempty i lo hi0 selected hMinEval hMaxEval)
    ?hFEq
  case hStableI =>
    exact archiveIndexedInv_stableBi i
  case hFEq =>
    intro ld vd hInv hPost
    have hFormula : formulaOfExpr emptySymEnv (.setNonempty (Expr.lit (Literal.set selected))) ld vd :=
      formulaOfExpr_setNonempty_nonempty selected hNonempty ld vd
    have hWF : wellFormedTableFields vd := by
      rcases hInv.1 with ⟨_, _, _, _, hWF⟩
      exact hWF
    intro row
    have hRow := hPost row
    have hInsIff := insertedRowSet_iff_archive_insert_with_selected
      (i := i) (lo := lo) (hi0 := hi0) (selected := selected) hSelMin hSelMax [] vd row
    have hDelIff := deleteSetExpr_iff_archive_delete_with_selected
      (i := i) (lo := lo) (hi0 := hi0) (selected := selected) hSelMin hSelMax [] vd hWF row
    have hFormula' : formulaOfExpr emptySymEnv
        (.setNonempty (Expr.lit (Literal.set selected))) [] vd := hFormula
    simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote_empty, false_or,
      SetLanguage.denote, archiveCtorF_nonempty, SetLanguage.SetExpr.union,
      archiveLogEffect_with_selected, SetLanguage.SetExpr.ite,
      SetLanguage.Env.ofDatabases] at hRow ⊢
    rw [if_pos hFormula'] at hRow
    rw [hInsIff, hDelIff] at hRow
    exact hRow

/-- Constructor-only PaperInfer for the body's per-selected case when
`setMinField` returns none (covers `selected = []` and the case where records
in `selected` lack `idField`). Uses `paperInfer_archiveBodySubst_empty` as the
cascade base and `PaperInfer.conseqF_withInv` to bridge from the (vacuous)
ITE form to `archiveLogEffect_with_selected sel` (which is itself vacuous since
`selectedLitMin sel = none`). -/
private theorem paperInfer_archiveBodyForSelected_empty
    (i : Nat) (selected : SetLit)
    (hMinNone :
      Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) = none) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty
      (.ite (.setNonempty (Expr.lit (Literal.set selected)))
        (.letE loVar (.setMinField (Expr.lit (Literal.set selected)) idField)
          (.letE hi0Var (.setMaxField (Expr.lit (Literal.set selected)) idField)
            (.seq
              (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (Expr.int 1))))
              (.delete rowVar archiveDeletePredicate))))
        .skip)
      (archiveLogEffect_with_selected (archiveTxnId i) i selected) := by
  refine PaperInfer.conseqF_withInv
    (I := fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
    ?hStableI
    (paperInfer_archiveBodySubst_empty i selected hMinNone)
    ?hFEq
  case hStableI =>
    exact archiveIndexedInv_stableBi i
  case hFEq =>
    intro ld vd _hInv hPost
    have hMinNoneLit : selectedLitMin selected = none := by
      unfold selectedLitMin; rw [hMinNone]
    intro row
    have hRow := hPost row
    simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote_empty, false_or,
      SetLanguage.denote, SetLanguage.SetExpr.union, archiveLogEffect_with_selected,
      SetLanguage.SetExpr.ite, SetLanguage.Env.ofDatabases, ite_self] at hRow ⊢
    -- After simp, hRow : empty ∨ empty ↔ row ∈ ld (if cond collapsed via ite_self).
    refine Iff.trans ?_ hRow
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · rcases h with ⟨_, _, hMin, _, _⟩
        rw [hMinNoneLit] at hMin; cases hMin
      · rcases h with ⟨_, _, _, _, hMin, _, _, _, _, _, _⟩
        rw [hMinNoneLit] at hMin; cases hMin
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inl h

/-- Constructor-only variant of `paperInfer_archiveLogBody_indexed_via_lazy`.

The per-`selected` body PaperInfer is built using only PaperInfer constructors
(`.selectLazy / .ite / .letE / .letE_none / .seq / .insert / .delete / .skip /
.conseqF`) — no `viaLocalValid` for the body proof. The F-shape bridge from the
constructor-natural ITE form to `archiveLogEffect_with_selected sel` is handled
via `PaperInfer.conseqF_withInv`. -/
theorem paperInfer_archiveLogBody_indexed_via_lazy_pure (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty (archiveLogBody i)
      (fun localDb globalDb out =>
        ∃ selected,
          Semantics.collectSelected globalDb rowVar
              (instantiateSymExpr emptySymEnv [rowVar] (isLogExpr rowVar)) = some selected ∧
          archiveLogEffect_with_selected (archiveTxnId i) i selected localDb globalDb out) := by
  unfold archiveLogBody
  refine PaperInfer.selectLazy
    (env := emptySymEnv)
    (Fbody := archiveLogEffect_with_selected (archiveTxnId i) i)
    ?_ ?_ ?_
  · exact transformerPre_stable_relyMod_snapshot _ _
  · intro localDb visibleDb visibleDb' hR
    have := relyMod_snapshot_exec_silent localDb visibleDb visibleDb' hR
    rw [this]
  · intro selected
    -- Substituted body: `.ite (.setNonempty (.lit (.set selected))) compactBody[sel] .skip`
    simp only [Command.subst, Expr.subst, archiveCompactBody, Expr.subst_lit,
      Value.subst_toExpr, Value.toExpr]
    -- Case-split on selected emptiness, then dispatch to the per-case constructor lemma.
    -- Case on whether setMinField evaluates.
    cases hMin : Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) with
    | none =>
        exact paperInfer_archiveBodyForSelected_empty i selected hMin
    | some loVal =>
        rcases setMinField_lit_eval_int hMin with ⟨lo, hloVal⟩
        subst hloVal
        -- Now non-stuck on min. Case on max.
        cases hMax : Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) with
        | none =>
            -- Unreachable: if minInt? succeeds, maxInt? on the same list succeeds.
            exact absurd hMax (setMinField_some_setMaxField_some_unreachable selected hMin)
        | some hi0Val =>
            rcases setMaxField_lit_eval_int hMax with ⟨hi0, hhi0Val⟩
            subst hhi0Val
            -- Check if selected is empty or not.
            by_cases hEmpty : selected = []
            · -- selected = [] → setMinField [] = none, contradiction with hMin.
              subst hEmpty
              simp [Expr.eval, Literal.toValue, Expr.collectIntFieldValues, Expr.minInt?] at hMin
            · exact paperInfer_archiveBodyForSelected_nonempty i selected hEmpty lo hi0 hMin hMax


/-- Indexed `PaperInfer` derivation for `archiveLogBody` under SI's local rely
(which forces `visibleDb = visibleDb'`). The strengthening lets the guarantee
bridge know archive-id `i` is fresh in the visible database.

Proof structure (skeleton):

  refine PaperInfer.viaLocalValid ?_
  apply Logic.localValid_of_stutterRely _ relyMod_snapshot_exec_silent
  -- LocalValid (False rely) ... archiveLogBody (transformerPost empty F)

Body decomposition:

  archiveLogBody i = .select logsVar rowVar (isLogExpr rowVar)
                       (.ite (.setNonempty (.var logsVar))
                          (archiveCompactBody i) .skip)

Under False rely, env doesn't fire. After `.select`, `selected` is V_start's
log rows (V_end = V_start since no env interference). Then `.ite` branches:

  * non-empty: `archiveCompactBody[logsVar→selected]` runs, producing
    archiveRow + log delete markers. F's denotation at V_start matches.
  * empty: `.skip`, no writes. F's denotation at V_start is empty
    (selectedLogMin/Max existentials fail).

The full proof requires composing `localValid_*_false` rules through the
nested structure. That is the remaining substantial work for this sorry. -/
theorem paperInfer_archiveLogBody_indexed_final (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty (archiveLogBody i)
      (archiveLogEffect (archiveTxnId i) i) := by
  -- Use `_via_lazy_pure` (constructor-only LazyF post) +
  -- `PaperInfer.conseqF_withInv` to bridge to `archiveLogEffect` post
  -- under the invariant. The body proof is fully constructor-based now
  -- (no `viaLocalValid` for body, no False rely descent).
  refine PaperInfer.conseqF_withInv
    (I := fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
    ?hStableI (paperInfer_archiveLogBody_indexed_via_lazy_pure i) ?hBridge
  case hStableI =>
    -- Trivial under SI silent rely (vd doesn't change).
    intro localDb v v' hInv hStep
    have hEq := relyMod_snapshot_exec_silent localDb v v' hStep
    rw [hEq]; exact hInv
  case hBridge =>
    intro ld vd hInv hPostLazy
    intro row
    have hRowLazy := hPostLazy row
    simp only [transformerPost, SetLanguage.denote, SetLanguage.Env.ofDatabases,
      SetLanguage.SetExpr.union, SetLanguage.empty, false_or] at hRowLazy ⊢
    rw [← lazyF_iff_archiveLogEffect_at_invariant (i := i) hInv.1 row]
    exact hRowLazy

private theorem paperInfer_archiveLogBody_indexed_final_old (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty (archiveLogBody i)
      (archiveLogEffect (archiveTxnId i) i) := by
  refine PaperInfer.viaLocalValid ?_
  refine Logic.localValid_of_stutterRely ?_ relyMod_snapshot_exec_silent
  unfold archiveLogBody
  refine Logic.localValid_select_false_pinVd (archiveTxnId i) _ _ logsVar rowVar _ _ ?_
  intro localDb visibleDb selected hPre _hSelect
  -- Substituted body: `.ite (.setNonempty (.lit (.set selected)))
  --   (archiveCompactBody[logsVar→selected]) .skip`
  simp only [Command.subst, Expr.subst, archiveCompactBody, archiveDeletePredicate,
    archiveRecordExpr, isLogExpr, isTableExpr, eqExpr, fieldExpr, andExpr,
    leExpr, addExpr]
  -- Some of those names may not unfold; the `.lit (.set selected)` substitution
  -- propagates into setMinField/setMaxField etc. Continue with localValid_ite_false.
  refine Logic.localValid_ite_false (archiveTxnId i) _ _ _ _ _ ?_ ?_
  · -- True branch: nonempty selected. archiveCompactBody[logsVar→selected]
    -- decomposes into letE loVar / letE hi0Var / seq (insert) (delete).
    -- Same body structure as via_lazy, but the post uses the direct F
    -- (archiveLogEffect with selectedLogMin/Max vd). The pinVd combinator
    -- gives us vd = visibleDb in the Pre, and the selectedLitMin/Max ↔
    -- selectedLogMin/Max bridges close the gap.
    intro _hEvalTrue
    simp only [Command.subst, Expr.subst, archiveCompactBody, archiveDeletePredicate,
      archiveRecordExpr, isLogExpr, isTableExpr, eqExpr, fieldExpr, andExpr,
      leExpr, addExpr, if_true, if_false]
    cases hMinEval :
        Expr.eval (.setMinField (Expr.lit (Literal.set selected)) idField) with
    | none =>
        exact localValid_letE_none_false (archiveTxnId i) _ _ loVar _ _ hMinEval
    | some loVal =>
        refine Logic.localValid_let_false (archiveTxnId i) _ _ loVar _ _ loVal hMinEval ?_
        cases hMaxEval :
            Expr.eval (.setMaxField (Expr.lit (Literal.set selected)) idField) with
        | none =>
            exact localValid_letE_none_false (archiveTxnId i) _ _ hi0Var _ _ hMaxEval
        | some hi0Val =>
            refine Logic.localValid_let_false (archiveTxnId i) _ _ hi0Var _ _ hi0Val hMaxEval ?_
            simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
              Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr,
              logsVar, loVar, hi0Var, rowVar, idField, tableField, loField, hiField,
              show ("logs" : VarName) ≠ "lo" from by decide,
              show ("logs" : VarName) ≠ "hi0" from by decide,
              show ("logs" : VarName) ≠ "row" from by decide,
              show ("lo" : VarName) ≠ "hi0" from by decide,
              show ("lo" : VarName) ≠ "row" from by decide,
              show ("hi0" : VarName) ≠ "row" from by decide,
              if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
              Expr.int]
            obtain ⟨lo, hLoVal⟩ := setMinField_lit_eval_int hMinEval
            obtain ⟨hi0, hHi0Val⟩ := setMaxField_lit_eval_int hMaxEval
            subst hLoVal
            subst hHi0Val
            have hSelMin : selectedLitMin selected = some lo := by
              simp [selectedLitMin, hMinEval]
            have hSelMax : selectedLitMax selected = some hi0 := by
              simp [selectedLitMax, hMaxEval]
            -- Decompose seq with intermediate post carrying `vd = visibleDb` plus
            -- the invariant so the delete step has wellFormedness AND the bridge
            -- can apply (selectedLitMin/Max selected ↔ selectedLogMin/Max vd).
            refine Logic.localValid_seq_false (archiveTxnId i)
              (fun ld vd =>
                transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
                    SetLanguage.empty ld vd ∧ vd = visibleDb)
              (fun ld vd =>
                transformerPost SetLanguage.empty
                    (archiveLogInsertEffect (archiveTxnId i) i) ld vd ∧
                  logSystemInv vd ∧ archiveKeysFreshFrom i vd ∧ vd = visibleDb)
              (transformerPost SetLanguage.empty
                (archiveLogEffect (archiveTxnId i) i))
              _ _ ?_ ?_
            · -- Insert step
              refine Logic.localValid_insert_false (archiveTxnId i) _ _ _ ?_
              intro ld vd record hPre' hEval _hFresh
              rcases hPre' with ⟨hPre, hVdEq⟩
              rcases hPre with ⟨hLocal, hInv⟩
              refine ⟨?_, hInv.1, hInv.2, hVdEq⟩
              have hLdEmpty : ld = [] := by
                cases ld with
                | nil => rfl
                | cons row rest =>
                    have := (hLocal row).mpr List.mem_cons_self
                    simp [SetLanguage.denote, SetLanguage.empty] at this
              subst hLdEmpty
              simp only [Expr.eval, Value.toExpr, Literal.toValue,
                Expr.evalFieldValues, Bind.bind, Option.bind, Option.some_bind,
                Pure.pure] at hEval
              injection hEval with hEval
              injection hEval with hEval
              have hRecord : record = archiveRecord i lo (hi0 + 1) := by
                rw [← hEval]
                simp [archiveRecord, tableField, idField, loField, hiField]
              subst hRecord
              subst hVdEq
              have hWF : wellFormedTableFields vd := by
                rcases hInv.1 with ⟨_, _, _, _, hWF⟩
                exact hWF
              have hSelLogMin : selectedLogMin vd lo :=
                (selectedLitMin_iff_selectedLogMin _hSelect hWF).mp hSelMin
              have hSelLogMax : selectedLogMax vd hi0 :=
                (selectedLitMax_iff_selectedLogMax _hSelect hWF).mp hSelMax
              intro row
              simp only [transformerPost, List.nil_append, List.mem_singleton,
                SetLanguage.denote, SetLanguage.SetExpr.union, SetLanguage.empty,
                archiveLogInsertEffect, false_or]
              constructor
              · rintro ⟨lo', hi0', hMin', hMax', hOut⟩
                -- Both selectedLogMin's are about same vd, must agree
                rcases hMin' with ⟨⟨wA, hwAMem, hwAKey⟩, hMinUB⟩
                rcases hSelLogMin with ⟨⟨w, hwMem, hwKey⟩, hSelMinUB⟩
                have h₁ : lo' ≤ lo := hMinUB w lo ⟨hwMem, hwKey⟩
                have h₂ : lo ≤ lo' := hSelMinUB wA lo' ⟨hwAMem, hwAKey⟩
                have hLoEq : lo' = lo := by omega
                rcases hMax' with ⟨⟨wB, hwBMem, hwBKey⟩, hMaxUB⟩
                rcases hSelLogMax with ⟨⟨w2, hw2Mem, hw2Key⟩, hSelMaxUB⟩
                have h₃ : hi0 ≤ hi0' := hMaxUB w2 hi0 ⟨hw2Mem, hw2Key⟩
                have h₄ : hi0' ≤ hi0 := hSelMaxUB wB hi0' ⟨hwBMem, hwBKey⟩
                have hHiEq : hi0' = hi0 := by omega
                rw [hLoEq, hHiEq] at hOut
                exact hOut
              · intro hRow
                exact ⟨lo, hi0, hSelLogMin, hSelLogMax, hRow⟩
            · -- Delete step
              refine Logic.localValid_delete_false (archiveTxnId i) _ _ _ _ ?_
              intro ld vd removed hPre' hCollect _hDisjoint
              rcases hPre' with ⟨hPostIns, hInv, _hKeysFresh, hVdEq⟩
              subst hVdEq
              have hWF : wellFormedTableFields vd := by
                rcases hInv with ⟨_, _, _, _, hWF⟩
                exact hWF
              have hSelLogMin : selectedLogMin vd lo :=
                (selectedLitMin_iff_selectedLogMin _hSelect hWF).mp hSelMin
              have hSelLogMax : selectedLogMax vd hi0 :=
                (selectedLitMax_iff_selectedLogMax _hSelect hWF).mp hSelMax
              simp only [transformerPost, SetLanguage.denote,
                SetLanguage.SetExpr.union, SetLanguage.empty,
                archiveLogInsertEffect, archiveLogDeleteEffect,
                archiveLogEffect, false_or] at hPostIns ⊢
              intro row
              rw [List.mem_append]
              constructor
              · rintro (hIns | hDel)
                · rcases hIns with ⟨lo', hi0', hMin', hMax', hOut⟩
                  rcases hMin' with ⟨⟨wA, hwAMem, hwAKey⟩, hMinUB⟩
                  obtain ⟨⟨w, hwMem, hwKey⟩, hSelMinUB⟩ := hSelLogMin
                  obtain ⟨⟨w2, hw2Mem, hw2Key⟩, hSelMaxUB⟩ := hSelLogMax
                  have h₁ : lo' ≤ lo := hMinUB w lo ⟨hwMem, hwKey⟩
                  have h₂ : lo ≤ lo' := hSelMinUB wA lo' ⟨hwAMem, hwAKey⟩
                  have hLoEq : lo' = lo := by omega
                  rcases hMax' with ⟨⟨wB, hwBMem, hwBKey⟩, hMaxUB⟩
                  have h₃ : hi0 ≤ hi0' := hMaxUB w2 hi0 ⟨hw2Mem, hw2Key⟩
                  have h₄ : hi0' ≤ hi0 := hSelMaxUB wB hi0' ⟨hwBMem, hwBKey⟩
                  have hHiEq : hi0' = hi0 := by omega
                  rw [hLoEq, hHiEq] at hOut
                  left
                  exact (hPostIns row).mp ⟨lo, hi0,
                    ⟨⟨w, hwMem, hwKey⟩, hSelMinUB⟩,
                    ⟨⟨w2, hw2Mem, hw2Key⟩, hSelMaxUB⟩, hOut⟩
                · rcases hDel with ⟨src, n, lo', hi0', hMin', hMax', hSelRow, hLo, hHi, hOut⟩
                  rcases hMin' with ⟨⟨wA, hwAMem, hwAKey⟩, hMinUB⟩
                  obtain ⟨⟨w, hwMem, hwKey⟩, hSelMinUB⟩ := hSelLogMin
                  obtain ⟨⟨w2, hw2Mem, hw2Key⟩, hSelMaxUB⟩ := hSelLogMax
                  have h₁ : lo' ≤ lo := hMinUB w lo ⟨hwMem, hwKey⟩
                  have h₂ : lo ≤ lo' := hSelMinUB wA lo' ⟨hwAMem, hwAKey⟩
                  have hLoEq : lo' = lo := by omega
                  rcases hMax' with ⟨⟨wB, hwBMem, hwBKey⟩, hMaxUB⟩
                  have h₃ : hi0 ≤ hi0' := hMaxUB w2 hi0 ⟨hw2Mem, hw2Key⟩
                  have h₄ : hi0' ≤ hi0 := hSelMaxUB wB hi0' ⟨hwBMem, hwBKey⟩
                  have hHiEq : hi0' = hi0 := by omega
                  rw [hLoEq] at hLo
                  rw [hHiEq] at hHi
                  rcases hSelRow with ⟨hSrcMem, hSrcKey⟩
                  right
                  rw [Semantics.mem_collectDeleted_iff hCollect]
                  refine ⟨src, hSrcMem, ?_, hOut⟩
                  have hTab : rowFieldInt? src tableField = some logTable :=
                    rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem hSrcKey
                  have hSat :=
                    (satisfiesPredicate_archiveDelete_iff src lo hi0).mpr
                      ⟨hTab, n, rowFieldInt?_idField_of_key hSrcKey, hLo, hHi⟩
                  exact hSat
              · rintro (hLd | hRem)
                · left
                  exact (hPostIns row).mpr hLd
                · right
                  rw [Semantics.mem_collectDeleted_iff hCollect] at hRem
                  rcases hRem with ⟨src, hSrc, hSat, hOut⟩
                  have hSat' := (satisfiesPredicate_archiveDelete_iff src lo hi0).mp hSat
                  rcases hSat' with ⟨hTab, n, hId, hLo, hHi⟩
                  have hKey : src.key? = some (logTable, n) :=
                    rowKey?_of_table_id_fields hTab hId
                  exact ⟨src, n, lo, hi0, hSelLogMin, hSelLogMax,
                    ⟨hSrc, hKey⟩, hLo, hHi, hOut⟩
  · -- False branch: empty selected. Substituted body is .skip.
    intro hEvalFalse
    -- Extract `selected = []` from hEvalFalse.
    have hSelectedEmpty : selected = [] := by
      cases hSel : selected with
      | nil => rfl
      | cons head tail =>
          exfalso
          simp [Expr.eval, Literal.toValue, hSel] at hEvalFalse
    -- Local row characterization: visibleDb has no log rows.
    have hSelectEmpty : Semantics.collectSelected visibleDb rowVar (isLogExpr rowVar) = some [] := by
      rw [hSelectedEmpty] at _hSelect
      exact _hSelect
    -- Extract wellFormedTableFields from precondition's invariant.
    have hWF : wellFormedTableFields visibleDb := by
      rcases hPre with ⟨_, hInv, _⟩
      rcases hInv with ⟨_, _, _, _, hWF⟩
      exact hWF
    have hNoLogs : ∀ row, row ∈ visibleDb → ∀ n : Int, row.key? ≠ some (logTable, n) := by
      intro row hMem n hKey
      -- From key? = some (logTable, n) + wellFormedTableFields: rowFieldInt? tableField = logTable.
      have hTable : rowFieldInt? row tableField = some logTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWF hMem hKey
      -- Hence isLogExpr predicate is satisfied.
      have hSat : Semantics.satisfiesPredicate rowVar (isLogExpr rowVar) row.visible = some true :=
        (satisfiesPredicate_isTableExpr_iff row logTable).mpr hTable
      -- But collectSelected returned [], so no row satisfies — contradiction.
      have hNoMatch : Semantics.satisfiesPredicate rowVar (isLogExpr rowVar) row.visible = some false :=
        collectSelected_empty_no_match hSelectEmpty row hMem
      rw [hSat] at hNoMatch
      cases hNoMatch
    -- Use localValid_skip_false + conseq with the strengthened Pre' = Pre ∧ vd = visibleDb.
    -- The key bridge: vd = visibleDb gives us hNoLogs to discharge archiveLogEffect at vd.
    refine Logic.localValid_conseq
      (P := fun ld vd =>
        transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
            SetLanguage.empty ld vd ∧ vd = visibleDb)
      (P' := fun ld vd =>
        transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
            SetLanguage.empty ld vd ∧ vd = visibleDb)
      (Q' := fun ld vd =>
        transformerPre (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
            SetLanguage.empty ld vd ∧ vd = visibleDb)
      (fun _ _ h => h)
      (Logic.localValid_skip_false (archiveTxnId i) _) ?_
    intro localDb' visibleDb' hPre'
    rcases hPre' with ⟨hPreOnly, hVdEq⟩
    subst hVdEq
    rcases hPreOnly with ⟨hLocal, _hInv⟩
    have hLocalEmpty : localDb' = [] := by
      cases localDb' with
      | nil => rfl
      | cons row rest =>
          have := (hLocal row).mpr List.mem_cons_self
          simp [SetLanguage.denote, SetLanguage.empty] at this
    subst hLocalEmpty
    intro row
    simp only [transformerPost, SetLanguage.denote, SetLanguage.SetExpr.union,
      SetLanguage.empty, archiveLogEffect, archiveLogInsertEffect,
      archiveLogDeleteEffect, false_or, List.not_mem_nil, iff_false]
    rintro (⟨lo, hi0, hMin, _hMax, _hOut⟩ | ⟨src, n, lo, hi0, _hMin, _hMax, hSel, _hLo, _hHi, _hOut⟩)
    · rcases hMin with ⟨⟨witLo, hWitMem, hWitKey⟩, _hMinUB⟩
      exact hNoLogs witLo hWitMem _ hWitKey
    · rcases hSel with ⟨hSrcMem, hSrcKey⟩
      exact hNoLogs src hSrcMem _ hSrcKey

/-- Per-rec accumulator predicate used by the `selectAllLogBody` foreach loop
invariant. It says `row` is in the local DB iff it is the result of running
`selectEntryResultEffect` against some entry whose `visible` record was already
processed (i.e., lies in `done`). -/
private def selectAllLogBody_doneContrib
    (q : Nat) (visibleDb : Database) (done : SetLit) (row : Row) : Prop :=
  ∃ rec, rec ∈ done ∧
    ∃ srcRow, srcRow ∈ visibleDb ∧ srcRow.visible = rec ∧
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
        (selectEntryResultEffect (selectTxnId q) q srcRow) row

/-- Per-entry result effect matching the body's operational behavior for
**arbitrary** entries, as required by `PaperInfer.selectLazy`'s universal-`y`
body hypothesis (paper 1710.09844v2.pdf, Appendix C, p.45 SELECT case:
"y occurs free in c and by the inductive hypothesis, any binding of y can be used").

The body's outer `.ite (isLogExpr entry)` evaluates to:
- `some (.bool true)` when `entry.lookup? "table" = some (.int logTable)` →
  insert one resultRow at `entry.id`.
- `some (.bool false)` when `entry.lookup? "table" = some (.int t)` with
  `t ≠ logTable`, or `some (.bool _)` → inner foreach over `[entry.lo, entry.hi)`.
- `none` when `entry.lookup? "table" = none` → body stuck (no contribution).

For storage entries (sel from `collectSelected` with `isStorageEntryExpr`),
`entry.lookup? "table" ∈ {some (.int logTable), some (.int archiveTable)}`. -/
private def selectEntryResultEffect_byRecord (q : Nat) (entry : RecordLit) :
    SetLanguage.SetExpr :=
  fun _localDb _globalDb row =>
    (entry.lookup? "table" = some (.int logTable) ∧
      ∃ n, entry.lookup? "id" = some (.int n) ∧
        row = resultRowLit (selectTxnId q) q n) ∨
    (entry.lookup? "table" ≠ some (.int logTable) ∧
      entry.lookup? "table" ≠ none ∧
      ∃ lo hi n, entry.lookup? "lo" = some (.int lo) ∧
        entry.lookup? "hi" = some (.int hi) ∧
        lo ≤ n ∧ n < hi ∧ row = resultRowLit (selectTxnId q) q n)

/-- `selectAllLogEffect_byRecord sel`: per-`sel` formulation purely determined
by `sel`'s entries (no dependence on `vd`). This matches the foreach body's
operational effect under universal `sel`, suitable for `PaperInfer.selectLazy`. -/
private def selectAllLogEffect_byRecord (q : Nat) (selected : SetLit) :
    SetLanguage.SetExpr :=
  fun localDb globalDb row =>
    ∃ entry, entry ∈ selected ∧
      selectEntryResultEffect_byRecord q entry localDb globalDb row

/-- `_byRecord` analog of `selectAllLogBody_doneContrib`: purely sel-determined
accumulator predicate. -/
private def selectAllLogBody_doneContrib_byRecord
    (q : Nat) (done : SetLit) (row : Row) : Prop :=
  ∃ entry, entry ∈ done ∧
    selectEntryResultEffect_byRecord q entry [] [] row

/-- Per-row bridge between `selectAllLogEffect_byRecord` (purely sel-determined)
and `selectAllLogEffect_with_selected` (requires source-row in vd). Holds under
`hSelect : collectSelected vd ... = some sel` + `hWF : wellFormedTableFields vd`,
since `sel`'s entries correspond bijectively to storage rows in `vd`. -/
private theorem selectAllLogEffect_byRecord_iff_with_selected
    {q : Nat} {ld vd : Database} {selected : SetLit}
    (hSelect : Semantics.collectSelected vd rowVar (isStorageEntryExpr rowVar) = some selected)
    (hWF : wellFormedTableFields vd) (row : Row) :
    selectAllLogEffect_byRecord q selected ld vd row ↔
    selectAllLogEffect_with_selected (selectTxnId q) q selected ld vd row := by
  unfold selectAllLogEffect_byRecord selectAllLogEffect_with_selected
  -- Helper: srcRow.visible = entry implies lookup-table equivalence.
  have hTabBridge : ∀ (entry : RecordLit) (srcRow : Row), srcRow.visible = entry →
      ∀ t, rowFieldInt? srcRow tableField = some t ↔ entry.lookup? "table" = some (.int t) := by
    intros entry srcRow hSrcVis t
    unfold rowFieldInt? tableField
    rw [hSrcVis]
    cases hT : entry.lookup? "table" with
    | none => simp [hT]
    | some lit =>
      cases lit with
      | int v => simp [hT]
      | bool _ => simp [hT]
  constructor
  · rintro ⟨entry, hEntry, hEff⟩
    rcases (mem_selected_iff_storage_entry hSelect hWF entry).mp hEntry with
      ⟨srcRow, hSrcMem, hKeyOr, hSrcVis⟩
    refine ⟨entry, hEntry, srcRow, hSrcMem, hSrcVis, ?_⟩
    unfold selectEntryResultEffect_byRecord at hEff
    unfold selectEntryResultEffect SetLanguage.SetExpr.union
    rcases hEff with hLog | hNonLog
    · left
      unfold selectLogResultEffect
      rcases hLog with ⟨hTableLog, n, hId, hRow⟩
      have hSrcKey : srcRow.key? = some (logTable, n) := by
        unfold Row.key? RecordLit.key? RecordLit.table? RecordLit.id?
        rw [hSrcVis, hTableLog, hId]
      refine ⟨n, ⟨n, hSrcKey⟩, ?_, hRow⟩
      rw [rowFieldInt?_eq_some_iff_lookup, hSrcVis]; exact hId
    · right
      unfold selectArchiveResultEffect
      rcases hNonLog with ⟨hTNeLog, _hTNeNone, lo, hi, n, hLo, hHi, hLoLe, hLtHi, hRow⟩
      -- For storage entries: srcRow.key? is log or archive. Since entry's table ≠ log, must be archive.
      have hSrcArch : ∃ id, srcRow.key? = some (archiveTable, id) := by
        rcases hKeyOr with ⟨_, hLogKey⟩ | hArch
        · exfalso
          have hTab : rowFieldInt? srcRow tableField = some logTable :=
            rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem hLogKey
          exact hTNeLog ((hTabBridge entry srcRow hSrcVis logTable).mp hTab)
        · exact hArch
      refine ⟨lo, hi, n, hSrcArch, ?_, ?_, hLoLe, hLtHi, hRow⟩
      · rw [rowFieldInt?_eq_some_iff_lookup, hSrcVis]; exact hLo
      · rw [rowFieldInt?_eq_some_iff_lookup, hSrcVis]; exact hHi
  · rintro ⟨entry, hEntry, srcRow, hSrcMem, hSrcVis, hEff⟩
    refine ⟨entry, hEntry, ?_⟩
    unfold selectEntryResultEffect SetLanguage.SetExpr.union at hEff
    unfold selectEntryResultEffect_byRecord
    rcases hEff with hLog | hArch
    · left
      unfold selectLogResultEffect at hLog
      rcases hLog with ⟨n, ⟨_id, hSrcLogKey⟩, hSrcId, hRow⟩
      have hSrcTab : rowFieldInt? srcRow tableField = some logTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem hSrcLogKey
      have hTable : entry.lookup? "table" = some (.int logTable) :=
        (hTabBridge entry srcRow hSrcVis logTable).mp hSrcTab
      refine ⟨hTable, n, ?_, hRow⟩
      have := rowFieldInt?_eq_some_iff_lookup.mp hSrcId
      rw [hSrcVis] at this; exact this
    · right
      unfold selectArchiveResultEffect at hArch
      rcases hArch with ⟨lo, hi, n, ⟨_id, hSrcArchKey⟩, hSrcLo, hSrcHi, hLoLe, hLtHi, hRow⟩
      have hSrcTab : rowFieldInt? srcRow tableField = some archiveTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem hSrcArchKey
      have hTable : entry.lookup? "table" = some (.int archiveTable) :=
        (hTabBridge entry srcRow hSrcVis archiveTable).mp hSrcTab
      refine ⟨?_, ?_, lo, hi, n, ?_, ?_, hLoLe, hLtHi, hRow⟩
      · rw [hTable]; intro h; injection h with h; injection h with h
        exact absurd h (by decide : archiveTable ≠ logTable)
      · rw [hTable]; intro h; cases h
      · have := rowFieldInt?_eq_some_iff_lookup.mp hSrcLo
        rw [hSrcVis] at this; exact this
      · have := rowFieldInt?_eq_some_iff_lookup.mp hSrcHi
        rw [hSrcVis] at this; exact this

/-- `_byRecord` version: inner `foreachRuntime` over `intRangeRecords "id" lo hi`
for the archive-head case. Operates purely on `head : RecordLit`'s fields
(no `headRow ∈ visibleDb` needed). -/
private theorem selectAllLogBody_archive_inner_foreach_byRecord
    (q : Nat) (done : SetLit) (head : RecordLit) (lo hi : Int)
    (hHeadTable : head.lookup? "table" ≠ some (.int logTable) ∧
                  head.lookup? "table" ≠ none)
    (hHeadLo : head.lookup? "lo" = some (.int lo))
    (hHeadHi : head.lookup? "hi" = some (.int hi))
    (_hLeq : lo ≤ hi) :
    ∀ (rangeDone rangeRest : SetLit),
      rangeDone ++ rangeRest = Expr.intRangeRecords "id" lo hi →
      Logic.LocalValid (ι := IsolationSpec Database) (fun _ _ _ => False) (selectTxnId q)
        (fun ld _vd =>
          ∀ row, row ∈ ld ↔
            (selectAllLogBody_doneContrib_byRecord q done row ∨
              ∃ rec, rec ∈ rangeDone ∧ ∃ id : Int,
                rec.lookup? "id" = some (.int id) ∧
                row = resultRowLit (selectTxnId q) q id))
        (Command.foreachRuntime (Expr.setLit rangeDone) (Expr.setLit rangeRest)
          rangeDoneVar rangeElemVar
          (Command.subst doneVar (Expr.setLit done)
            (Command.insert (Expr.subst entryVar (.lit (.record head))
              (resultRecordExpr q (fieldExpr rangeElemVar idField))))))
        (fun ld _vd =>
          ∀ row, row ∈ ld ↔
            selectAllLogBody_doneContrib_byRecord q (done ++ [head]) row) := by
  intro rangeDone rangeRest hSplit
  induction rangeRest generalizing rangeDone with
  | nil =>
      have hRangeDoneEq : rangeDone = Expr.intRangeRecords "id" lo hi := by
        simpa using hSplit
      subst hRangeDoneEq
      refine Logic.localValid_foreachDone (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?_ ?_
      · intro _ _ _ _ hR; exact False.elim hR
      · intro ld vd hLdMem
        intro row
        rw [hLdMem row]
        unfold selectAllLogBody_doneContrib_byRecord
        constructor
        · rintro (hDC | hRec)
          · rcases hDC with ⟨rec, hRecMem, hEff⟩
            exact ⟨rec, List.mem_append_left _ hRecMem, hEff⟩
          · rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
            simp [Expr.intRangeRecords, List.mem_map, List.mem_range, idField] at hRecMem
            rcases hRecMem with ⟨k, hkLt, hRecForm⟩
            subst hRecForm
            have hIdEq : id = lo + (k : Int) := by
              simp [RecordLit.lookup?, idField] at hRecId; omega
            subst hIdEq
            have hLeId : lo ≤ lo + (k : Int) := by
              have : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
              omega
            have hIdLt : lo + (k : Int) < hi := by
              have hCast : (k : Int) < hi - lo := by exact_mod_cast hkLt
              omega
            refine ⟨head, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
            unfold selectEntryResultEffect_byRecord
            right
            exact ⟨hHeadTable.1, hHeadTable.2, lo, hi, lo + (k : Int), hHeadLo, hHeadHi, hLeId, hIdLt, hRowEq⟩
        · rintro ⟨rec, hRecMem, hEff⟩
          rcases List.mem_append.mp hRecMem with hRecDone | hRecHead
          · left; exact ⟨rec, hRecDone, hEff⟩
          · rw [List.mem_singleton] at hRecHead
            subst hRecHead
            unfold selectEntryResultEffect_byRecord at hEff
            rcases hEff with hLog | hArch
            · exfalso
              rcases hLog with ⟨hLogTab, _⟩
              exact hHeadTable.1 hLogTab
            · rcases hArch with ⟨_hTNeLog, _hTNeNone, lo', hi', n', hLo', hHi', hLoLeN, hNLtHi, hRowEq⟩
              rw [hHeadLo] at hLo'; rw [hHeadHi] at hHi'
              have hLoEq : lo' = lo := (ScalarLit.int.inj (Option.some.inj hLo')).symm
              have hHiEq : hi' = hi := (ScalarLit.int.inj (Option.some.inj hHi')).symm
              right
              rw [hLoEq] at hLoLeN
              rw [hHiEq] at hNLtHi
              have hNGeLo : (0 : Int) ≤ n' - lo := by omega
              have hOffsetEq : ((n' - lo).toNat : Int) = n' - lo := Int.toNat_of_nonneg hNGeLo
              have hOffsetLt : ((n' - lo).toNat : Int) < hi - lo := by omega
              refine ⟨⟨[(idField, .int (lo + ((n' - lo).toNat : Int)))]⟩, ?_, n', ?_, hRowEq⟩
              · simp [Expr.intRangeRecords, List.mem_map, List.mem_range, idField]
                refine ⟨(n' - lo).toNat, hOffsetLt, ?_⟩
                rw [Int.toNat_of_nonneg hNGeLo]; omega
              · simp [RecordLit.lookup?, idField]; omega
  | cons current rest ih =>
      have hSplit' : (rangeDone ++ [current]) ++ rest = Expr.intRangeRecords "id" lo hi := by
        rw [List.append_assoc]; simpa using hSplit
      have hCurrentInRange : current ∈ Expr.intRangeRecords "id" lo hi := by
        rw [← hSplit]; simp
      have hCurrentForm : ∃ k : Nat, ((k : Int) < hi - lo) ∧
          ⟨[(idField, .int (lo + (k : Int)))]⟩ = current := by
        simp [Expr.intRangeRecords, List.mem_map, List.mem_range, idField] at hCurrentInRange
        exact hCurrentInRange
      rcases hCurrentForm with ⟨k, _hkLt, hCurForm⟩
      have hCurId : current.lookup? "id" = some (.int (lo + (k : Int))) := by
        rw [← hCurForm]; simp [RecordLit.lookup?, idField]
      apply Logic.localValid_foreachNext (fun _ _ _ => False) (selectTxnId q)
      · intro _ _ _ _ hR; exact False.elim hR
      · refine Logic.localValid_seq_false (selectTxnId q) _
          (fun ld _vd =>
            ∀ row, row ∈ ld ↔
              (selectAllLogBody_doneContrib_byRecord q done row ∨
                ∃ rec, rec ∈ (rangeDone ++ [current]) ∧ ∃ id : Int,
                  rec.lookup? "id" = some (.int id) ∧
                  row = resultRowLit (selectTxnId q) q id))
          _ _ _ ?_ ?_
        · simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
            Expr.substFieldExprs_nil, Expr.subst_lit,
            doneVar, entryVar, rangeDoneVar, rangeElemVar,
            idField, loField, hiField, tableField,
            show ("entry" : VarName) ≠ "num" from by decide,
            show ("entry" : VarName) ≠ "rangeDone" from by decide,
            show ("done" : VarName) ≠ "entry" from by decide,
            show ("done" : VarName) ≠ "rangeDone" from by decide,
            show ("done" : VarName) ≠ "num" from by decide,
            show ("num" : VarName) ≠ "rangeDone" from by decide,
            show ("num" : VarName) ≠ "entry" from by decide,
            show ("rangeDone" : VarName) ≠ "entry" from by decide,
            show ("rangeDone" : VarName) ≠ "done" from by decide,
            show ("rangeDone" : VarName) ≠ "num" from by decide,
            if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
            dite_eq_left_iff, dite_eq_right_iff]
          refine Logic.localValid_insert_false (selectTxnId q) _ _ _ ?_
          intro ld vd record hLdMem hEval _hFresh
          have hRecordEq : record = resultRecord q (lo + (k : Int)) := by
            simp [resultRecordExpr, fieldExpr, Expr.int, Expr.subst, Expr.eval,
              Expr.evalFieldValues, Literal.toValue, hCurId,
              resultRecord, tableField, idField] at hEval
            exact hEval.symm
          subst hRecordEq
          intro row
          constructor
          · intro hRow
            rcases List.mem_append.mp hRow with hLd | hNew
            · rcases (hLdMem row).mp hLd with hDC | hRec
              · left; exact hDC
              · right
                rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
                exact ⟨rec, List.mem_append_left _ hRecMem, id, hRecId, hRowEq⟩
            · rw [List.mem_singleton] at hNew
              subst hNew
              right
              refine ⟨current, List.mem_append_right _ (List.mem_singleton_self _),
                lo + (k : Int), hCurId, ?_⟩
              rfl
          · rintro (hDC | hRec)
            · exact List.mem_append_left _ ((hLdMem row).mpr (Or.inl hDC))
            · rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
              rcases List.mem_append.mp hRecMem with hRecDone | hRecCur
              · exact List.mem_append_left _
                  ((hLdMem row).mpr (Or.inr ⟨rec, hRecDone, id, hRecId, hRowEq⟩))
              · rw [List.mem_singleton] at hRecCur
                subst hRecCur
                rw [hCurId] at hRecId
                have hIdEq : id = lo + (k : Int) := (ScalarLit.int.inj
                  (Option.some.inj hRecId)).symm
                subst hIdEq
                rw [hRowEq]
                exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact ih (rangeDone ++ [current]) hSplit'

/-- `_byRecord` version of the main foreach loop invariant. Purely sel-determined
post (no visibleDb dependence). Handles arbitrary entries (per universal-y of
PaperInfer.selectLazy, paper Appendix C p.45).

**Status (paper alignment verified):** the proof of this lemma requires
handling cases where head's `lookup? "id"` returns a `.bool` value
(under ITE-true branch with `table = logTable`). For such heads, the body
inserts a row with a bool-valued id, but `selectEntryResultEffect_byRecord`'s
log case requires `entry.lookup? "id" = some (.int n)`. The mismatch makes
the proof technically unprovable with the current narrow `_byRecord` def
when `head` is non-int-id.

In practice (sel = `collectSelected ... isStorageEntryExpr`), all storage
entries have int id by construction. So the proof works for the actual use
case but not for universal-y as required by `PaperInfer.selectLazy`.

To fully fill: either widen `selectEntryResultEffect_byRecord` to capture
any-scalar id (which makes the bridge `_byRecord_iff_with_selected` more
complex), or restrict `PaperInfer.selectLazy.hBody` to storage-y (paper-aligned
SELECT case strengthens body pre with `y = collectSelected`, see p.45). -/
private theorem selectAllLogBody_foreach_invariant_byRecord
    (q : Nat) (selected : SetLit) :
    ∀ (done rest : SetLit), done ++ rest = selected →
      Logic.LocalValid (ι := IsolationSpec Database) (fun _ _ _ => False) (selectTxnId q)
        (fun ld _vd =>
          ∀ row, row ∈ ld ↔ selectAllLogBody_doneContrib_byRecord q done row)
        (Command.foreachRuntime (Expr.setLit done) (Expr.setLit rest) doneVar entryVar
          (Command.ite (isLogExpr entryVar)
             (Command.insert (resultRecordExpr q (fieldExpr entryVar idField)))
             (Command.foreach
                (Expr.rangeRows idField
                  (fieldExpr entryVar loField) (fieldExpr entryVar hiField))
                rangeDoneVar rangeElemVar
                (Command.insert
                  (resultRecordExpr q (fieldExpr rangeElemVar idField))))))
        (transformerPost SetLanguage.empty
          (selectAllLogEffect_byRecord q selected)) := by
  sorry

/-- Helper for the archive-head case: inner `foreachRuntime` over
`intRangeRecords "id" lo hi`. Each iteration inserts `resultRowLit q (lo+offset)`
for the current record's id. After processing all `rangeRest`, the local DB
contains exactly the archive contribution of `head`. -/
private theorem selectAllLogBody_archive_inner_foreach
    (q : Nat) (visibleDb : Database) (done : SetLit)
    (head : RecordLit) (lo hi : Int)
    (headRow : Row) (hHeadRowMem : headRow ∈ visibleDb)
    (hHeadVis : headRow.visible = head)
    (nKey : Int)
    (hHeadKey' : head.key? = some (archiveTable, nKey))
    (hHeadLo : head.lookup? "lo" = some (.int lo))
    (hHeadHi : head.lookup? "hi" = some (.int hi))
    (hLeq : lo ≤ hi) :
    ∀ (rangeDone rangeRest : SetLit),
      rangeDone ++ rangeRest = Expr.intRangeRecords "id" lo hi →
      Logic.LocalValid (ι := IsolationSpec Database) (fun _ _ _ => False) (selectTxnId q)
        (fun ld vd => vd = visibleDb ∧
          ∀ row, row ∈ ld ↔
            (selectAllLogBody_doneContrib q visibleDb done row ∨
              ∃ rec, rec ∈ rangeDone ∧ ∃ id : Int,
                rec.lookup? "id" = some (.int id) ∧
                row = resultRowLit (selectTxnId q) q id))
        (Command.foreachRuntime (Expr.setLit rangeDone) (Expr.setLit rangeRest)
          rangeDoneVar rangeElemVar
          (Command.subst doneVar (Expr.setLit done)
            (Command.insert (Expr.subst entryVar (.lit (.record head))
              (resultRecordExpr q (fieldExpr rangeElemVar idField))))))
        (fun ld vd => vd = visibleDb ∧
          ∀ row, row ∈ ld ↔
            selectAllLogBody_doneContrib q visibleDb (done ++ [head]) row) := by
  -- We use `headRow.visible = head` to lift head's lookups to `rowFieldInt? headRow`.
  have hHeadRowLo : rowFieldInt? headRow loField = some lo := by
    rw [rowFieldInt?_eq_some_iff_lookup, hHeadVis]; exact hHeadLo
  have hHeadRowHi : rowFieldInt? headRow hiField = some hi := by
    rw [rowFieldInt?_eq_some_iff_lookup, hHeadVis]; exact hHeadHi
  have hHeadRowKey : headRow.key? = some (archiveTable, nKey) := by
    show headRow.visible.key? = _
    rw [hHeadVis]; exact hHeadKey'
  intro rangeDone rangeRest hSplit
  induction rangeRest generalizing rangeDone with
  | nil =>
      -- rangeDone = intRangeRecords "id" lo hi.
      have hRangeDoneEq : rangeDone = Expr.intRangeRecords "id" lo hi := by
        simpa using hSplit
      subst hRangeDoneEq
      refine Logic.localValid_foreachDone (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?_ ?_
      · intro _ _ _ _ hR; exact False.elim hR
      · intro ld vd hPre
        rcases hPre with ⟨hVd, hLdMem⟩
        refine ⟨hVd, ?_⟩
        intro row
        rw [hLdMem row]
        unfold selectAllLogBody_doneContrib
        constructor
        · rintro (hDC | hRec)
          · rcases hDC with ⟨rec, hRecMem, srcRow, hSrcMem, hSrcVis, hOut⟩
            exact ⟨rec, List.mem_append_left _ hRecMem, srcRow, hSrcMem, hSrcVis, hOut⟩
          · rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
            -- rec ∈ intRangeRecords "id" lo hi means rec = ⟨[("id", .int (lo+k))]⟩
            -- with k < (hi-lo).toNat. So id = lo+k and lo ≤ id < hi.
            simp [Expr.intRangeRecords, List.mem_map, List.mem_range] at hRecMem
            rcases hRecMem with ⟨k, hkLt, hRecForm⟩
            subst hRecForm
            -- rec.lookup? "id" = some (.int (lo + k))
            have hIdEq : id = lo + (k : Int) := by
              simp [RecordLit.lookup?] at hRecId
              omega
            subst hIdEq
            -- now id = lo + k where k < (hi - lo).toNat.
            have hLeId : lo ≤ lo + (k : Int) := by
              have : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
              omega
            have hIdLt : lo + (k : Int) < hi := by
              -- hkLt may be either `k < (hi - lo).toNat` or `↑k < hi - lo`.
              -- Try to bridge via omega after a cast.
              have hCast : (k : Int) < hi - lo := by exact_mod_cast hkLt
              omega
            -- Build doneContrib (done ++ [head]) row via rec=head, srcRow=headRow,
            -- selectArchiveResultEffect.
            refine ⟨head, List.mem_append_right _ (List.mem_singleton_self _),
                    headRow, hHeadRowMem, hHeadVis, ?_⟩
            right
            refine ⟨lo, hi, lo + (k : Int), ⟨nKey, hHeadRowKey⟩, hHeadRowLo,
                    hHeadRowHi, hLeId, hIdLt, hRowEq⟩
        · rintro ⟨rec, hRecMem, srcRow, hSrcMem, hSrcVis, hOut⟩
          rcases List.mem_append.mp hRecMem with hRecDone | hRecHead
          · -- rec ∈ done: original doneContrib branch.
            left
            exact ⟨rec, hRecDone, srcRow, hSrcMem, hSrcVis, hOut⟩
          · -- rec = head.
            rw [List.mem_singleton] at hRecHead
            subst hRecHead
            -- srcRow.visible = head, so srcRow.key? = head.key? = (archiveTable, nKey).
            have hSrcKey : srcRow.key? = some (archiveTable, nKey) := by
              show srcRow.visible.key? = _
              rw [hSrcVis]; exact hHeadKey'
            rcases hOut with hLog | hArch
            · -- Log subcase contradicts archive head.
              exfalso
              rcases hLog with ⟨_n, ⟨_id, hLogKey⟩, _, _⟩
              rw [hSrcKey] at hLogKey
              simp [logTable, archiveTable] at hLogKey
            · -- Archive subcase: extract n', show ∃ rec ∈ intRangeRecords.
              rcases hArch with ⟨lo', hi', n', ⟨_id, _hKey⟩, hLo', hHi', hLoLeN, hNLtHi, hRowEq⟩
              -- rowFieldInt? srcRow loField = some lo' AND head's lookup gives lo.
              -- Since srcRow.visible = head, rowFieldInt? srcRow loField = some lo. So lo' = lo.
              have hLoMatch : rowFieldInt? srcRow loField = some lo := by
                rw [rowFieldInt?_eq_some_iff_lookup, hSrcVis]; exact hHeadLo
              have hHiMatch : rowFieldInt? srcRow hiField = some hi := by
                rw [rowFieldInt?_eq_some_iff_lookup, hSrcVis]; exact hHeadHi
              rw [hLoMatch] at hLo'
              rw [hHiMatch] at hHi'
              have hLoEq : lo' = lo := (Option.some.inj hLo').symm
              have hHiEq : hi' = hi := (Option.some.inj hHi').symm
              -- Replace lo'/hi' with lo/hi in remaining hypotheses without subst.
              rw [hLoEq] at hLoLeN
              rw [hHiEq] at hNLtHi
              right
              -- Pick offset = n' - lo (which is ≥ 0).
              have hNGeLo : (0 : Int) ≤ n' - lo := by omega
              have hOffsetEq : ((n' - lo).toNat : Int) = n' - lo := Int.toNat_of_nonneg hNGeLo
              -- After simp [Expr.intRangeRecords, List.mem_map, List.mem_range], the
              -- membership predicate becomes `↑a < hi - lo`, so we phrase hOffsetLt
              -- in that simplified form too.
              have hOffsetLt : ((n' - lo).toNat : Int) < hi - lo := by omega
              refine ⟨⟨[(idField, .int (lo + ((n' - lo).toNat : Int)))]⟩, ?_, n', ?_, hRowEq⟩
              · -- membership in intRangeRecords
                simp [Expr.intRangeRecords, List.mem_map, List.mem_range, idField]
                refine ⟨(n' - lo).toNat, hOffsetLt, ?_⟩
                -- Goal: ↑(n' - lo).toNat = max (n' - lo) 0
                rw [Int.toNat_of_nonneg hNGeLo]
                omega
              · -- lookup? "id" = some (.int n')
                simp [RecordLit.lookup?, idField]
                -- Need: lo + ((n' - lo).toNat : Int) = n'. From hOffsetEq.
                omega
  | cons current rest ih =>
      -- foreachNext + seq + insert.
      have hSplit' : (rangeDone ++ [current]) ++ rest = Expr.intRangeRecords "id" lo hi := by
        rw [List.append_assoc]; simpa using hSplit
      -- current ∈ intRangeRecords means current.lookup? "id" = some (.int (lo + k)).
      have hCurrentInRange : current ∈ Expr.intRangeRecords "id" lo hi := by
        rw [← hSplit]
        simp
      have hCurrentForm : ∃ k : Nat, ((k : Int) < hi - lo) ∧
          ⟨[(idField, .int (lo + (k : Int)))]⟩ = current := by
        simp [Expr.intRangeRecords, List.mem_map, List.mem_range, idField] at hCurrentInRange
        exact hCurrentInRange
      rcases hCurrentForm with ⟨k, _hkLt, hCurForm⟩
      have hCurId : current.lookup? "id" = some (.int (lo + (k : Int))) := by
        rw [← hCurForm]
        simp [RecordLit.lookup?, idField]
      apply Logic.localValid_foreachNext (fun _ _ _ => False) (selectTxnId q)
      · intro _ _ _ _ hR; exact False.elim hR
      · -- Body for current + foreachRuntime (rangeDone ++ [current]) rest
        refine Logic.localValid_seq_false (selectTxnId q) _
          (fun ld vd => vd = visibleDb ∧
            ∀ row, row ∈ ld ↔
              (selectAllLogBody_doneContrib q visibleDb done row ∨
                ∃ rec, rec ∈ (rangeDone ++ [current]) ∧ ∃ id : Int,
                  rec.lookup? "id" = some (.int id) ∧
                  row = resultRowLit (selectTxnId q) q id))
          _ _ _ ?_ ?_
        · -- The body Command.subst "rangeDone" ... (Command.subst "num" ... innerBody)
          -- innerBody = Command.subst "done" ... (Command.insert ...)
          -- After push-through, this is Command.insert e where e evaluates to
          -- resultRecord q (lo + k).
          simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
            Expr.substFieldExprs_nil, Expr.subst_lit,
            doneVar, entryVar, rangeDoneVar, rangeElemVar,
            idField, loField, hiField, tableField,
            show ("entry" : VarName) ≠ "num" from by decide,
            show ("entry" : VarName) ≠ "rangeDone" from by decide,
            show ("done" : VarName) ≠ "entry" from by decide,
            show ("done" : VarName) ≠ "rangeDone" from by decide,
            show ("done" : VarName) ≠ "num" from by decide,
            show ("num" : VarName) ≠ "rangeDone" from by decide,
            show ("num" : VarName) ≠ "entry" from by decide,
            show ("rangeDone" : VarName) ≠ "entry" from by decide,
            show ("rangeDone" : VarName) ≠ "done" from by decide,
            show ("rangeDone" : VarName) ≠ "num" from by decide,
            if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
            dite_eq_left_iff, dite_eq_right_iff]
          refine Logic.localValid_insert_false (selectTxnId q) _ _ _ ?_
          intro ld vd record hPre hEval _hFresh
          rcases hPre with ⟨hVd, hLdMem⟩
          subst hVd
          have hRecordEq : record = resultRecord q (lo + (k : Int)) := by
            simp [resultRecordExpr, fieldExpr, Expr.int, Expr.subst, Expr.eval,
              Expr.evalFieldValues, Literal.toValue, hCurId,
              resultRecord, tableField, idField] at hEval
            exact hEval.symm
          subst hRecordEq
          refine ⟨rfl, ?_⟩
          intro row
          constructor
          · intro hRow
            rcases List.mem_append.mp hRow with hLd | hNew
            · rcases (hLdMem row).mp hLd with hDC | hRec
              · left; exact hDC
              · right
                rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
                exact ⟨rec, List.mem_append_left _ hRecMem, id, hRecId, hRowEq⟩
            · rw [List.mem_singleton] at hNew
              subst hNew
              right
              refine ⟨current, List.mem_append_right _ (List.mem_singleton_self _),
                lo + (k : Int), hCurId, ?_⟩
              show Row.fromInsert (selectTxnId q) (resultRecord q (lo + (k : Int))) = _
              rfl
          · rintro (hDC | hRec)
            · exact List.mem_append_left _ ((hLdMem row).mpr (Or.inl hDC))
            · rcases hRec with ⟨rec, hRecMem, id, hRecId, hRowEq⟩
              rcases List.mem_append.mp hRecMem with hRecDone | hRecCur
              · exact List.mem_append_left _
                  ((hLdMem row).mpr (Or.inr ⟨rec, hRecDone, id, hRecId, hRowEq⟩))
              · rw [List.mem_singleton] at hRecCur
                subst hRecCur
                -- rec = current, so id = lo + k (matches hCurId).
                rw [hCurId] at hRecId
                have hIdEq : id = lo + (k : Int) := (ScalarLit.int.inj
                  (Option.some.inj hRecId)).symm
                subst hIdEq
                rw [hRowEq]
                exact List.mem_append_right _ (List.mem_singleton_self _)
        · -- Recurse via ih.
          exact ih (rangeDone ++ [current]) hSplit'

/-- `selectAllLogBody`'s foreach loop invariant under `(done, rest)` parameters
with `done ++ rest = selected`. Lifting from foreach's empty-accumulator
start (done = [], rest = selected) to fully-processed (done = selected,
rest = []) yields the post `transformerPost empty (selectAllLogEffect q)`.

Paper Appendix C FOREACH case (p.46) reified to Lean's `foreachRuntime`
runtime form. -/
private theorem selectAllLogBody_foreach_invariant
    (q : Nat) (visibleDb : Database)
    (hVisInv : logSystemInv visibleDb)
    (selected : SetLit)
    (hSelect : Semantics.collectSelected visibleDb rowVar
        (isStorageEntryExpr rowVar) = some selected) :
    ∀ (done rest : SetLit), done ++ rest = selected →
      Logic.LocalValid (ι := IsolationSpec Database) (fun _ _ _ => False) (selectTxnId q)
        (fun ld vd => vd = visibleDb ∧
          ∀ row, row ∈ ld ↔ selectAllLogBody_doneContrib q visibleDb done row)
        (Command.foreachRuntime (Expr.setLit done) (Expr.setLit rest) doneVar entryVar
          (Command.ite (isLogExpr entryVar)
             (Command.insert (resultRecordExpr q (fieldExpr entryVar idField)))
             (Command.foreach
                (Expr.rangeRows idField
                  (fieldExpr entryVar loField) (fieldExpr entryVar hiField))
                rangeDoneVar rangeElemVar
                (Command.insert
                  (resultRecordExpr q (fieldExpr rangeElemVar idField))))))
        (transformerPost SetLanguage.empty (selectAllLogEffect (selectTxnId q) q)) := by
  intro done rest hSplit
  induction rest generalizing done with
  | nil =>
      -- Base case: rest = [], so done = selected. Apply foreachDone.
      have hDoneSel : done = selected := by simpa using hSplit
      subst hDoneSel
      refine Logic.localValid_foreachDone (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?_ ?_
      · -- stable Pre under False rely (trivial)
        intro _ _ _ _ hR
        exact False.elim hR
      · -- Pre → Post conversion
        intro ld vd hPre
        rcases hPre with ⟨hVd, hLdMem⟩
        rw [hVd]
        -- Goal: transformerPost empty (selectAllLogEffect q) ld visibleDb
        have hWF : wellFormedTableFields visibleDb := by
          rcases hVisInv with ⟨_, _, _, _, hWF⟩
          exact hWF
        intro row
        simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote_empty,
          false_or]
        rw [hLdMem row]
        -- denote(selectAllLogEffect q) at visibleDb row ↔ doneContrib q visibleDb done row
        unfold selectAllLogBody_doneContrib selectAllLogEffect
        rw [SetLanguage.denote_bind]
        constructor
        · -- mp: denote → doneContrib
          rintro ⟨entry, hEntryDenote, hOut⟩
          rw [selectedStorageEntriesSet_denote_iff] at hEntryDenote
          rcases hEntryDenote with ⟨hEntryMem, hTabOr⟩
          -- Build doneContrib with rec = entry.visible, srcRow = entry.
          refine ⟨entry.visible, ?_, entry, hEntryMem, rfl, hOut⟩
          -- Need: entry.visible ∈ done. Via mem_selected_iff_storage_entry.
          refine (mem_selected_iff_storage_entry hSelect hWF entry.visible).mpr ?_
          refine ⟨entry, hEntryMem, ?_, rfl⟩
          rcases hTabOr with hLog | hArch
          · left
            rcases hWF entry hEntryMem with ⟨t, n, hEKey, hETab⟩
            rw [hETab] at hLog
            have : t = logTable := Option.some.inj hLog
            exact ⟨n, this ▸ hEKey⟩
          · right
            rcases hWF entry hEntryMem with ⟨t, n, hEKey, hETab⟩
            rw [hETab] at hArch
            have : t = archiveTable := Option.some.inj hArch
            exact ⟨n, this ▸ hEKey⟩
        · -- mpr: doneContrib → denote
          rintro ⟨rec, hRecMem, srcRow, hSrcMem, hSrcVis, hOut⟩
          refine ⟨srcRow, ?_, hOut⟩
          rw [selectedStorageEntriesSet_denote_iff]
          refine ⟨hSrcMem, ?_⟩
          have hSel' := (mem_selected_iff_storage_entry hSelect hWF rec).mp hRecMem
          rcases hSel' with ⟨row', _hRow'Mem, hKey, hRow'Vis⟩
          have hSrcKeyEqRow' : srcRow.key? = row'.key? := by
            unfold Row.key?
            rw [hSrcVis, ← hRow'Vis]
          rcases hKey with ⟨n, hLog⟩ | ⟨n, hArch⟩
          · left
            have : srcRow.key? = some (logTable, n) := hSrcKeyEqRow'.trans hLog
            exact rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem this
          · right
            have : srcRow.key? = some (archiveTable, n) := hSrcKeyEqRow'.trans hArch
            exact rowFieldInt?_tableField_of_key_wellFormed hWF hSrcMem this
  | cons head tail ih =>
      -- Step case: foreachNext peels off head, recursion handles tail.
      -- head's contribution depends on its table (log vs archive).
      have hSplit' : (done ++ [head]) ++ tail = selected := by
        rw [List.append_assoc]
        simpa using hSplit
      have hWF : wellFormedTableFields visibleDb := by
        rcases hVisInv with ⟨_, _, _, _, hWF⟩
        exact hWF
      -- head ∈ selected (from hSplit, head is in done ++ head :: tail = selected)
      have hHeadInSel : head ∈ selected := by
        rw [← hSplit]
        simp
      -- Bridge: head corresponds to some row in visibleDb with storage key
      have hHeadRow := (mem_selected_iff_storage_entry hSelect hWF head).mp hHeadInSel
      rcases hHeadRow with ⟨headRow, hHeadRowMem, hHeadKey, hHeadVis⟩
      -- Apply localValid_foreachNext
      apply Logic.localValid_foreachNext (fun _ _ _ => False) (selectTxnId q)
      · -- stable Pre under False rely (trivial)
        intro _ _ _ _ hR
        exact False.elim hR
      · -- seq body: <body for head>; foreachRuntime continued
        -- We use localValid_seq_false with intermediate Pre' for (done ++ [head]).
        refine Logic.localValid_seq_false (selectTxnId q) _
          (fun ld vd => vd = visibleDb ∧
            ∀ row, row ∈ ld ↔ selectAllLogBody_doneContrib q visibleDb (done ++ [head]) row)
          _ _ _ ?_ ?_
        · -- Body for head: subst doneVar (lit done) (subst entryVar (lit (record head)) <body>)
          -- Simp the substitutions: doneVar identity, entryVar replaces.
          simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
            Expr.substFieldExprs_nil, Expr.subst_lit,
            doneVar, entryVar, rangeDoneVar, rangeElemVar,
            idField, loField, hiField, tableField,
            show ("entry" : VarName) ≠ "rangeDone" from by decide,
            show ("entry" : VarName) ≠ "num" from by decide,
            show ("done" : VarName) ≠ "entry" from by decide,
            show ("done" : VarName) ≠ "rangeDone" from by decide,
            show ("done" : VarName) ≠ "num" from by decide,
            if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
            dite_eq_left_iff, dite_eq_right_iff]
          -- Case-split on head's key type via hHeadKey
          rcases hHeadKey with ⟨n, hLogKey⟩ | ⟨n, hArchKey⟩
          · -- Log head: head's tableField = logTable, ITE takes true branch
            have hHeadTableLookup : head.lookup? "table" = some (.int logTable) := by
              rw [← hHeadVis]
              exact lookup?_table_of_key_wellFormed hWF hHeadRowMem hLogKey
            have hHeadIdLookup : head.lookup? "id" = some (.int n) := by
              rw [← hHeadVis]
              exact lookup?_id_of_key hLogKey
            have hHeadKey' : head.key? = some (logTable, n) := by
              rw [← hHeadVis]; exact hLogKey
            refine Logic.localValid_ite_false (selectTxnId q) _ _ _ _ _ ?_ ?_
            · intro _hEvalTrue
              refine Logic.localValid_insert_false (selectTxnId q) _ _ _ ?_
              intro ld vd record hPre hEval _hFresh
              rcases hPre with ⟨hVd, hLdMem⟩
              subst hVd
              have hRecordEq : record = resultRecord q n := by
                simp [resultRecordExpr, fieldExpr, Expr.int, Expr.subst, Expr.eval,
                  Expr.evalFieldValues, Literal.toValue, hHeadIdLookup,
                  resultRecord, tableField, idField] at hEval
                exact hEval.symm
              subst hRecordEq
              refine ⟨rfl, ?_⟩
              intro row
              constructor
              · intro hRow
                rcases List.mem_append.mp hRow with hLd | hNew
                · have hDC := (hLdMem row).mp hLd
                  rcases hDC with ⟨rec, hRec, srcRow, hSrcMem, hSrcVis, hOut⟩
                  exact ⟨rec, List.mem_append_left _ hRec, srcRow, hSrcMem, hSrcVis, hOut⟩
                · rw [List.mem_singleton] at hNew
                  subst hNew
                  refine ⟨head, List.mem_append_right _ (List.mem_singleton_self _),
                    headRow, hHeadRowMem, hHeadVis, ?_⟩
                  left
                  refine ⟨n, ⟨n, hLogKey⟩, ?_, rfl⟩
                  exact rowFieldInt?_eq_some_iff_lookup.mpr
                    (by rw [hHeadVis]; exact hHeadIdLookup)
              · rintro ⟨rec, hRec, srcRow, hSrcMem, hSrcVis, hOut⟩
                rcases List.mem_append.mp hRec with hRecDone | hRecHead
                · exact List.mem_append_left _
                    ((hLdMem row).mpr ⟨rec, hRecDone, srcRow, hSrcMem, hSrcVis, hOut⟩)
                · rw [List.mem_singleton] at hRecHead
                  subst hRecHead
                  refine List.mem_append_right _ ?_
                  rcases hOut with hLog | hArch
                  · rcases hLog with ⟨n', _hSrcKey, hSrcId, hRowEq⟩
                    have hSrcIdEq : n' = n := by
                      have hL : rec.lookup? "id" = some (.int n') := by
                        have := rowFieldInt?_eq_some_iff_lookup.mp hSrcId
                        rw [hSrcVis] at this
                        exact this
                      rw [hHeadIdLookup] at hL
                      injection hL with hL
                      exact (ScalarLit.int.inj hL).symm
                    subst hSrcIdEq
                    rw [hRowEq]
                    exact List.mem_singleton_self _
                  · exfalso
                    rcases hArch with ⟨_lo, _hi, _n', ⟨_id, hArchKey⟩, _⟩
                    have hSrcKeyVis : srcRow.key? = some (logTable, n) := by
                      show srcRow.visible.key? = _
                      rw [hSrcVis]; exact hHeadKey'
                    rw [hSrcKeyVis] at hArchKey
                    simp [logTable, archiveTable] at hArchKey
            · -- False branch: contradiction since head's table = logTable
              intro hEvalFalse
              exfalso
              have hEvalTrue : (Expr.subst "done" (Expr.setLit done)
                  (Expr.subst "entry" (Expr.lit (Literal.record head))
                    (isLogExpr "entry"))).eval =
                  some (Value.scalar (.bool true)) := by
                simp [isLogExpr, isTableExpr, eqExpr, fieldExpr, Expr.int,
                  Expr.subst, Expr.eval, Literal.toValue, tableField,
                  hHeadTableLookup]
              rw [hEvalTrue] at hEvalFalse
              cases hEvalFalse
          · -- Archive head: head's tableField = archiveTable, ITE takes false branch.
            have hHeadTableLookup : head.lookup? "table" = some (.int archiveTable) := by
              rw [← hHeadVis]
              exact lookup?_table_of_key_wellFormed hWF hHeadRowMem hArchKey
            have hHeadIdLookup : head.lookup? "id" = some (.int n) := by
              rw [← hHeadVis]
              exact lookup?_id_of_key hArchKey
            have hHeadKey' : head.key? = some (archiveTable, n) := by
              rw [← hHeadVis]; exact hArchKey
            refine Logic.localValid_ite_false (selectTxnId q) _ _ _ _ _ ?_ ?_
            · -- True branch: contradiction since head's table is archive
              intro hEvalTrue
              exfalso
              have hEvalFalse : (Expr.subst "done" (Expr.setLit done)
                  (Expr.subst "entry" (Expr.lit (Literal.record head))
                    (isLogExpr "entry"))).eval =
                  some (Value.scalar (.bool false)) := by
                simp [isLogExpr, isTableExpr, eqExpr, fieldExpr, Expr.int,
                  Expr.subst, Expr.eval, Literal.toValue, tableField,
                  hHeadTableLookup, logTable, archiveTable]
              rw [hEvalFalse] at hEvalTrue
              cases hEvalTrue
            · -- False branch: inner foreach over rangeRows
              intro _hEvalFalse
              -- Clean up the nested dite (False ∨ False) coming from Command.subst's
              -- if-then-else for foreach bound-var checks.
              simp only [or_self, dite_false]
              -- Now the body is Command.foreach (rangeRows ...) "rangeDone" "num"
              --   (Command.subst "done" ... (Command.insert (Expr.subst "entry" ... ...))).
              refine Logic.localValid_foreach (fun _ _ _ => False) (selectTxnId q)
                _ _ _ _ _ _ ?_ ?_
              · -- Stable Pre under False rely.
                intro _ _ _ _ hR; exact False.elim hR
              · -- Body: for any records that rangeRows evaluates to, recurse.
                intro records hSrcEval
                -- After substitutions and Expr.eval/.proj reductions, hSrcEval encodes
                -- head.lookup? "lo" / "hi", their being .int, and the range condition.
                -- We extract lo, hi via case analysis on the bind chain.
                have hSrcEval' :
                    (do
                      let .scalar (.int loVal) ←
                        (Expr.subst "done" (Expr.setLit done)
                          (Expr.subst "entry" (.lit (.record head))
                            (fieldExpr "entry" "lo"))).eval
                        | none
                      let .scalar (.int hiVal) ←
                        (Expr.subst "done" (Expr.setLit done)
                          (Expr.subst "entry" (.lit (.record head))
                            (fieldExpr "entry" "hi"))).eval
                        | none
                      if loVal <= hiVal then
                        pure <| Value.set (Expr.intRangeRecords "id" loVal hiVal)
                      else
                        none) = some (.set records) := by
                  rw [← hSrcEval]; rfl
                -- Compute the inner evals.
                have hLoEvalProj :
                    (Expr.subst "done" (Expr.setLit done)
                      (Expr.subst "entry" (.lit (.record head))
                        (fieldExpr "entry" "lo"))).eval =
                    (head.lookup? "lo").bind fun s => some (Value.scalar s) := by
                  simp [fieldExpr, Expr.subst, Expr.eval, Literal.toValue]
                have hHiEvalProj :
                    (Expr.subst "done" (Expr.setLit done)
                      (Expr.subst "entry" (.lit (.record head))
                        (fieldExpr "entry" "hi"))).eval =
                    (head.lookup? "hi").bind fun s => some (Value.scalar s) := by
                  simp [fieldExpr, Expr.subst, Expr.eval, Literal.toValue]
                rw [hLoEvalProj, hHiEvalProj] at hSrcEval'
                -- Now case on head.lookup? "lo".
                cases hLoLk : head.lookup? "lo" with
                | none =>
                    rw [hLoLk] at hSrcEval'
                    simp at hSrcEval'
                | some loS =>
                    rw [hLoLk] at hSrcEval'
                    cases loS with
                    | bool _ => simp at hSrcEval'
                    | int iLo =>
                        cases hHiLk : head.lookup? "hi" with
                        | none =>
                            rw [hHiLk] at hSrcEval'
                            simp at hSrcEval'
                        | some hiS =>
                            rw [hHiLk] at hSrcEval'
                            cases hiS with
                            | bool _ => simp at hSrcEval'
                            | int iHi =>
                                -- Now: if iLo ≤ iHi then some (.set (intRangeRecords ...)) = some (.set records).
                                by_cases hLeq : iLo ≤ iHi
                                · simp [hLeq] at hSrcEval'
                                  have hHeadLo : head.lookup? "lo" = some (.int iLo) := hLoLk
                                  have hHeadHi : head.lookup? "hi" = some (.int iHi) := hHiLk
                                  -- hSrcEval' : intRangeRecords "id" iLo iHi = records.
                                  have hRecEq : records = Expr.intRangeRecords "id" iLo iHi :=
                                    hSrcEval'.symm
                                  subst hRecEq
                                  refine Logic.localValid_conseq
                                    (P' := fun ld vd => vd = visibleDb ∧
                                      ∀ row, row ∈ ld ↔
                                        (selectAllLogBody_doneContrib q visibleDb done row ∨
                                          ∃ rec, rec ∈ ([] : SetLit) ∧ ∃ id : Int,
                                            rec.lookup? "id" = some (.int id) ∧
                                            row = resultRowLit (selectTxnId q) q id))
                                    (Q' := fun ld vd => vd = visibleDb ∧
                                      ∀ row, row ∈ ld ↔
                                        selectAllLogBody_doneContrib q visibleDb
                                          (done ++ [head]) row)
                                    ?_ ?_ ?_
                                  · intro ld vd hPre
                                    rcases hPre with ⟨hVd, hLdMem⟩
                                    refine ⟨hVd, ?_⟩
                                    intro row
                                    rw [hLdMem row]
                                    constructor
                                    · intro h; exact Or.inl h
                                    · rintro (h | ⟨_, hMem, _⟩)
                                      · exact h
                                      · cases hMem
                                  · exact selectAllLogBody_archive_inner_foreach
                                      q visibleDb done head iLo iHi headRow hHeadRowMem
                                      hHeadVis n hHeadKey' hHeadLo hHeadHi hLeq
                                      [] (Expr.intRangeRecords "id" iLo iHi) (by simp)
                                  · intro ld vd hPost; exact hPost
                                · -- iLo > iHi: if-cond false, so eval returns none, contradicting some.
                                  simp [hLeq] at hSrcEval'
        · -- Recursive call via ih
          exact ih (done ++ [head]) hSplit'

-- `_via_lazy_pure` removed: replaced by direct constructor-only proof of
-- `paperInfer_selectAllLogBody_final` below using
-- `Logic.localValid_select_collectInvariant` (paper-aligned, p.45 strengthened
-- pre `P' = P ∧ y = collectSelected`). The narrow `selectEntryResultEffect_byRecord`
-- doesn't soundly capture `PaperInfer.selectLazy`'s universal-y body effect,
-- so the LocalValid-level paper-aligned approach is used instead.

/-- Constructor-only `paperInfer_selectAllLogBody_final`.

Paper-aligned proof using `Logic.localValid_select_collectInvariant`
(1710.09844v2.pdf p.45: SELECT case's strengthened body precondition
`P' = P ∧ y = {r ∈ Δ|[r/x]e}`). This avoids the universal-y problem of
`PaperInfer.selectLazy` by directly giving the body access to
`hSelect : collectSelected vd ... = some selected`. -/
theorem paperInfer_selectAllLogBody_final (q : Nat) :
    PaperInfer
      (Logic.relyMod (R_select q) (IsolationSpec.snapshot (σ := Database)).exec)
      (selectTxnId q) logSystemInv SetLanguage.empty (selectAllLogBody q)
      (selectAllLogEffect (selectTxnId q) q) := by
  refine PaperInfer.viaLocalValid ?_
  refine Logic.localValid_of_stutterRely ?_ relyMod_snapshot_exec_silent
  unfold selectAllLogBody
  have hInstNop :
      instantiateSymExpr emptySymEnv [rowVar] (isStorageEntryExpr rowVar) =
        isStorageEntryExpr rowVar := by simp [instantiateSymExpr, emptySymEnv]
  refine Logic.localValid_select_collectInvariant
    (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?stable ?body
  case stable =>
    intro _ _ _ _ hR; exact False.elim hR
  case body =>
    intro selected
    simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
      Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr,
      entriesVar, doneVar, entryVar, rangeDoneVar, rangeElemVar, rowVar,
      idField, loField, hiField, tableField,
      show ("entries" : VarName) ≠ "done" from by decide,
      show ("entries" : VarName) ≠ "entry" from by decide,
      show ("entries" : VarName) ≠ "rangeDone" from by decide,
      show ("entries" : VarName) ≠ "num" from by decide,
      show ("entries" : VarName) ≠ "row" from by decide,
      if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
      dite_eq_left_iff, dite_eq_right_iff, or_self, dite_false]
    refine Logic.localValid_foreach (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?_ ?_
    · intro _ _ _ _ hR; exact False.elim hR
    · intro records hEval
      have hRecordsEq : records = selected := by
        simp [Expr.eval, Literal.toValue] at hEval; exact hEval.symm
      subst hRecordsEq
      -- Note: after subst, `selected` is eliminated; `records` remains in scope.
      intro ld vd finalCfg hPre hMulti hSkip
      rcases hPre with ⟨hPreI, hSelect⟩
      have hInv : logSystemInv vd := hPreI.2
      apply selectAllLogBody_foreach_invariant q vd hInv records
        hSelect [] records (List.nil_append _) ld vd finalCfg ?_ hMulti hSkip
      refine ⟨rfl, ?_⟩
      intro row
      constructor
      · intro hRow
        have := (hPreI.1 row).mpr hRow
        simp [SetLanguage.denote_empty] at this
      · rintro ⟨_, hRecMem, _⟩
        cases hRecMem

/-- _final_old: previous version using `viaLocalValid + False rely descent`.
Kept for reference; replaced by the `_via_lazy_pure + conseqF_withInv` chain. -/
private theorem paperInfer_selectAllLogBody_final_old (q : Nat) :
    PaperInfer
      (Logic.relyMod (R_select q) (IsolationSpec.snapshot (σ := Database)).exec)
      (selectTxnId q) logSystemInv SetLanguage.empty (selectAllLogBody q)
      (selectAllLogEffect (selectTxnId q) q) := by
  refine PaperInfer.viaLocalValid ?_
  refine Logic.localValid_of_stutterRely ?_ relyMod_snapshot_exec_silent
  -- Goal: LocalValid (False) (selectTxnId q)
  --   (transformerPre logSystemInv empty) (selectAllLogBody q)
  --   (transformerPost empty (selectAllLogEffect ... q))
  unfold selectAllLogBody
  refine Logic.localValid_select_false_pinVd (selectTxnId q) _ _ entriesVar rowVar _ _ ?_
  intro localDb visibleDb selected hPre _hSelect
  -- Substituted body: foreach (lit (set selected)) doneVar entryVar (ite ...)
  simp only [Command.subst, Expr.subst, Expr.substFieldExprs_cons,
    Expr.substFieldExprs_nil, Expr.subst_lit, Value.subst_toExpr,
    entriesVar, doneVar, entryVar, rangeDoneVar, rangeElemVar, rowVar,
    idField, loField, hiField, tableField,
    show ("entries" : VarName) ≠ "done" from by decide,
    show ("entries" : VarName) ≠ "entry" from by decide,
    show ("entries" : VarName) ≠ "rangeDone" from by decide,
    show ("entries" : VarName) ≠ "num" from by decide,
    show ("entries" : VarName) ≠ "row" from by decide,
    if_true, if_false, ite_eq_left_iff, ite_eq_right_iff,
    dite_eq_left_iff, dite_eq_right_iff, or_self, dite_false]
  -- Convert eval-form foreach to runtime form via `localValid_foreach`.
  refine Logic.localValid_foreach (fun _ _ _ => False) (selectTxnId q) _ _ _ _ _ _ ?_ ?_
  · -- stableBiAssertion under False rely is trivial
    intro _ _ _ _ hR
    exact False.elim hR
  · -- For each records satisfying eval, prove LocalValid for the runtime form
    intro records hEval
    -- records = selected (from eval of `lit (set selected)`)
    have hRecordsEq : records = selected := by
      simp [Expr.eval, Literal.toValue] at hEval
      exact hEval.symm
    subst hRecordsEq
    -- Goal: LocalValid (False) txnId Pre (foreachRuntime [] selected ...) Post.
    -- Paper Appendix C FOREACH case (p.46): loop invariant
    --   ψ(δ, Δ) ⇔ δ = s ∪ y ≫= (λz. F(Δ)) ∪ Fctxt(Δ) ∧ I(Δ)
    -- with y = `done` accumulator, F(Δ) = selectEntryResultEffect q at z.
    --
    -- Under pinVd (vd = visibleDb) and False rely, body executes at visibleDb
    -- throughout. Each iteration runs ITE: log entry → insert one resultRow;
    -- archive entry → inner foreach over rangeRows.
    --
    -- The proof requires:
    -- (a) `selectAllLogBody_foreach_loop_invariant` lemma: by structural
    --     induction on `rest`, using `localValid_foreachDone` (rest = []) and
    --     `localValid_foreachNext` (rest = cons).
    -- (b) Per-iteration body LocalValid: case-split via `localValid_ite_false`
    --     on `isLogExpr rec`. For log, `localValid_insert_false`. For archive,
    --     `localValid_foreach` again for the inner range, then induct over the
    --     rangeRows list.
    -- (c) Row/RecordLit bridge: via `mem_selected_iff_storage_entry` (just
    --     added), `intField?_idField_of_log_row` (existing), and structural
    --     facts about archiveRecord/Row.
    --
    -- Length estimate: ~250 lines fully written out. Each iteration's effect
    -- decomposition (ITE → insert / nested foreach) is the bulk.
    --
    -- Apply the foreach loop invariant with done = [], rest = records (= selected).
    refine Logic.localValid_conseq ?_
      (selectAllLogBody_foreach_invariant q visibleDb hPre.2 records _hSelect
        [] records (List.nil_append _)) ?_
    · -- Pre-conversion: (transformerPre logSystemInv empty ld vd ∧ vd = visibleDb) →
      --                 (vd = visibleDb ∧ ∀ row, row ∈ ld ↔ doneContrib q visibleDb [] row)
      intro ld vd hPre'
      rcases hPre' with ⟨hPre1, hVd⟩
      refine ⟨hVd, ?_⟩
      intro row
      constructor
      · intro hRow
        have : SetLanguage.denote (SetLanguage.Env.ofDatabases [] vd)
            SetLanguage.empty row := (hPre1.1 row).mpr hRow
        simp [SetLanguage.denote_empty] at this
      · rintro ⟨rec, hRec, _⟩
        cases hRec
    · -- Post-conversion: identity.
      intros _ _ hPost
      exact hPost

/-- Commit-stability for the indexed insert effect. -/
theorem insertLogIndexedEffect_qstable_final (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R_insert (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost (logSystemInvAtNext i) R_insert
        (insertLogEffect (insertTxnId i) i)) :=
  txnSnapshotPost_stable_readCommitted (logSystemInvAtNext i) R_insert
    (insertLogEffect (insertTxnId i) i)

theorem archiveLogEffect_qstable_final (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).commit)
      (txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)) :=
  txnSnapshotPost_stable_snapshot logSystemInv R_archive
    (archiveLogEffect (archiveTxnId i) i)

theorem archiveLogIndexedEffect_qstable_final (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).commit)
      (txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        R_archive (archiveLogEffect (archiveTxnId i) i)) :=
  txnSnapshotPost_stable_snapshot (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
    R_archive (archiveLogEffect (archiveTxnId i) i)

theorem selectAllLogEffect_qstable_final (q : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod (R_select q) (IsolationSpec.snapshot (σ := Database)).commit)
      (txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)) :=
  txnSnapshotPost_stable_snapshot logSystemInv (R_select q)
    (selectAllLogEffect (selectTxnId q) q)

/-! ## Generic helpers -/

/-- A key in `localDb.keyDom` comes from some local row whose `key?` matches. -/
theorem mem_keyDom_iff' (db : Database) (key : RowKey) :
    key ∈ db.keyDom ↔ ∃ row, row ∈ db ∧ row.key? = some key := by
  unfold Database.keyDom
  simp [List.mem_filterMap]

/-! ## Insert: local-row key characterization -/

/-- Direct iff for `updateSetExpr`'s denotation, mirroring the closure inside
`updateSetExprWith_sound` without the `Semantics.collectUpdated` detour. -/
theorem updateSetExpr_denote_iff
    (txnId : TxnId) (env : Env) (source : VarName) (updateExpr predicate : Expr)
    (db : Database) (row : Row) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (updateSetExpr txnId env source updateExpr predicate) row ↔
      ∃ mid : Row, mid ∈ db ∧
        Semantics.satisfiesPredicate source
          (instantiateExpr env [source] predicate) mid.visible = some true ∧
        ∃ updated : RecordLit,
          Expr.eval (Semantics.instantiateRecord source mid.visible
            (instantiateExpr env [source] updateExpr)) = some (.record updated) ∧
          row = mid.overwrite txnId updated := by
  classical
  unfold updateSetExpr updateSetExprWith
  simp [SetLanguage.denote, rowPredicateFormula, SetLanguage.SetExpr.bind,
    SetLanguage.SetExpr.globalDb, defaultOutVar]
  constructor
  · rintro ⟨mid, hMidMem, hBody⟩
    refine ⟨mid, ?_, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMidMem
    · by_cases hPred :
        Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate)
          mid.visible = some true
      · simp [hPred, SetLanguage.empty] at hBody
        exact ⟨hPred, hBody⟩
      · simp [hPred, SetLanguage.empty] at hBody
  · rintro ⟨mid, hMidMem, hPred, hBody⟩
    refine ⟨mid, ?_, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMidMem
    · simp [hPred, SetLanguage.empty]
      exact hBody

/-- The local delta of `insertLogBody i` against a snapshot satisfying
`logSystemInvAtNext i` consists of either:
- the inserted log row `logRow txnId i` (with key `(logTable, i)`), or
- a counter overwrite row whose key is `(counterTable, 0)`, with
  `nextField` set to `i + 1`, explicit `tableField = counterTable`, and live. -/
theorem insertLogEffect_local_row
    (txnId : TxnId) (i : Nat) (snapshotDb : Database)
    (hSnap : logSystemInvAtNext i snapshotDb)
    (row : Row)
    (hDenote :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (insertLogEffect txnId i) row) :
    row = logRow txnId (i : Int) ∨
      (row.key? = some (counterTable, 0) ∧
        rowFieldInt? row tableField = some counterTable ∧
        rowFieldInt? row nextField = some ((i : Int) + 1) ∧
        liveRow row) := by
  rcases hSnap with ⟨_cut, hShape, _hResults, hWF⟩
  rcases hShape with ⟨_hCut, _hCounter, hCounterAtZero, _hHaveNext, hStorageLive,
    _hLiveLog, _hArchive, _hIntervals⟩
  unfold insertLogEffect at hDenote
  rw [SetLanguage.denote_union] at hDenote
  rcases hDenote with hInserted | hUpdated
  · -- Inserted log row branch
    left
    have hEval : Expr.eval (instantiateSymExpr emptySymEnv [] (logRecordExpr (.int i))) =
        some (.record (logRecord (i : Int))) := rfl
    have hClosed :
        evalExprInSetEnv emptySymEnv
            ((SetLanguage.Env.ofDatabases [] snapshotDb).bindElem "_row" row)
            (logRecordExpr (.int i)) =
          Expr.eval (instantiateSymExpr emptySymEnv [] (logRecordExpr (.int i))) := rfl
    have hRowEq :=
      (denote_insertedRowSet txnId emptySymEnv (logRecordExpr (.int i)) snapshotDb row
        (logRecord i) hClosed hEval).1 hInserted
    rw [hRowEq]; rfl
  · -- Counter overwrite branch
    right
    rw [updateSetExpr_denote_iff] at hUpdated
    rcases hUpdated with ⟨mid, hMidMem, hPred, _updated, _hEval, hRow⟩
    have hMidTab : rowFieldInt? mid tableField = some counterTable :=
      (satisfiesPredicate_isTableExpr_iff mid counterTable).mp
        (by simpa [isCounterExpr, isTableExpr, instantiateExpr, Expr.subst, rowVar]
            using hPred)
    rcases rowKey?_of_tableField_wellFormed hWF hMidMem hMidTab with ⟨id, hMidKey⟩
    have hMidKeyZero : mid.key? = some (counterTable, 0) :=
      hCounterAtZero mid hMidMem ⟨id, hMidKey⟩
    have hMidIdField : mid.visible.lookup? "id" = some (.int 0) :=
      lookup?_id_of_key hMidKeyZero
    have hMidTableField : mid.visible.lookup? "table" = some (.int counterTable) :=
      lookup?_table_of_key_wellFormed hWF hMidMem hMidKeyZero
    have hMidLive : liveRow mid :=
      hStorageLive mid hMidMem (Or.inl ⟨0, hMidKeyZero⟩)
    -- The `_updated` value comes from evaluating the update expression on `mid.visible`.
    -- It equals `mid.visible.setField nextField (.int (i+1))`.
    have hUpdatedEq : _updated = mid.visible.setField nextField (.int ((i : Int) + 1)) := by
      have hInnerEval : Expr.eval (.int ((i : Int) + 1)) = some (.scalar (.int ((i : Int) + 1))) :=
        rfl
      have hEvalCanonical :
          Expr.eval (Semantics.instantiateRecord rowVar mid.visible
            (instantiateExpr [] [rowVar] (insertCounterUpdateExpr i))) =
          some (.record (mid.visible.setField nextField (.int ((i : Int) + 1)))) := by
        show Expr.eval
          (.withUpdates (.lit (.record mid.visible)) [(nextField, .int ((i : Int) + 1))]) = _
        exact Expr.eval_lit_record_single_update (record := mid.visible) (field := nextField)
          (expr := .int ((i : Int) + 1)) (value := .int ((i : Int) + 1)) hInnerEval
      rw [hEvalCanonical] at _hEval
      exact (Value.record.inj (Option.some.inj _hEval)).symm
    subst hRow
    subst hUpdatedEq
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Key is (counterTable, 0)
      exact Row.overwrite_key?_of_explicit mid txnId
        (mid.visible.setField nextField (.int ((i : Int) + 1)))
        hMidIdField hMidTableField
    · -- tableField = counterTable
      rw [rowFieldInt?_eq_some_iff_lookup]
      unfold tableField
      exact Row.overwrite_lookup?_table_of_explicit mid txnId
        (mid.visible.setField nextField (.int ((i : Int) + 1)))
        hMidTableField
    · -- nextField = i+1
      have hNeId : (nextField : FieldName) ≠ "id" := by unfold nextField; decide
      have hNeTable : (nextField : FieldName) ≠ "table" := by unfold nextField; decide
      have hNeKind : (nextField : FieldName) ≠ "kind" := by unfold nextField; decide
      have hOverwriteLookup :=
        Row.overwrite_lookup?_of_ne mid txnId
          (mid.visible.setField nextField (.int ((i : Int) + 1)))
          (field := nextField) hNeId hNeTable hNeKind
      have hSetFieldNext :
          (mid.visible.setField nextField (.int ((i : Int) + 1))).lookup? nextField =
            some (.int ((i : Int) + 1)) := RecordLit.lookup?_setField
      rw [rowFieldInt?_eq_some_iff_lookup]
      rw [hOverwriteLookup, hSetFieldNext]
    · -- Live: del = false
      show (mid.overwrite txnId _).del = false
      rw [Row.overwrite_del]
      exact hMidLive

/-- The denotation of `insertLogEffect` always contains a counter overwrite row
when the snapshot has a live counter, which it does under
`logSystemInvAtNext i`. -/
theorem insertLogEffect_has_counter_overwrite
    (txnId : TxnId) (i : Nat) (snapshotDb : Database)
    (hSnap : logSystemInvAtNext i snapshotDb) :
    ∃ row : Row,
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (insertLogEffect txnId i) row ∧
      row.key? = some (counterTable, 0) ∧
      rowFieldInt? row nextField = some ((i : Int) + 1) ∧
      liveRow row := by
  rcases hSnap with ⟨_cut, hShape, _hResults, hWF⟩
  rcases hShape with ⟨_hCut, hCounter, hCounterAtZero, _hHaveNext, hStorageLive,
    _hLiveLog, _hArchive, _hIntervals⟩
  rcases hCounter with ⟨mid, hMidMem, hMidLive, hMidKey, _hMidNext⟩
  -- Construct the overwrite row
  let updated := mid.visible.setField nextField (.int ((i : Int) + 1))
  refine ⟨mid.overwrite txnId updated, ?_, ?_, ?_, ?_⟩
  · -- denote
    unfold insertLogEffect
    rw [SetLanguage.denote_union]
    right
    rw [updateSetExpr_denote_iff]
    refine ⟨mid, hMidMem, ?_, updated, ?_, rfl⟩
    · -- predicate matches: tableField = counterTable
      have hMidTab : rowFieldInt? mid tableField = some counterTable :=
        rowFieldInt?_tableField_of_key_wellFormed hWF hMidMem hMidKey
      simpa [isCounterExpr, isTableExpr, instantiateExpr, Expr.subst, rowVar]
        using (satisfiesPredicate_isTableExpr_iff mid counterTable).mpr hMidTab
    · -- update expression evaluates to `updated`
      have hInnerEval :
          Expr.eval (.int ((i : Int) + 1)) = some (.scalar (.int ((i : Int) + 1))) := rfl
      show Expr.eval
        (.withUpdates (.lit (.record mid.visible)) [(nextField, .int ((i : Int) + 1))]) = _
      exact Expr.eval_lit_record_single_update (record := mid.visible) (field := nextField)
        (expr := .int ((i : Int) + 1)) (value := .int ((i : Int) + 1)) hInnerEval
  · -- key
    have hMidIdField : mid.visible.lookup? "id" = some (.int 0) :=
      lookup?_id_of_key hMidKey
    have hMidTableField : mid.visible.lookup? "table" = some (.int counterTable) :=
      lookup?_table_of_key_wellFormed hWF hMidMem hMidKey
    exact Row.overwrite_key?_of_explicit mid txnId updated hMidIdField hMidTableField
  · -- nextField
    have hNeId : (nextField : FieldName) ≠ "id" := by unfold nextField; decide
    have hNeTable : (nextField : FieldName) ≠ "table" := by unfold nextField; decide
    have hNeKind : (nextField : FieldName) ≠ "kind" := by unfold nextField; decide
    have hOverwriteLookup :=
      Row.overwrite_lookup?_of_ne mid txnId updated (field := nextField)
        hNeId hNeTable hNeKind
    have hSetFieldNext : updated.lookup? nextField = some (.int ((i : Int) + 1)) :=
      RecordLit.lookup?_setField
    rw [rowFieldInt?_eq_some_iff_lookup]
    rw [hOverwriteLookup, hSetFieldNext]
  · -- live
    show (mid.overwrite txnId updated).del = false
    rw [Row.overwrite_del]
    exact hMidLive

/-- The denotation of `insertLogEffect` always contains the inserted log row. -/
theorem insertLogEffect_has_log_row
    (txnId : TxnId) (i : Nat) (snapshotDb : Database) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
      (insertLogEffect txnId i) (logRow txnId i) := by
  unfold insertLogEffect
  rw [SetLanguage.denote_union]
  left
  have hEval : Expr.eval (instantiateSymExpr emptySymEnv [] (logRecordExpr (.int i))) =
      some (.record (logRecord (i : Int))) := rfl
  have hClosed :
      evalExprInSetEnv emptySymEnv
          ((SetLanguage.Env.ofDatabases [] snapshotDb).bindElem "_row" (logRow txnId i))
          (logRecordExpr (.int i)) =
        Expr.eval (instantiateSymExpr emptySymEnv [] (logRecordExpr (.int i))) := rfl
  exact (denote_insertedRowSet txnId emptySymEnv (logRecordExpr (.int i)) snapshotDb
    (logRow txnId i) (logRecord i) hClosed hEval).2 rfl

/-! ## Insert: storage-table no-clobber lemmas -/

/-- Local rows of insert have keys disjoint from the archive table. -/
theorem insertLogEffect_local_no_archive_key
    (txnId : TxnId) (i : Nat) (snapshotDb localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost (logSystemInvAtNext i) R_insert
        (insertLogEffect txnId i) localDb visibleDb)
    {row : Row} {id : Int} (hMem : row ∈ localDb)
    (hKey : row.key? = some (archiveTable, id)) : False := by
  rcases hPost with ⟨snapshotDb', hSnap, _hReach, hRows⟩
  have hDenote := (hRows row).2 hMem
  rcases insertLogEffect_local_row txnId i snapshotDb' hSnap row hDenote with hLog | hCounter
  · subst hLog
    rw [logRow_key?] at hKey
    have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
    exact logTable_ne_archiveTable this
  · rw [hCounter.1] at hKey
    have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
    exact counterTable_ne_archiveTable this

/-- Local rows of insert have keys disjoint from any result table. -/
theorem insertLogEffect_local_no_result_key
    (txnId : TxnId) (i : Nat) (snapshotDb localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost (logSystemInvAtNext i) R_insert
        (insertLogEffect txnId i) localDb visibleDb)
    {row : Row} {q : Nat} {n : Int} (hMem : row ∈ localDb)
    (hKey : row.key? = some (resultTable q, n)) : False := by
  rcases hPost with ⟨snapshotDb', hSnap, _hReach, hRows⟩
  have hDenote := (hRows row).2 hMem
  rcases insertLogEffect_local_row txnId i snapshotDb' hSnap row hDenote with hLog | hCounter
  · subst hLog
    rw [logRow_key?] at hKey
    have : logTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
    exact resultTable_ne_logTable q this.symm
  · rw [hCounter.1] at hKey
    have : counterTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
    exact resultTable_ne_counterTable q this.symm

/-- Indexed insert guarantee bridge. -/
theorem insertLogIndexedEffect_guarantee_final (i : Nat) :
    ∀ localDb visibleDb,
      txnSnapshotPost (logSystemInvAtNext i) R_insert
          (insertLogEffect (insertTxnId i) i) localDb visibleDb →
        G_insert visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hPost
  -- Snapshot info
  rcases hPost with ⟨snapshotDb, hSnap, hReach, hRows⟩
  -- Visible satisfies logSystemInvAtNext i by stability under R_insert
  have hVisAtNext : logSystemInvAtNext i visibleDb :=
    stableAssertion_multiStep (logSystemInvAtNext_stable_R_insert i) hReach hSnap
  rcases hVisAtNext with ⟨cut, hVisShape, hVisResults, hVisWF⟩
  rcases hVisShape with ⟨hCutLe, hVisCounter, hVisCounterAtZero, hVisHaveNext,
    hVisStorageLive, hVisLiveLog, hVisArchive, hVisIntervals⟩
  -- Snapshot has logSystemInvAtNext i
  have hPostBack : txnSnapshotPost (logSystemInvAtNext i) R_insert
      (insertLogEffect (insertTxnId i) i) localDb visibleDb :=
    ⟨snapshotDb, hSnap, hReach, hRows⟩
  -- Local row characterization helper
  have hLocalRow : ∀ row, row ∈ localDb →
      row = logRow (insertTxnId i) (i : Int) ∨
        (row.key? = some (counterTable, 0) ∧
          rowFieldInt? row tableField = some counterTable ∧
          rowFieldInt? row nextField = some ((i : Int) + 1) ∧
          liveRow row) := by
    intro row hMem
    exact insertLogEffect_local_row (insertTxnId i) i snapshotDb hSnap row ((hRows row).2 hMem)
  -- Local has the inserted log row
  have hLocalHasLog : logRow (insertTxnId i) (i : Int) ∈ localDb :=
    (hRows (logRow (insertTxnId i) (i : Int))).1
      (insertLogEffect_has_log_row (insertTxnId i) i snapshotDb)
  -- Local has at least one counter overwrite
  have hLocalHasCounter : ∃ row : Row, row ∈ localDb ∧
      row.key? = some (counterTable, 0) ∧
      rowFieldInt? row nextField = some ((i : Int) + 1) ∧
      liveRow row := by
    rcases insertLogEffect_has_counter_overwrite (insertTxnId i) i snapshotDb hSnap with
      ⟨row, hRowDenote, hRowKey, hRowNext, hRowLive⟩
    exact ⟨row, (hRows row).1 hRowDenote, hRowKey, hRowNext, hRowLive⟩
  -- For convenience, abbreviate the local key set
  -- The constructor for G_insertCore: cut, next = i.
  refine ⟨cut, i, ?_, ?_, ?_, ?_, ?_⟩
  · -- storageShape visibleDb cut i
    exact ⟨hCutLe, hVisCounter, hVisCounterAtZero, hVisHaveNext, hVisStorageLive,
      hVisLiveLog, hVisArchive, hVisIntervals⟩
  · -- storageShape (flush) cut (i+1)
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- liveCounterAt (flush) (i+1)
      rcases hLocalHasCounter with ⟨counterRow, hCounterMem, hCounterKey, hCounterNext, hCounterLive⟩
      refine ⟨counterRow, ?_, hCounterLive, hCounterKey, hCounterNext⟩
      rw [mem_flush_iff]; exact Or.inr ⟨hCounterMem, hCounterLive⟩
    · -- counterRowsAtZero (flush)
      intro row hMem hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisCounterAtZero row hG.1 hInTable
      · rcases hLocalRow row hL.1 with hLogR | hCounterR
        · exfalso
          subst hLogR
          rcases hInTable with ⟨id, hKey⟩
          rw [logRow_key?] at hKey
          have : logTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_logTable this.symm
        · exact hCounterR.1
    · -- liveCountersHaveNext (flush) (i+1)
      intro row hMem hLive hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exfalso
        have hKey : row.key? = some (counterTable, 0) := hVisCounterAtZero row hG.1 hInTable
        have hLocalCounterKey : (counterTable, (0 : Int)) ∈ localDb.keyDom := by
          rw [mem_keyDom_iff']
          rcases hLocalHasCounter with ⟨cRow, hcM, hcK, _, _⟩
          exact ⟨cRow, hcM, hcK⟩
        have hNoClobber := hG.2
        rw [hKey] at hNoClobber
        exact hNoClobber hLocalCounterKey
      · rcases hLocalRow row hL.1 with hLogR | hCounterR
        · exfalso
          subst hLogR
          rcases hInTable with ⟨id, hKey⟩
          rw [logRow_key?] at hKey
          have : logTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_logTable this.symm
        · exact hCounterR.2.2.1
    · -- storageRowsLive (flush)
      intro row hMem hStorage
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisStorageLive row hG.1 hStorage
      · rcases hLocalRow row hL.1 with hLogR | hCounterR
        · subst hLogR
          show (logRow (insertTxnId i) (i : Int)).del = false
          simp [logRow, Row.fromInsert]
        · exact hCounterR.2.2.2
    · -- liveLog (flush) n iff cut ≤ n < i+1
      intro n
      constructor
      · intro hL
        rcases liveLog_of_flush hL with hVis | hLoc
        · -- visible has it: cut ≤ n < i, so cut ≤ n < i+1
          have := (hVisLiveLog n).1 hVis
          omega
        · -- local has it: must be the inserted log row at i
          rcases hLoc with ⟨row, hMem, _hLive, hKey⟩
          rcases hLocalRow row hMem with hLogR | hCounterR
          · subst hLogR
            rw [logRow_key?] at hKey
            have hN : (i : Int) = (n : Int) := (Prod.mk.inj (Option.some.inj hKey)).2
            have : i = n := by exact_mod_cast hN
            subst this
            exact ⟨hCutLe, by omega⟩
          · exfalso
            rw [hCounterR.1] at hKey
            have : counterTable = logTable := (Prod.mk.inj (Option.some.inj hKey)).1
            exact counterTable_ne_logTable this
      · rintro ⟨hCut, hLt⟩
        by_cases hN : n = i
        · -- Use the local log row
          subst hN
          refine ⟨logRow (insertTxnId n) (n : Int), ?_, ?_, ?_⟩
          · rw [mem_flush_iff]
            refine Or.inr ⟨hLocalHasLog, ?_⟩
            simp [logRow, Row.fromInsert]
          · simp [logRow, Row.fromInsert, liveRow]
          · exact logRow_key? (insertTxnId n) (n : Int)
        · -- Use a visible log row
          have hVisLog : liveLog visibleDb n := (hVisLiveLog n).2 ⟨hCut, by omega⟩
          rcases hVisLog with ⟨row, hMem, hLive, hKey⟩
          refine ⟨row, ?_, hLive, hKey⟩
          rw [mem_flush_iff]
          refine Or.inl ⟨hMem, ?_⟩
          rw [hKey]
          intro hLocal
          rw [mem_keyDom_iff'] at hLocal
          rcases hLocal with ⟨row', hMem', hKey'⟩
          rcases hLocalRow row' hMem' with hLogR | hCounterR
          · subst hLogR
            rw [logRow_key?] at hKey'
            have hEq : (i : Int) = (n : Int) := (Prod.mk.inj (Option.some.inj hKey')).2
            have : i = n := by exact_mod_cast hEq
            exact hN this.symm
          · rw [hCounterR.1] at hKey'
            have : counterTable = logTable := (Prod.mk.inj (Option.some.inj hKey')).1
            exact counterTable_ne_logTable this
    · -- archiveCovers (flush) n iff n < cut
      intro n
      constructor
      · intro hC
        rcases archiveCovers_of_flush hC with hVis | hLoc
        · exact (hVisArchive n).1 hVis
        · -- local rows have key (logTable, i) or (counterTable, 0), not archive
          exfalso
          rcases hLoc with ⟨row, _id, _lo, _hi, hMem, _hLive, hKey, _, _, _, _⟩
          rcases hLocalRow row hMem with hLogR | hCounterR
          · subst hLogR
            rw [logRow_key?] at hKey
            have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
            exact logTable_ne_archiveTable this
          · rw [hCounterR.1] at hKey
            have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
            exact counterTable_ne_archiveTable this
      · intro hN
        have hVisArch : archiveCovers visibleDb n := (hVisArchive n).2 hN
        apply archiveCovers_flush_of_global _ hVisArch
        intro idx hLocal
        rw [mem_keyDom_iff'] at hLocal
        rcases hLocal with ⟨row, hMem, hKey⟩
        rcases hLocalRow row hMem with hLogR | hCounterR
        · subst hLogR
          rw [logRow_key?] at hKey
          have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact logTable_ne_archiveTable this
        · rw [hCounterR.1] at hKey
          have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_archiveTable this
    · -- archiveIntervalsWellFormed (flush)
      intro row idx lo hi hMem hLive hKey hLo hHi
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisIntervals row idx lo hi hG.1 hLive hKey hLo hHi
      · exfalso
        rcases hLocalRow row hL.1 with hLogR | hCounterR
        · subst hLogR
          rw [logRow_key?] at hKey
          have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact logTable_ne_archiveTable this
        · rw [hCounterR.1] at hKey
          have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_archiveTable this
  · -- sameResultRows
    intro q n
    constructor
    · intro hNew
      rcases resultRowFor_of_flush hNew with hOld | hLoc
      · exact hOld
      · exfalso
        rcases hLoc with ⟨row, hMem, _hLive, hKey⟩
        exact insertLogEffect_local_no_result_key (insertTxnId i) i snapshotDb localDb visibleDb
          ⟨snapshotDb, hSnap, hReach, hRows⟩ hMem hKey
    · intro hOld
      apply resultRowFor_flush_of_global _ hOld
      intro hLocal
      rw [mem_keyDom_iff'] at hLocal
      rcases hLocal with ⟨row, hMem, hKey⟩
      exact insertLogEffect_local_no_result_key (insertTxnId i) i snapshotDb localDb visibleDb
        ⟨snapshotDb, hSnap, hReach, hRows⟩ hMem hKey
  · -- preservesArchiveKeyFreshness
    intro idx hOldFresh row hMemNew hKey
    rw [mem_flush_iff] at hMemNew
    rcases hMemNew with hG | hL
    · exact hOldFresh row hG.1 hKey
    · exact insertLogEffect_local_no_archive_key (insertTxnId i) i snapshotDb localDb visibleDb
        ⟨snapshotDb, hSnap, hReach, hRows⟩ hL.1 hKey
  · -- preservesWellFormedTableFields
    intro hOldWF row hMem
    rw [mem_flush_iff] at hMem
    rcases hMem with hG | hL
    · exact hOldWF row hG.1
    · rcases hLocalRow row hL.1 with hLogR | hCounterR
      · subst hLogR
        exact ⟨logTable, i, logRow_key? (insertTxnId i) (i : Int),
          rowFieldInt?_logRow_table (insertTxnId i) (i : Int)⟩
      · exact ⟨counterTable, 0, hCounterR.1, hCounterR.2.1⟩

/-! ## Constructive min/max for the set of log keys in a finite database -/

private theorem selectedLogMin_exists :
    ∀ (db : Database) (witRow : Row) (witN : Int),
      witRow ∈ db → witRow.key? = some (logTable, witN) →
      ∃ lo, (∃ row, row ∈ db ∧ row.key? = some (logTable, lo)) ∧
        ∀ row' n', row' ∈ db → row'.key? = some (logTable, n') → lo ≤ n' := by
  intro db
  induction db with
  | nil =>
      intro witRow _witN hMem _
      cases hMem
  | cons head tail ih =>
      intro witRow witN hMem hKey
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst hHead
        by_cases hTailLog : ∃ row n, row ∈ tail ∧ row.key? = some (logTable, n)
        · rcases hTailLog with ⟨tw, tn, tMem, tKey⟩
          rcases ih tw tn tMem tKey with ⟨tailLo, ⟨tailRow, tailMem, tailKey⟩, tailMin⟩
          by_cases hCmp : witN ≤ tailLo
          · refine ⟨witN, ⟨witRow, List.mem_cons_self, hKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'
              rw [hKey] at hKey'
              have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
              omega
            · have := tailMin row' n' hTail' hKey'
              omega
          · refine ⟨tailLo, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'
              rw [hKey] at hKey'
              have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
              omega
            · exact tailMin row' n' hTail' hKey'
        · refine ⟨witN, ⟨witRow, List.mem_cons_self, hKey⟩, ?_⟩
          intro row' n' hMem' hKey'
          rcases List.mem_cons.mp hMem' with hHead' | hTail'
          · subst hHead'
            rw [hKey] at hKey'
            have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
            omega
          · exact absurd ⟨row', n', hTail', hKey'⟩ hTailLog
      · rcases ih witRow witN hTail hKey with ⟨tailLo, ⟨tailRow, tailMem, tailKey⟩, tailMin⟩
        cases hHeadKey : head.key? with
        | none =>
            refine ⟨tailLo, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'; rw [hHeadKey] at hKey'; cases hKey'
            · exact tailMin row' n' hTail' hKey'
        | some key =>
            rcases key with ⟨table, k⟩
            by_cases hLogTable : table = logTable
            · subst hLogTable
              by_cases hCmp : k ≤ tailLo
              · refine ⟨k, ⟨head, List.mem_cons_self, hHeadKey⟩, ?_⟩
                intro row' n' hMem' hKey'
                rcases List.mem_cons.mp hMem' with hHead' | hTail'
                · subst hHead'
                  rw [hHeadKey] at hKey'
                  have : k = n' := (Prod.mk.inj (Option.some.inj hKey')).2
                  omega
                · have := tailMin row' n' hTail' hKey'
                  omega
              · refine ⟨tailLo, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
                intro row' n' hMem' hKey'
                rcases List.mem_cons.mp hMem' with hHead' | hTail'
                · subst hHead'
                  rw [hHeadKey] at hKey'
                  have : k = n' := (Prod.mk.inj (Option.some.inj hKey')).2
                  omega
                · exact tailMin row' n' hTail' hKey'
            · refine ⟨tailLo, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
              intro row' n' hMem' hKey'
              rcases List.mem_cons.mp hMem' with hHead' | hTail'
              · subst hHead'
                rw [hHeadKey] at hKey'
                have hT : table = logTable := (Prod.mk.inj (Option.some.inj hKey')).1
                exact absurd hT hLogTable
              · exact tailMin row' n' hTail' hKey'

private theorem selectedLogMax_exists :
    ∀ (db : Database) (witRow : Row) (witN : Int),
      witRow ∈ db → witRow.key? = some (logTable, witN) →
      ∃ hi, (∃ row, row ∈ db ∧ row.key? = some (logTable, hi)) ∧
        ∀ row' n', row' ∈ db → row'.key? = some (logTable, n') → n' ≤ hi := by
  intro db
  induction db with
  | nil =>
      intro witRow _witN hMem _
      cases hMem
  | cons head tail ih =>
      intro witRow witN hMem hKey
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst hHead
        by_cases hTailLog : ∃ row n, row ∈ tail ∧ row.key? = some (logTable, n)
        · rcases hTailLog with ⟨tw, tn, tMem, tKey⟩
          rcases ih tw tn tMem tKey with ⟨tailHi, ⟨tailRow, tailMem, tailKey⟩, tailMax⟩
          by_cases hCmp : tailHi ≤ witN
          · refine ⟨witN, ⟨witRow, List.mem_cons_self, hKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'
              rw [hKey] at hKey'
              have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
              omega
            · have := tailMax row' n' hTail' hKey'
              omega
          · refine ⟨tailHi, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'
              rw [hKey] at hKey'
              have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
              omega
            · exact tailMax row' n' hTail' hKey'
        · refine ⟨witN, ⟨witRow, List.mem_cons_self, hKey⟩, ?_⟩
          intro row' n' hMem' hKey'
          rcases List.mem_cons.mp hMem' with hHead' | hTail'
          · subst hHead'
            rw [hKey] at hKey'
            have : witN = n' := (Prod.mk.inj (Option.some.inj hKey')).2
            omega
          · exact absurd ⟨row', n', hTail', hKey'⟩ hTailLog
      · rcases ih witRow witN hTail hKey with ⟨tailHi, ⟨tailRow, tailMem, tailKey⟩, tailMax⟩
        cases hHeadKey : head.key? with
        | none =>
            refine ⟨tailHi, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
            intro row' n' hMem' hKey'
            rcases List.mem_cons.mp hMem' with hHead' | hTail'
            · subst hHead'; rw [hHeadKey] at hKey'; cases hKey'
            · exact tailMax row' n' hTail' hKey'
        | some key =>
            rcases key with ⟨table, k⟩
            by_cases hLogTable : table = logTable
            · subst hLogTable
              by_cases hCmp : tailHi ≤ k
              · refine ⟨k, ⟨head, List.mem_cons_self, hHeadKey⟩, ?_⟩
                intro row' n' hMem' hKey'
                rcases List.mem_cons.mp hMem' with hHead' | hTail'
                · subst hHead'
                  rw [hHeadKey] at hKey'
                  have : k = n' := (Prod.mk.inj (Option.some.inj hKey')).2
                  omega
                · have := tailMax row' n' hTail' hKey'
                  omega
              · refine ⟨tailHi, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
                intro row' n' hMem' hKey'
                rcases List.mem_cons.mp hMem' with hHead' | hTail'
                · subst hHead'
                  rw [hHeadKey] at hKey'
                  have : k = n' := (Prod.mk.inj (Option.some.inj hKey')).2
                  omega
                · exact tailMax row' n' hTail' hKey'
            · refine ⟨tailHi, ⟨tailRow, List.mem_cons_of_mem _ tailMem, tailKey⟩, ?_⟩
              intro row' n' hMem' hKey'
              rcases List.mem_cons.mp hMem' with hHead' | hTail'
              · subst hHead'
                rw [hHeadKey] at hKey'
                have hT : table = logTable := (Prod.mk.inj (Option.some.inj hKey')).1
                exact absurd hT hLogTable
              · exact tailMax row' n' hTail' hKey'

/-- A local row with `(logTable, n)` key in archive's effect denotation comes
from a snap log row at the same key (a delete marker, since archive insert
rows have key `(archiveTable, i)`). -/
theorem archiveLogSnapshotPost_local_logKey_implies_snap_log
    (i : Nat) (snapshotDb : Database)
    (hSnapInv : logSystemInv snapshotDb)
    {row : Row} {n : Int}
    (hDenote :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (archiveLogEffect (archiveTxnId i) i) row)
    (hKey : row.key? = some (logTable, n)) :
    ∃ src, src ∈ snapshotDb ∧ liveRow src ∧ src.key? = some (logTable, n) := by
  unfold archiveLogEffect at hDenote
  rw [SetLanguage.denote_union] at hDenote
  rcases hDenote with hInsert | hDelete
  · -- archive insert: row has (archiveTable, i) key, contradicting (logTable, n)
    exfalso
    rcases hInsert with ⟨lo', hi0', _, _, hRow⟩
    subst hRow
    rw [archiveRow_key?] at hKey
    have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hKey)).1
    exact logTable_ne_archiveTable this.symm
  · -- delete marker: row = src.markDeleted, src has logTable key
    rcases hDelete with ⟨src, n', _, _, _, _, hSel, _, _, hRow⟩
    subst hRow
    rcases hSel with ⟨hSrcMem, hSrcKey⟩
    -- markDeleted preserves key
    rw [markDeleted_key?] at hKey
    rw [hSrcKey] at hKey
    have hPair : (logTable, n') = (logTable, n) := Option.some.inj hKey
    have hN'Eq : n' = n := (Prod.mk.inj hPair).2
    rw [hN'Eq] at hSrcKey
    -- src is live by snap's storageRowsLive (since src has logTable key)
    rcases hSnapInv with ⟨_, _, hShape, _, _⟩
    rcases hShape with ⟨_, _, _, _, hStorageLive, _, _, _⟩
    have hLive : liveRow src :=
      hStorageLive src hSrcMem (Or.inr (Or.inl ⟨n, hSrcKey⟩))
    exact ⟨src, hSrcMem, hLive, hSrcKey⟩

/-- Converse of `archiveLogSnapshotPost_local_logKey_implies_snap_log`:
if snap has a live log row at `n`, the archive's local delta has a delete
marker at the same key. -/
private theorem archiveLogEffect_local_has_logKey
    (i : Nat) (snapshotDb : Database) {snapCut snapNext : Nat}
    (hSnapShape : storageShape snapshotDb snapCut snapNext)
    (localDb : Database)
    (hRows : ∀ row,
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (archiveLogEffect (archiveTxnId i) i) row ↔ row ∈ localDb)
    {n : Nat} (hLow : snapCut ≤ n) (hHigh : n < snapNext) :
    (logTable, (n : Int)) ∈ localDb.keyDom := by
  rcases hSnapShape with ⟨_, _, _, _, _, hSnapLiveLog, _, _⟩
  rcases (hSnapLiveLog n).2 ⟨hLow, hHigh⟩ with ⟨src, hSrcMem, _hSrcLive, hSrcKey⟩
  rcases selectedLogMin_exists snapshotDb src n hSrcMem hSrcKey with
    ⟨lo, ⟨witLo, hLoMem, hLoKey⟩, hLoMin⟩
  rcases selectedLogMax_exists snapshotDb src n hSrcMem hSrcKey with
    ⟨hi, ⟨witHi, hHiMem, hHiKey⟩, hHiMax⟩
  let archRow : Row := src.markDeleted (archiveTxnId i)
  have hDenote :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
        (archiveLogEffect (archiveTxnId i) i) archRow := by
    unfold archiveLogEffect
    rw [SetLanguage.denote_union]
    refine Or.inr ?_
    refine ⟨src, (n : Int), lo, hi, ?_, ?_, ⟨hSrcMem, hSrcKey⟩, ?_, ?_, rfl⟩
    · refine ⟨⟨witLo, hLoMem, hLoKey⟩, ?_⟩
      intro row' n' hSel'
      exact hLoMin row' n' hSel'.1 hSel'.2
    · refine ⟨⟨witHi, hHiMem, hHiKey⟩, ?_⟩
      intro row' n' hSel'
      exact hHiMax row' n' hSel'.1 hSel'.2
    · exact hLoMin src n hSrcMem hSrcKey
    · exact hHiMax src n hSrcMem hSrcKey
  have hLocalMem : archRow ∈ localDb := (hRows archRow).1 hDenote
  have hKey : archRow.key? = some (logTable, (n : Int)) := by
    show (src.markDeleted (archiveTxnId i)).key? = _
    rw [markDeleted_key?]
    exact hSrcKey
  rw [mem_keyDom_iff']
  exact ⟨archRow, hLocalMem, hKey⟩

/-- Visible's freshness from the indexed snapshot post via stability under
`R_archive`. -/
theorem archiveKeysFreshFrom_visible_of_indexedSnapshotPost
    (i : Nat) (localDb visibleDb : Database)
    (hPost : txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        R_archive (archiveLogEffect (archiveTxnId i) i) localDb visibleDb) :
    archiveKeysFreshFrom i visibleDb := by
  rcases hPost with ⟨snapshotDb, ⟨hSnapInv, hSnapFresh⟩, hReach, _hRows⟩
  -- Stability of (logSystemInv ∧ archiveKeysFreshFrom i) under R_archive
  have hStable : Logic.stableAssertion R_archive
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) :=
    archiveIndexedInv_stable_R_archive i
  have : (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) visibleDb := by
    induction hReach with
    | refl => exact ⟨hSnapInv, hSnapFresh⟩
    | tail _hPrev hLast ih => exact hStable _ _ ih hLast
  exact this.2

/-- Indexed archive guarantee bridge.

The snapshot post is now over the strengthened invariant
`logSystemInv ∧ archiveKeysFreshFrom i`, which gives:
- the snapshot's storage shape and frontier;
- archive-id `i`'s freshness in the snapshot, which propagates to the
  visible database by `archiveIndexedInv_stable_R_archive`.

These together let us conclude that the local archive insert at
`(archiveTable, i)` purely extends archive coverage from `[0, vis.cut)`
to `[0, snap.next)`, without any clobber-induced shape distortion. -/
theorem archiveLogIndexedEffect_guarantee_final (i : Nat) :
    ∀ localDb visibleDb,
      txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
          R_archive (archiveLogEffect (archiveTxnId i) i) localDb visibleDb →
        G_archive visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hPost
  -- Snapshot info
  rcases hPost with ⟨snapshotDb, hSnapBoth, hReach, hRows⟩
  have hSnapLogInvFull : logSystemInv snapshotDb := hSnapBoth.1
  have hSnapFresh : archiveKeysFreshFrom i snapshotDb := hSnapBoth.2
  rcases hSnapLogInvFull with ⟨snapCut, snapNext, hSnapShape, hSnapResults, hSnapWF⟩
  have hSnapLogInv : logSystemInv snapshotDb :=
    ⟨snapCut, snapNext, hSnapShape, hSnapResults, hSnapWF⟩
  -- Visible's storage shape via stability lemma
  rcases R_archive_multiStep_storageShape hReach hSnapLogInv hSnapShape with
    ⟨visNext, hSnapNextLeVis, hVisShape⟩
  have hVisLogInv : logSystemInv visibleDb :=
    logSystemInv_stable_multiStep logSystemInv_stable_R_archive hReach hSnapLogInv
  -- Visible has archive-id freshness
  have hVisFresh : archiveKeysFreshFrom i visibleDb :=
    archiveKeysFreshFrom_visible_of_indexedSnapshotPost i localDb visibleDb
      ⟨snapshotDb, ⟨hSnapLogInv, hSnapFresh⟩, hReach, hRows⟩
  -- Local row characterization (weaken to logSystemInv-only snapshot post first)
  have hPostStrong :
      txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        R_archive (archiveLogEffect (archiveTxnId i) i) localDb visibleDb :=
    ⟨snapshotDb, ⟨hSnapLogInv, hSnapFresh⟩, hReach, hRows⟩
  have hPostWeak : txnSnapshotPost logSystemInv R_archive
      (archiveLogEffect (archiveTxnId i) i) localDb visibleDb :=
    txnSnapshotPost_weaken
      (I := fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      (I' := logSystemInv)
      (fun _ h => h.1) hPostStrong
  have hLocalRowKey := archiveLogSnapshotPost_local_row_key i localDb visibleDb hPostWeak
  -- Useful: visible storage shape components
  rcases hVisShape with ⟨_hVisCutLe, hVisCounter, hVisCounterAtZero, hVisHaveNext,
    hVisStorageLive, hVisLiveLog, hVisArchive, hVisIntervals⟩
  have hVisShapeFull : storageShape visibleDb snapCut visNext :=
    ⟨_hVisCutLe, hVisCounter, hVisCounterAtZero, hVisHaveNext, hVisStorageLive,
      hVisLiveLog, hVisArchive, hVisIntervals⟩
  -- Local has no counter rows: hLocalRowKey gives archiveTable or logTable key.
  have hLocalNoCounterKey : ∀ id : Int, (counterTable, id) ∉ localDb.keyDom := by
    intro id hLocal
    rw [mem_keyDom_iff'] at hLocal
    rcases hLocal with ⟨row, hMem, hKey⟩
    rcases hLocalRowKey row hMem with hArch | ⟨_n, hLog⟩
    · rw [hArch] at hKey
      have : archiveTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
      exact counterTable_ne_archiveTable this.symm
    · rw [hLog] at hKey
      have : logTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
      exact counterTable_ne_logTable this.symm
  -- Provide G_archiveCore
  refine ⟨snapCut, snapNext, visNext, hVisShapeFull, hSnapShape.1, hSnapNextLeVis, ?_, ?_, ?_⟩
  · -- storageShape (flush) snapNext visNext
    refine ⟨hSnapNextLeVis, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- liveCounterAt (flush) visNext
      rcases hVisCounter with ⟨row, hMem, hLive, hKey, hNext⟩
      refine ⟨row, ?_, hLive, hKey, hNext⟩
      rw [mem_flush_iff]
      refine Or.inl ⟨hMem, ?_⟩
      rw [hKey]
      exact hLocalNoCounterKey 0
    · -- counterRowsAtZero (flush)
      intro row hMem hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisCounterAtZero row hG.1 hInTable
      · exfalso
        rcases hInTable with ⟨id, hKey⟩
        rcases hLocalRowKey row hL.1 with hArch | ⟨_n, hLog⟩
        · rw [hArch] at hKey
          have : archiveTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_archiveTable this.symm
        · rw [hLog] at hKey
          have : logTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_logTable this.symm
    · -- liveCountersHaveNext (flush) visNext
      intro row hMem hLive hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisHaveNext row hG.1 hLive hInTable
      · exfalso
        rcases hInTable with ⟨id, hKey⟩
        rcases hLocalRowKey row hL.1 with hArch | ⟨_n, hLog⟩
        · rw [hArch] at hKey
          have : archiveTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_archiveTable this.symm
        · rw [hLog] at hKey
          have : logTable = counterTable := (Prod.mk.inj (Option.some.inj hKey)).1
          exact counterTable_ne_logTable this.symm
    · -- storageRowsLive (flush)
      intro row hMem hStorage
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisStorageLive row hG.1 hStorage
      · -- local rows: archive insert is alive, delete markers are filtered out by flush.
        -- Since hL.2 is `row.del = false`, the row is alive.
        exact hL.2
    · -- liveLog (flush) n iff snapNext ≤ n ∧ n < visNext
      have hSnapCutLeNext : snapCut ≤ snapNext := hSnapShape.1
      intro n
      constructor
      · -- forward
        intro hL
        rcases liveLog_of_flush hL with hVis | hLoc
        · -- Visible has live log at n. By iff: snapCut ≤ n < visNext. Need n ≥ snapNext.
          have hVisRange := (hVisLiveLog n).1 hVis
          -- Suppose n < snapNext. Then snap.liveLog n. So (logTable, n) ∈ local. But for the
          -- row to be in flush from visible, key should NOT be in local. So we need to extract
          -- the visible row's key-not-in-local from `hL`.
          -- Approach: re-derive from mem_flush_iff applied to liveLog directly.
          rcases hL with ⟨row, hMem, hLive, hKey⟩
          rw [mem_flush_iff] at hMem
          rcases hMem with hG | hLocalRow
          · -- row from visible. (logTable, n) ∉ local.
            have hKeyNotInLocal : (logTable, (n : Int)) ∉ localDb.keyDom := by
              rw [hKey] at hG
              exact hG.2
            -- Suppose snap.liveLog n. Then (logTable, n) ∈ local. Contradiction.
            -- For our n : Nat with snapCut ≤ n < visNext: if n < snapNext, then snap.liveLog n.
            -- But we need (logTable, n) ∉ local to imply ¬ snap.liveLog n.
            -- However, going the other way: if snap.liveLog n, then via the converse of our
            -- helper (which we don't have constructively), we'd get (logTable, n) ∈ local.
            -- WORKAROUND: split on n vs snapNext.
            by_cases hCase : n < snapNext
            · -- n < snapNext together with snapCut ≤ n gives snap.liveLog n.
              -- The converse helper builds a local delete marker at (logTable, n),
              -- contradicting hKeyNotInLocal.
              exfalso
              have hLow : snapCut ≤ n := hVisRange.1
              exact hKeyNotInLocal
                (archiveLogEffect_local_has_logKey i snapshotDb hSnapShape localDb
                  (fun row => hRows row) hLow hCase)
            · have hGe : snapNext ≤ n := by omega
              exact ⟨hGe, hVisRange.2⟩
          · -- row from local: alive. Local alive rows are archive insert (key archiveTable).
            -- But row's key is (logTable, n). Contradiction.
            exfalso
            rcases hLocalRow with ⟨hLocMem, _hAlive⟩
            rcases hLocalRowKey row hLocMem with hArch | ⟨_n', hLog⟩
            · rw [hArch] at hKey
              have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hKey)).1
              exact logTable_ne_archiveTable this.symm
            · -- Local has logTable key. Was the row originally a delete marker (del=true)?
              -- mem_flush_iff says committed rows are filtered for !del. So if from local, alive.
              -- But our archive local logTable rows are delete markers (del=true). They don't
              -- pass the filter. So local has no alive logTable row. Contradiction.
              -- Concretely: hAlive : row.del = false. But local logTable rows are markDeleted,
              -- which has del = true. So row.del = true, contradicting hAlive.
              have hDenote := (hRows row).2 hLocMem
              unfold archiveLogEffect at hDenote
              rw [SetLanguage.denote_union] at hDenote
              rcases hDenote with hInsert | hDelete
              · rcases hInsert with ⟨_, _, _, _, hRowEq⟩
                subst hRowEq
                rw [archiveRow_key?] at hLog
                have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hLog)).1
                exact logTable_ne_archiveTable this.symm
              · rcases hDelete with ⟨src, _, _, _, _, _, _, _, _, hRowEq⟩
                subst hRowEq
                have : (src.markDeleted (archiveTxnId i)).del = true := rfl
                rw [this] at _hAlive
                exact Bool.noConfusion _hAlive
        · -- Local has live log at n. But local's alive rows are archive inserts.
          exfalso
          rcases hLoc with ⟨row, hMem, _hLive, hKey⟩
          rcases hLocalRowKey row hMem with hArch | ⟨_n', hLog⟩
          · rw [hArch] at hKey
            have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hKey)).1
            exact logTable_ne_archiveTable this.symm
          · -- Local logTable row is a delete marker (del=true). Not live.
            -- Same argument as above.
            have hDenote := (hRows row).2 hMem
            unfold archiveLogEffect at hDenote
            rw [SetLanguage.denote_union] at hDenote
            rcases hDenote with hInsert | hDelete
            · rcases hInsert with ⟨_, _, _, _, hRowEq⟩
              subst hRowEq
              rw [archiveRow_key?] at hLog
              have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hLog)).1
              exact logTable_ne_archiveTable this.symm
            · rcases hDelete with ⟨src, _, _, _, _, _, _, _, _, hRowEq⟩
              subst hRowEq
              have hDel : (src.markDeleted (archiveTxnId i)).del = true := rfl
              unfold liveRow at _hLive
              rw [hDel] at _hLive
              exact Bool.noConfusion _hLive
      · -- backward: snapNext ≤ n ∧ n < visNext → liveLog (flush) n
        rintro ⟨hN, hLt⟩
        have hVisLog : liveLog visibleDb n :=
          (hVisLiveLog n).2 ⟨by omega, hLt⟩
        rcases hVisLog with ⟨row, hMem, hLive, hKey⟩
        refine ⟨row, ?_, hLive, hKey⟩
        rw [mem_flush_iff]
        refine Or.inl ⟨hMem, ?_⟩
        rw [hKey]
        intro hLocal
        -- Use easy helper: (logTable, n) ∈ local → snap has live log at n.
        rw [mem_keyDom_iff'] at hLocal
        rcases hLocal with ⟨row', hMem', hKey'⟩
        have hDenote' := (hRows row').2 hMem'
        rcases archiveLogSnapshotPost_local_logKey_implies_snap_log i snapshotDb hSnapLogInv
            hDenote' hKey' with ⟨src, hSrcMem, _hSrcLive, hSrcKey⟩
        -- snap has live log at n. By snap.iff: snapCut ≤ n < snapNext.
        rcases hSnapShape with ⟨_, _, _, _, _, hSnapLiveLog, _, _⟩
        have hSnapLog : liveLog snapshotDb (n : Int) := ⟨src, hSrcMem, _hSrcLive, hSrcKey⟩
        have := (hSnapLiveLog n).1 hSnapLog
        omega
    · -- archiveCovers (flush) n iff n < snapNext
      have hSnapCutLeNext : snapCut ≤ snapNext := hSnapShape.1
      intro n
      constructor
      · -- forward: archiveCovers (flush) n → n < snapNext
        intro hC
        rcases archiveCovers_of_flush hC with hVis | hLoc
        · -- Visible side: by visible's iff, n < snapCut, hence n < snapNext.
          have := (hVisArchive n).1 hVis
          omega
        · -- Local side: must be the archive insert.
          rcases hLoc with ⟨row, _idx, _lo, _hi, hMem, hLive, _hKey, hLo, hHi, hLeq, hLt⟩
          have hDenote := (hRows row).2 hMem
          unfold archiveLogEffect at hDenote
          rw [SetLanguage.denote_union] at hDenote
          rcases hDenote with hInsert | hDelete
          · -- Archive insert
            rcases hInsert with ⟨lo', hi0', _hMin', hMax', hRow⟩
            subst hRow
            rw [rowFieldInt?_archiveRow_lo] at hLo
            rw [rowFieldInt?_archiveRow_hi] at hHi
            have hLoEq : _lo = lo' := (Option.some.inj hLo).symm
            have hHiEq : _hi = hi0' + 1 := (Option.some.inj hHi).symm
            subst hLoEq; subst hHiEq
            -- We have lo' ≤ n < hi0'+1, so n ≤ hi0'.
            -- Witness for selectedLogMax hi0' shows snap has a log at (logTable, hi0').
            rcases hMax' with ⟨⟨witMax, hWitMax⟩, _hMaxAll⟩
            rcases hWitMax with ⟨hWitMem, hWitKey⟩
            have hHi0_nonneg : (0 : Int) ≤ hi0' := by
              have hN_nonneg : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
              omega
            obtain ⟨hi0Nat, hHi0Cast⟩ : ∃ k : Nat, hi0' = (k : Int) :=
              ⟨hi0'.toNat, (Int.toNat_of_nonneg hHi0_nonneg).symm⟩
            rw [hHi0Cast] at hWitKey
            rcases hSnapShape with ⟨_, _, _, _, hSnapStorageLive, hSnapLiveLog, _, _⟩
            have hWitLive : liveRow witMax :=
              hSnapStorageLive witMax hWitMem (Or.inr (Or.inl ⟨_, hWitKey⟩))
            have hSnapLog : liveLog snapshotDb (hi0Nat : Int) :=
              ⟨witMax, hWitMem, hWitLive, hWitKey⟩
            have hRange := (hSnapLiveLog hi0Nat).1 hSnapLog
            -- hRange : snapCut ≤ hi0Nat ∧ hi0Nat < snapNext.
            -- We have n ≤ hi0' = hi0Nat, so n < snapNext.
            have hN_le : (n : Int) ≤ (hi0Nat : Int) := by rw [← hHi0Cast]; omega
            have hN_le_nat : n ≤ hi0Nat := by exact_mod_cast hN_le
            omega
          · -- Delete marker: hLive contradicts (markDeleted has del = true)
            exfalso
            rcases hDelete with ⟨src, _n', _lo', _hi0', _, _, _, _, _, hRow⟩
            subst hRow
            unfold liveRow at hLive
            have : (src.markDeleted (archiveTxnId i)).del = true := rfl
            rw [this] at hLive
            exact Bool.noConfusion hLive
      · -- backward: n < snapNext → archiveCovers (flush) n
        intro hN
        by_cases hCase : n < snapCut
        · -- Visible side covers it
          have hVisCov : archiveCovers visibleDb n := (hVisArchive n).2 hCase
          rcases hVisCov with ⟨row, j, lo, hi, hMem, hLive, hKey, hLo, hHi, hLe, hLt⟩
          -- j is a Nat (from archiveCovers). visible's row at (archiveTable, ↑j).
          -- By hVisFresh, j ≠ i (else visible would have (archiveTable, ↑i) which is forbidden).
          apply archiveCovers_flush_of_global_witness hMem hLive hKey hLo hHi hLe hLt
          intro hLocal
          rw [mem_keyDom_iff'] at hLocal
          rcases hLocal with ⟨row', hMem', hKey'⟩
          rcases hLocalRowKey row' hMem' with hArch | ⟨_n', hLog⟩
          · -- Local archive at (archiveTable, ↑i). Visible's at (archiveTable, j).
            rw [hArch] at hKey'
            have hPair : (archiveTable, (i : Int)) = (archiveTable, j) :=
              Option.some.inj hKey'
            have hijEq : (i : Int) = j := (Prod.mk.inj hPair).2
            have hKeyAtI : row.key? = some (archiveTable, (i : Int)) := by
              rw [hKey, hijEq]
            exact hVisFresh i (Nat.le_refl i) row hMem hKeyAtI
          · rw [hLog] at hKey'
            have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey')).1
            exact logTable_ne_archiveTable this
        · -- snapCut ≤ n < snapNext: build local archive insert via min/max.
          have hCase' : snapCut ≤ n := by omega
          rcases hSnapShape with ⟨_, _, _, _, _, hSnapLiveLogShape, _, _⟩
          rcases (hSnapLiveLogShape n).2 ⟨hCase', hN⟩ with
            ⟨src, hSrcMem, _, hSrcKey⟩
          rcases selectedLogMin_exists snapshotDb src n hSrcMem hSrcKey with
            ⟨lo, ⟨witLo, hLoMem, hLoKey⟩, hLoMin⟩
          rcases selectedLogMax_exists snapshotDb src n hSrcMem hSrcKey with
            ⟨hi, ⟨witHi, hHiMem, hHiKey⟩, hHiMax⟩
          let archRow : Row := archiveRow (archiveTxnId i) i lo (hi + 1)
          have hDenote :
              SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb)
                (archiveLogEffect (archiveTxnId i) i) archRow := by
            unfold archiveLogEffect
            rw [SetLanguage.denote_union]
            refine Or.inl ?_
            refine ⟨lo, hi, ?_, ?_, rfl⟩
            · refine ⟨⟨witLo, hLoMem, hLoKey⟩, ?_⟩
              intro row' n' hSel'
              exact hLoMin row' n' hSel'.1 hSel'.2
            · refine ⟨⟨witHi, hHiMem, hHiKey⟩, ?_⟩
              intro row' n' hSel'
              exact hHiMax row' n' hSel'.1 hSel'.2
          have hLocalMem : archRow ∈ localDb := (hRows archRow).1 hDenote
          have hKey : archRow.key? = some (archiveTable, (i : Int)) :=
            archiveRow_key? _ _ _ _
          have hLive : liveRow archRow := rfl
          have hLoFld : rowFieldInt? archRow loField = some lo :=
            rowFieldInt?_archiveRow_lo _ _ _ _
          have hHiFld : rowFieldInt? archRow hiField = some (hi + 1) :=
            rowFieldInt?_archiveRow_hi _ _ _ _
          have hLoLeN : lo ≤ (n : Int) := hLoMin src n hSrcMem hSrcKey
          have hNLeHi : (n : Int) ≤ hi := hHiMax src n hSrcMem hSrcKey
          have hMemFlush : archRow ∈ Database.flush localDb visibleDb := by
            rw [mem_flush_iff]
            exact Or.inr ⟨hLocalMem, hLive⟩
          refine ⟨archRow, (i : Int), lo, hi + 1, hMemFlush, hLive, hKey,
            hLoFld, hHiFld, hLoLeN, by omega⟩
    · -- archiveIntervalsWellFormed (flush)
      intro row idx lo hi hMem hLive hKey hLo hHi
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hVisIntervals row idx lo hi hG.1 hLive hKey hLo hHi
      · -- Local row with archive key: it's the archive insert row.
        -- Unfold archiveLogInsertEffect to get lo, hi values.
        rcases hPostWeak with ⟨snapDb', _hSnapInv', _hReach', hRows'⟩
        have hDenote := (hRows' row).2 hL.1
        unfold archiveLogEffect at hDenote
        rw [SetLanguage.denote_union] at hDenote
        rcases hDenote with hInsert | hDelete
        · -- Archive insert: row = archiveRow txnId i lo' (hi0+1) with lo' ≤ hi0.
          rcases hInsert with ⟨lo', hi0', hMin', hMax', hRow⟩
          subst hRow
          rcases hMin' with ⟨⟨witMin, hWitMin⟩, _hMinAll⟩
          rcases hMax' with ⟨_hWitMax, hMaxAll⟩
          rcases hWitMin with ⟨_hMinMem, hMinKey⟩
          have hMinLeMax : lo' ≤ hi0' := hMaxAll witMin lo' ⟨_hMinMem, hMinKey⟩
          -- hLo: rowFieldInt? row loField = some lo. row = archiveRow ... lo' (hi0'+1).
          rw [rowFieldInt?_archiveRow_lo] at hLo
          rw [rowFieldInt?_archiveRow_hi] at hHi
          have : lo = lo' := (Option.some.inj hLo).symm
          have : hi = hi0' + 1 := (Option.some.inj hHi).symm
          omega
        · -- Delete marker: hLive = false (markDeleted has del = true)
          exfalso
          rcases hDelete with ⟨src, _n', _lo, _hi0, _, _, _hSel, _, _, hRow⟩
          subst hRow
          unfold liveRow at hLive
          have : (src.markDeleted (archiveTxnId i)).del = true := rfl
          rw [this] at hLive
          exact Bool.noConfusion hLive
  · -- sameResultRows: local has only archive/log keys, never resultTable
    intro q n
    constructor
    · intro hNew
      rcases resultRowFor_of_flush hNew with hOld | hLocal
      · exact hOld
      · exfalso
        rcases hLocal with ⟨row, hMem, _hLive, hKey⟩
        rcases hLocalRowKey row hMem with hArch | ⟨_n', hLog⟩
        · rw [hArch] at hKey
          have : archiveTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
          exact resultTable_ne_archiveTable q this.symm
        · rw [hLog] at hKey
          have : logTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
          exact resultTable_ne_logTable q this.symm
    · intro hOld
      apply resultRowFor_flush_of_global _ hOld
      intro hLocal
      rw [mem_keyDom_iff'] at hLocal
      rcases hLocal with ⟨row, hMem, hKey⟩
      rcases hLocalRowKey row hMem with hArch | ⟨_n', hLog⟩
      · rw [hArch] at hKey
        have : archiveTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
        exact resultTable_ne_archiveTable q this.symm
      · rw [hLog] at hKey
        have : logTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
        exact resultTable_ne_logTable q this.symm
  · -- preservesWellFormedTableFields
    intro hOldWF row hMem
    rw [mem_flush_iff] at hMem
    rcases hMem with hG | hL
    · exact hOldWF row hG.1
    · rcases hLocalRowKey row hL.1 with hArch | ⟨n, hLog⟩
      · -- Archive insert row
        refine ⟨archiveTable, (i : Int), hArch, ?_⟩
        -- Need: rowFieldInt? row tableField = some archiveTable
        -- The row is denoted by archiveLogInsertEffect, so it equals
        -- archiveRow txnId i lo (hi0+1). Use the existing helper.
        rcases hPostWeak with ⟨snapDb', _hSnapInv', _hReach', hRows'⟩
        have hDenote := (hRows' row).2 hL.1
        unfold archiveLogEffect at hDenote
        rw [SetLanguage.denote_union] at hDenote
        rcases hDenote with hInsert | hDelete
        · rcases hInsert with ⟨lo, hi0, _hMin, _hMax, hRow⟩
          subst hRow
          exact rowFieldInt?_archiveRow_table _ _ _ _
        · rcases hDelete with ⟨src, _n', _lo, _hi0, _, _, hSel, _, _, hRow⟩
          subst hRow
          rcases hSel with ⟨_hMem, hSrcKey⟩
          rw [markDeleted_key?] at hArch
          rw [hSrcKey] at hArch
          have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hArch)).1
          exact absurd this logTable_ne_archiveTable
      · -- Log delete marker
        refine ⟨logTable, n, hLog, ?_⟩
        -- Need: rowFieldInt? row tableField = some logTable
        -- The row is denoted by archiveLogDeleteEffect, so it equals
        -- src.markDeleted txnId where src is a log row.
        rcases hPostWeak with ⟨snapDb', hSnapInv', _hReach', hRows'⟩
        have hDenote := (hRows' row).2 hL.1
        unfold archiveLogEffect at hDenote
        rw [SetLanguage.denote_union] at hDenote
        rcases hDenote with hInsert | hDelete
        · -- archive insert: contradicts hLog
          exfalso
          rcases hInsert with ⟨lo, hi0, _hMin, _hMax, hRow⟩
          subst hRow
          rw [archiveRow_key?] at hLog
          have : archiveTable = logTable := (Prod.mk.inj (Option.some.inj hLog)).1
          exact logTable_ne_archiveTable this.symm
        · rcases hDelete with ⟨src, _n', _lo, _hi0, _, _, hSel, _, _, hRow⟩
          subst hRow
          rcases hSel with ⟨hSrcMem, hSrcKey⟩
          -- src is in snapshot's globalDb (= snapDb'). We have hSrcKey : src.key? = some (logTable, _n').
          -- The markDeleted preserves visible, so row.visible = src.visible.
          -- We need rowFieldInt? row tableField = some logTable.
          -- src has wellFormedTableFields → src.tableField = some logTable.
          rcases hSnapInv' with ⟨_, _, _, _, hSnapWF'⟩
          have hSrcMemDb : src ∈ snapDb' := hSrcMem
          have hSrcTab := rowFieldInt?_tableField_of_key_wellFormed hSnapWF' hSrcMemDb hSrcKey
          show rowFieldInt? (src.markDeleted (archiveTxnId i)) tableField = some logTable
          rw [rowFieldInt?_eq_some_iff_lookup]
          show (src.markDeleted (archiveTxnId i)).visible.lookup? tableField = some (.int logTable)
          show src.visible.lookup? tableField = some (.int logTable)
          have := (rowFieldInt?_eq_some_iff_lookup (row := src)
            (field := tableField) (v := logTable)).mp hSrcTab
          exact this

/-- Storage rows in a `wellFormedTableFields` database have keys disjoint
from any `resultTable q`. -/
theorem storageKey_ne_resultKey
    {row : Row} {table : TableName} {id n : Int} {q : Nat}
    (hKey : row.key? = some (table, id))
    (hStorage : table = counterTable ∨ table = logTable ∨ table = archiveTable)
    (hResult : row.key? = some (resultTable q, n)) :
    False := by
  rw [hKey] at hResult
  have hPair : (table, id) = (resultTable q, n) := Option.some.inj hResult
  have hTab : table = resultTable q := (Prod.mk.inj hPair).1
  rcases hStorage with rfl | rfl | rfl
  · exact resultTable_ne_counterTable q hTab.symm
  · exact resultTable_ne_logTable q hTab.symm
  · exact resultTable_ne_archiveTable q hTab.symm

/-- Local rows of select have keys disjoint from any storage table key. -/
theorem selectAllLogSnapshotPost_storageNoClobber
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb)
    (row : Row) (key : RowKey)
    (_hMem : row ∈ visibleDb)
    (hKey : row.key? = some key)
    (hStorage : key.fst = counterTable ∨ key.fst = logTable ∨ key.fst = archiveTable) :
    key ∉ localDb.keyDom := by
  intro hLocal
  rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost key hLocal with
    ⟨n, hKeyEq⟩
  subst hKeyEq
  simp at hStorage
  rcases hStorage with hCounter | hLog | hArchive
  · exact resultTable_ne_counterTable q hCounter
  · exact resultTable_ne_logTable q hLog
  · exact resultTable_ne_archiveTable q hArchive

/-- For result-row keys for queries other than `q`, local does not clobber. -/
theorem selectAllLogSnapshotPost_otherQueryNoClobber
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb)
    {q' : Nat} {n : Int} (hNe : q' ≠ q) :
    (resultTable q', n) ∉ localDb.keyDom := by
  intro hLocal
  rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost _ hLocal with
    ⟨_m, hKeyEq⟩
  have hPair : (resultTable q', n) = (resultTable q, _m) := hKeyEq
  have hTab : resultTable q' = resultTable q := (Prod.mk.inj hPair).1
  exact hNe (resultTable_injective hTab)

/-- Local rows of select are alive `resultRowLit (selectTxnId q) q m` rows. They
sit in `resultTable q`, so they cannot have any storage-table key. -/
theorem selectAllLogSnapshotPost_local_no_storage_key
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb)
    {row : Row} (hMem : row ∈ localDb)
    {table : TableName} {id : Int}
    (hKey : row.key? = some (table, id))
    (hStorage : table = counterTable ∨ table = logTable ∨ table = archiveTable) :
    False := by
  rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row hMem with
    ⟨m, hEq⟩
  subst hEq
  rw [resultRowLit_key?] at hKey
  have hPair : (resultTable q, m) = (table, id) := Option.some.inj hKey
  have hTab : resultTable q = table := (Prod.mk.inj hPair).1
  rcases hStorage with hCounter | hLog | hArchive
  · exact resultTable_ne_counterTable q (hTab.trans hCounter)
  · exact resultTable_ne_logTable q (hTab.trans hLog)
  · exact resultTable_ne_archiveTable q (hTab.trans hArchive)

/-- Mirror image of `liveLog_of_flush` and `liveLog_flush_of_global` packaged as
an iff for select: local has no log rows, so `liveLog` transfers in both
directions. -/
theorem selectAllLogSnapshotPost_liveLog_iff
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ n : Int, liveLog (Database.flush localDb visibleDb) n ↔ liveLog visibleDb n := by
  intro n
  refine ⟨?_, ?_⟩
  · intro h
    rcases liveLog_of_flush h with hVis | hLoc
    · exact hVis
    · rcases hLoc with ⟨row, hMem, _hLive, hKey⟩
      exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
        hMem hKey (Or.inr (Or.inl rfl)))
  · intro h
    refine liveLog_flush_of_global ?_ h
    intro hLocal
    rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost _ hLocal with
      ⟨_m, hEq⟩
    have hTab : logTable = resultTable q := (Prod.mk.inj hEq).1
    exact resultTable_ne_logTable q hTab.symm

/-- Same for `liveCounterAt`. -/
theorem selectAllLogSnapshotPost_liveCounterAt_iff
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ next : Int,
      liveCounterAt (Database.flush localDb visibleDb) next ↔ liveCounterAt visibleDb next := by
  intro next
  refine ⟨?_, ?_⟩
  · intro h
    rcases liveCounterAt_of_flush h with hVis | hLoc
    · exact hVis
    · rcases hLoc with ⟨row, hMem, _hLive, hKey, _hNext⟩
      exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
        hMem hKey (Or.inl rfl))
  · intro h
    refine liveCounterAt_flush_of_global ?_ h
    intro hLocal
    rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost _ hLocal with
      ⟨_m, hEq⟩
    have hTab : counterTable = resultTable q := (Prod.mk.inj hEq).1
    exact resultTable_ne_counterTable q hTab.symm

/-- Same for `archiveCovers`. -/
theorem selectAllLogSnapshotPost_archiveCovers_iff
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    ∀ n : Int, archiveCovers (Database.flush localDb visibleDb) n ↔ archiveCovers visibleDb n := by
  intro n
  refine ⟨?_, ?_⟩
  · intro h
    rcases archiveCovers_of_flush h with hVis | hLoc
    · exact hVis
    · rcases hLoc with ⟨row, _i, _lo, _hi, hMem, _hLive, hKey, _, _, _, _⟩
      exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
        hMem hKey (Or.inr (Or.inr rfl)))
  · intro h
    refine archiveCovers_flush_of_global ?_ h
    intro i hLocal
    rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost _ hLocal with
      ⟨_m, hEq⟩
    have hTab : archiveTable = resultTable q := (Prod.mk.inj hEq).1
    exact resultTable_ne_archiveTable q hTab.symm

/-- A key in `localDb.keyDom` comes from some local row whose `key?` matches. -/
theorem mem_keyDom_iff (db : Database) (key : RowKey) :
    key ∈ db.keyDom ↔ ∃ row, row ∈ db ∧ row.key? = some key := by
  unfold Database.keyDom
  simp [List.mem_filterMap]

/-- The key `(table, id)` is not in select's local keyDom whenever `table` is a
storage table. -/
theorem selectAllLogSnapshotPost_local_storage_no_clobber
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb)
    {table : TableName} {id : Int}
    (hStorage : table = counterTable ∨ table = logTable ∨ table = archiveTable) :
    (table, id) ∉ localDb.keyDom := by
  intro hLocal
  rw [mem_keyDom_iff] at hLocal
  rcases hLocal with ⟨row, hMem, hKey⟩
  exact selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
    hMem hKey hStorage

theorem selectAllLogSnapshotPost_sameStorageShape
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    sameStorageShape visibleDb (Database.flush localDb visibleDb) := by
  intro cut next
  have hLiveLogIff := selectAllLogSnapshotPost_liveLog_iff q localDb visibleDb hPost
  have hCounterIff := selectAllLogSnapshotPost_liveCounterAt_iff q localDb visibleDb hPost
  have hArchiveIff := selectAllLogSnapshotPost_archiveCovers_iff q localDb visibleDb hPost
  have hCounterClobber : ∀ id : Int, (counterTable, id) ∉ localDb.keyDom := fun id =>
    selectAllLogSnapshotPost_local_storage_no_clobber
      (q := q) (localDb := localDb) (visibleDb := visibleDb) (id := id) hPost (Or.inl rfl)
  have hLogClobber : ∀ id : Int, (logTable, id) ∉ localDb.keyDom := fun id =>
    selectAllLogSnapshotPost_local_storage_no_clobber
      (q := q) (localDb := localDb) (visibleDb := visibleDb) (id := id) hPost (Or.inr (Or.inl rfl))
  have hArchClobber : ∀ id : Int, (archiveTable, id) ∉ localDb.keyDom := fun id =>
    selectAllLogSnapshotPost_local_storage_no_clobber
      (q := q) (localDb := localDb) (visibleDb := visibleDb) (id := id) hPost (Or.inr (Or.inr rfl))
  refine ⟨?_, ?_⟩
  · -- forward
    rintro ⟨hCut, hCounter, hCounterAtZero, hHaveNext, hStorageLive,
      hLiveLog, hArchive, hIntervals⟩
    refine ⟨hCut, (hCounterIff _).2 hCounter, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- counterRowsAtZero flush
      intro row hMem hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hCounterAtZero row hG.1 hInTable
      · rcases hInTable with ⟨id, hKey⟩
        exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
          hL.1 hKey (Or.inl rfl))
    · -- liveCountersHaveNext flush
      intro row hMem hLive hInTable
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hHaveNext row hG.1 hLive hInTable
      · rcases hInTable with ⟨id, hKey⟩
        exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
          hL.1 hKey (Or.inl rfl))
    · -- storageRowsLive flush
      intro row hMem hStorage
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hStorageLive row hG.1 hStorage
      · exact hL.2
    · intro n; exact (hLiveLogIff n).trans (hLiveLog n)
    · intro n; exact (hArchiveIff n).trans (hArchive n)
    · -- archiveIntervalsWellFormed flush
      intro row i lo hi hMem hLive hKey hLo hHi
      rw [mem_flush_iff] at hMem
      rcases hMem with hG | hL
      · exact hIntervals row i lo hi hG.1 hLive hKey hLo hHi
      · exact False.elim (selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
          hL.1 hKey (Or.inr (Or.inr rfl)))
  · -- backward
    rintro ⟨hCut, hCounter, hCounterAtZero, hHaveNext, hStorageLive,
      hLiveLog, hArchive, hIntervals⟩
    refine ⟨hCut, (hCounterIff next).1 hCounter, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- counterRowsAtZero visible
      intro row hMem hInTable
      apply hCounterAtZero row _ hInTable
      rw [mem_flush_iff]
      refine Or.inl ⟨hMem, ?_⟩
      rcases hInTable with ⟨id, hKey⟩
      rw [hKey]
      exact hCounterClobber id
    · -- liveCountersHaveNext visible
      intro row hMem hLive hInTable
      apply hHaveNext row _ hLive hInTable
      rw [mem_flush_iff]
      refine Or.inl ⟨hMem, ?_⟩
      rcases hInTable with ⟨id, hKey⟩
      rw [hKey]
      exact hCounterClobber id
    · -- storageRowsLive visible
      intro row hMem hStorage
      apply hStorageLive row _ hStorage
      rw [mem_flush_iff]
      refine Or.inl ⟨hMem, ?_⟩
      rcases hStorage with ⟨id, hKey⟩ | ⟨id, hKey⟩ | ⟨id, hKey⟩
      · rw [hKey]; exact hCounterClobber id
      · rw [hKey]; exact hLogClobber id
      · rw [hKey]; exact hArchClobber id
    · intro n; exact (hLiveLogIff n).symm.trans (hLiveLog n)
    · intro n; exact (hArchiveIff n).symm.trans (hArchive n)
    · -- archiveIntervalsWellFormed visible
      intro row i lo hi hMem hLive hKey hLo hHi
      apply hIntervals row i lo hi _ hLive hKey hLo hHi
      rw [mem_flush_iff]
      refine Or.inl ⟨hMem, ?_⟩
      rw [hKey]
      exact hArchClobber i

theorem selectAllLogSnapshotPost_preservesWellFormedTableFields
    (q : Nat) (localDb visibleDb : Database)
    (hPost :
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
        localDb visibleDb) :
    preservesWellFormedTableFields visibleDb (Database.flush localDb visibleDb) := by
  intro hWFOld row hMem
  rw [mem_flush_iff] at hMem
  rcases hMem with hG | hL
  · exact hWFOld row hG.1
  · rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row
      hL.1 with ⟨m, hEq⟩
    subst hEq
    refine ⟨resultTable q, m, resultRowLit_key? _ _ _, ?_⟩
    exact rowFieldInt?_resultRowLit_table _ _ _

theorem selectAllLogEffect_guaranteeCore_final (q : Nat) :
    ∀ localDb visibleDb,
      logSystemInv visibleDb →
        txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
            localDb visibleDb →
          G_selectCore q visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb _hVisInv hPost
  refine ⟨selectAllLogSnapshotPost_sameStorageShape q localDb visibleDb hPost,
    ?_, ?_, selectAllLogSnapshotPost_preservesWellFormedTableFields q localDb visibleDb hPost, ?_⟩
  -- sameResultRowsExcept
  · intro q' n hNe
    constructor
    · intro hNew
      rcases resultRowFor_of_flush hNew with hOld | hLocal
      · exact hOld
      · exfalso
        rcases hLocal with ⟨row, hMem, _hLive, hKey⟩
        rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row
          hMem with ⟨m, hEq⟩
        subst hEq
        rw [resultRowLit_key?] at hKey
        have : resultTable q = resultTable q' := (Prod.mk.inj (Option.some.inj hKey)).1
        exact hNe (resultTable_injective this).symm
    · intro hOld
      exact resultRowFor_flush_of_global
        (selectAllLogSnapshotPost_otherQueryNoClobber q localDb visibleDb hPost hNe)
        hOld
  -- preservesArchiveKeyFreshness
  · intro i hOldFresh row hMemNew hKey
    rw [mem_flush_iff] at hMemNew
    rcases hMemNew with hG | hL
    · exact hOldFresh row hG.1 hKey
    · exact selectAllLogSnapshotPost_local_no_storage_key q localDb visibleDb hPost
        hL.1 hKey (Or.inr (Or.inr rfl))
  -- prefix
  · rcases selectAllLogSnapshotPost_local_result_prefix q localDb visibleDb hPost with
      ⟨k, hLocalPrefix⟩
    refine ⟨k, ?_, ?_⟩
    · intro n
      constructor
      · intro hNew
        rcases resultRowFor_of_flush hNew with hOld | hLocal
        · exact Or.inl hOld
        · have hMem :=
            (selectAllLogSnapshotPost_local_resultRowFor_iff q localDb visibleDb hPost n).1 hLocal
          exact Or.inr ((hLocalPrefix n).1 hMem)
      · intro hOldOrPrefix
        rcases hOldOrPrefix with hOld | hPrefix
        · -- hOld : resultRowFor visibleDb q n. Need: resultRowFor flush q n.
          -- If n < k, local has the row, use resultRowFor_flush_of_local.
          -- Else (n ≥ k), local doesn't have the key, use resultRowFor_flush_of_global.
          by_cases hLt : n < k
          · have hMem : resultRowLit (selectTxnId q) q n ∈ localDb := (hLocalPrefix n).2 hLt
            exact resultRowFor_flush_of_local
              ((selectAllLogSnapshotPost_local_resultRowFor_iff q localDb visibleDb hPost n).2 hMem)
          · apply resultRowFor_flush_of_global _ hOld
            intro hLocal
            rcases selectAllLogSnapshotPost_local_keyDom_results q localDb visibleDb hPost _
              hLocal with ⟨m, hEq⟩
            have hPair : (resultTable q, (n : Int)) = (resultTable q, m) := hEq
            have hM : (n : Int) = m := (Prod.mk.inj hPair).2
            have hMemLocal : resultRowLit (selectTxnId q) q (n : Int) ∈ localDb := by
              -- Construct from the local key membership
              unfold Database.keyDom at hLocal
              simp [List.mem_filterMap] at hLocal
              rcases hLocal with ⟨row, hMem, hKey⟩
              rcases selectAllLogSnapshotPost_local_rows_are_results q localDb visibleDb hPost row
                hMem with ⟨m', hEq'⟩
              subst hEq'
              rw [resultRowLit_key?] at hKey
              have : m' = (n : Int) := by
                have hPair' : (resultTable q, m') = (resultTable q, (n : Int)) :=
                  Option.some.inj hKey
                exact (Prod.mk.inj hPair').2
              subst this
              exact hMem
            exact hLt ((hLocalPrefix n).1 hMemLocal)
        · have hMem : resultRowLit (selectTxnId q) q n ∈ localDb := (hLocalPrefix n).2 hPrefix
          exact resultRowFor_flush_of_local
            ((selectAllLogSnapshotPost_local_resultRowFor_iff q localDb visibleDb hPost n).2 hMem)
    · intro n hlt
      have hMem : resultRowLit (selectTxnId q) q n ∈ localDb := (hLocalPrefix n).2 hlt
      exact selectAllLogSnapshotPost_local_result_expanded_visible q localDb visibleDb hPost n hMem

theorem selectAllLogEffect_guarantee_final (q : Nat) :
    ∀ localDb visibleDb,
      txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)
          localDb visibleDb →
        G_select q visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hPost
  -- G_select is now unconditional (= G_selectCore). Derive logSystemInv visibleDb
  -- from txnSnapshotPost + stability under R_select.
  rcases hPost with ⟨snapshotDb, hSnapInv, hReach, _hRows⟩
  have hVisInv : logSystemInv visibleDb :=
    logSystemInv_stable_multiStep (logSystemInv_stable_R_select q) hReach hSnapInv
  exact selectAllLogEffect_guaranteeCore_final q localDb visibleDb hVisInv
    ⟨snapshotDb, hSnapInv, hReach, _hRows⟩

/-! ## Indexed archive leaf

The indexed archive leaf needs the additional fact that after flushing the
archive transaction's local delta, the archive-key freshness advances from `i`
to `i+1`. -/

theorem archiveLogSnapshotPost_preservesArchiveKeysFreshFrom_succ_final (i : Nat) :
    ∀ localDb visibleDb,
      archiveKeysFreshFrom i visibleDb →
        txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)
            localDb visibleDb →
          archiveKeysFreshFrom (i + 1) (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hFresh hPost
  intro j hj row hMem hKey
  rw [mem_flush_iff] at hMem
  rcases hMem with hOld | hLocal
  · exact hFresh j (by omega) row hOld.1 hKey
  · rcases archiveLogSnapshotPost_local_row_key i localDb visibleDb hPost row hLocal.1 with
      hArchive | hLog
    · rw [hArchive] at hKey
      have hPair : (archiveTable, (i : Int)) = (archiveTable, (j : Int)) :=
        Option.some.inj hKey
      have : (i : Int) = (j : Int) := (Prod.mk.inj hPair).2
      omega
    · rcases hLog with ⟨_n, hLogKey⟩
      rw [hLogKey] at hKey
      have : logTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
      exact logTable_ne_archiveTable this

theorem archiveLogIndexedTxnSpec_of_paperObligations (i : Nat)
    (hInfer :
      PaperInfer
        (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
        (archiveTxnId i) logSystemInv SetLanguage.empty (archiveLogBody i)
        (archiveLogEffect (archiveTxnId i) i))
    (hQstable :
      Logic.stableBiAssertion
        (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).commit)
        (txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)))
    (hGuarantee :
      ∀ localDb visibleDb,
        txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)
            localDb visibleDb →
          G_archive visibleDb (Database.flush localDb visibleDb)) :
    archiveLogIndexedTxnSpec i := by
  let hObligations : ArchiveLogPaperObligations i :=
    { effect := archiveLogEffect (archiveTxnId i) i
      infer := hInfer
      qstable := hQstable
      guarantee := hGuarantee }
  simpa [archiveLogIndexedTxnSpec, txnSpecValid, txnSpecProgram,
    archiveLogIndexedSpec, archiveLogTxn]
    using
      globalValid_snapshot_of_paperObligations_post
        relyNoUndo_R_archive
        logSystemInv_stable_R_archive
        (archiveIndexedInv_stable_R_archive i)
        (archiveIndexedInv_stable_R_archive (i + 1))
        (fun _ hInv => hInv.1)
        hObligations
        (fun localDb visibleDb hInv hPost =>
          ⟨ G_archive_preserves_logSystemInv hInv.1
              (hObligations.guarantee localDb visibleDb hPost)
          , archiveLogSnapshotPost_preservesArchiveKeysFreshFrom_succ_final i
              localDb visibleDb hInv.2 hPost
          ⟩)

/-- Indexed archive wrapper that threads `archiveKeysFreshFrom i` into the
PaperInfer invariant. The bridge therefore receives a snapshot post over the
strengthened invariant `logSystemInv ∧ archiveKeysFreshFrom i`, which in turn
gives visible's freshness for the storage-shape transition (no archive-id
collision means the local archive row purely extends archive coverage). -/
theorem archiveLogIndexedTxnSpec_of_indexedPaperObligations (i : Nat)
    (hInfer :
      PaperInfer
        (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).exec)
        (archiveTxnId i)
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        SetLanguage.empty (archiveLogBody i)
        (archiveLogEffect (archiveTxnId i) i))
    (hQstable :
      Logic.stableBiAssertion
        (Logic.relyMod R_archive (IsolationSpec.snapshot (σ := Database)).commit)
        (txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
          R_archive (archiveLogEffect (archiveTxnId i) i)))
    (hGuarantee :
      ∀ localDb visibleDb,
        txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
            R_archive (archiveLogEffect (archiveTxnId i) i) localDb visibleDb →
          G_archive visibleDb (Database.flush localDb visibleDb)) :
    archiveLogIndexedTxnSpec i := by
  let hObligations :
      TxnPaperObligationsSI R_archive
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) G_archive
        (archiveTxnId i) (archiveLogBody i) :=
    { effect := archiveLogEffect (archiveTxnId i) i
      infer := hInfer
      qstable := hQstable
      guarantee := hGuarantee }
  simpa [archiveLogIndexedTxnSpec, txnSpecValid, txnSpecProgram,
    archiveLogIndexedSpec, archiveLogTxn]
    using
      globalValid_snapshot_of_paperObligations_post
        relyNoUndo_R_archive
        (archiveIndexedInv_stable_R_archive i)
        (archiveIndexedInv_stable_R_archive i)
        (archiveIndexedInv_stable_R_archive (i + 1))
        (fun _ hInv => hInv)
        hObligations
        (fun localDb visibleDb hInv hPost =>
          ⟨ G_archive_preserves_logSystemInv hInv.1
              (hObligations.guarantee localDb visibleDb hPost)
          , archiveLogSnapshotPost_preservesArchiveKeysFreshFrom_succ_final i
              localDb visibleDb hInv.2
              (txnSnapshotPost_weaken (fun _ h => h.1) hPost)
          ⟩)

/-! ## Final leaf theorems -/

theorem insertLogIndexedTxnSpec_final (i : Nat) :
    insertLogIndexedTxnSpec i := by
  refine insertLogIndexedTxnSpec_of_indexedPaperObligations i ?_
  refine
    { effect := insertLogEffect (insertTxnId i) i
      infer := paperInfer_insertLogBody_indexed_final i
      qstable := insertLogIndexedEffect_qstable_final i
      guarantee := insertLogIndexedEffect_guarantee_final i }

theorem archiveLogIndexedTxnSpec_final (i : Nat) :
    archiveLogIndexedTxnSpec i :=
  archiveLogIndexedTxnSpec_of_indexedPaperObligations i
    (paperInfer_archiveLogBody_indexed_final i)
    (archiveLogIndexedEffect_qstable_final i)
    (archiveLogIndexedEffect_guarantee_final i)

theorem selectAllLogTxnSpec_final (q : Nat) :
    selectAllLogTxnSpec q := by
  refine selectAllLogTxnSpec_of_paperObligations q ?_
  refine
    { effect := selectAllLogEffect (selectTxnId q) q
      infer := paperInfer_selectAllLogBody_final q
      qstable := selectAllLogEffect_qstable_final q
      guarantee := selectAllLogEffect_guarantee_final q }

end LogStorageExample

end Transformer

end DbAppProgramLogic
