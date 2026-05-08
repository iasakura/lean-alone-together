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
    intro _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hCommitStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).commit := by
    intro _ _ _ _ _ _; exact ⟨trivial, trivial⟩
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
    intro _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hCommitStable :
      Logic.stableIsolation R (IsolationSpec.readCommitted Database).commit := by
    intro _ _ _ _ _ _; exact ⟨trivial, trivial⟩
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

abbrev InsertLogPaperObligations (i : Nat) :=
  TxnPaperObligations R_insert (logSystemInvAtNext i) G_insert
    (insertTxnId i) (insertLogBody i)

abbrev ArchiveLogPaperObligations (i : Nat) :=
  TxnPaperObligations R_archive logSystemInv G_archive
    (archiveTxnId i) (archiveLogBody i)

abbrev SelectAllLogPaperObligations (q : Nat) :=
  TxnPaperObligations (R_select q) logSystemInv (G_select q)
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

def selectedLogRow (globalDb : SetLanguage.SetDenotation) (row : Row) (n : Int) : Prop :=
  globalDb row ∧ row.key? = some (logTable, n)

def selectedLogMin (globalDb : SetLanguage.SetDenotation) (lo : Int) : Prop :=
  (∃ row, selectedLogRow globalDb row lo) ∧
    ∀ row n, selectedLogRow globalDb row n → lo ≤ n

def selectedLogMax (globalDb : SetLanguage.SetDenotation) (hi : Int) : Prop :=
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

theorem archiveLogTxnSpec_of_paperObligations (i : Nat)
    (hObligations : ArchiveLogPaperObligations i) :
    archiveLogTxnSpec i := by
  simpa [archiveLogTxnSpec, txnSpecValid, txnSpecProgram, archiveLogSpec,
    ArchiveLogPaperObligations]
    using
      globalValid_readCommitted_of_paperObligations
        logSystemInv_stable_R_archive
        (fun _ _ hInv hG => G_archive_preserves_logSystemInv hInv hG)
        hObligations

theorem selectAllLogTxnSpec_of_paperObligations (q : Nat)
    (hObligations : SelectAllLogPaperObligations q) :
    selectAllLogTxnSpec q := by
  simpa [selectAllLogTxnSpec, txnSpecValid, txnSpecProgram, selectAllLogSpec,
    SelectAllLogPaperObligations]
    using
      globalValid_readCommitted_of_paperObligations
        (logSystemInv_stable_R_select q)
        (fun _ _ hInv hG => G_select_preserves_logSystemInv hInv hG)
        hObligations

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

theorem paperInfer_insertLogBody_indexed_final (i : Nat) :
    PaperInfer
      (Logic.relyMod R_insert (IsolationSpec.readCommitted Database).exec)
      (insertTxnId i) (logSystemInvAtNext i) SetLanguage.empty (insertLogBody i)
      (insertLogEffect (insertTxnId i) i) :=
  paperInfer_insertLogBody_of_stable R_insert (logSystemInvAtNext i)
    (insertTxnId i) i (logSystemInvAtNext_stable_R_insert i)

/-- `PaperInfer` derivation for `archiveLogBody`. -/
theorem paperInfer_archiveLogBody_final (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).exec)
      (archiveTxnId i) logSystemInv SetLanguage.empty (archiveLogBody i)
      (archiveLogEffect (archiveTxnId i) i) := by
  sorry

/-- `PaperInfer` derivation for `selectAllLogBody q`. -/
theorem paperInfer_selectAllLogBody_final (q : Nat) :
    PaperInfer
      (Logic.relyMod (R_select q) (IsolationSpec.readCommitted Database).exec)
      (selectTxnId q) logSystemInv SetLanguage.empty (selectAllLogBody q)
      (selectAllLogEffect (selectTxnId q) q) := by
  sorry

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
      (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)) :=
  txnSnapshotPost_stable_readCommitted logSystemInv R_archive
    (archiveLogEffect (archiveTxnId i) i)

theorem selectAllLogEffect_qstable_final (q : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod (R_select q) (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)) :=
  txnSnapshotPost_stable_readCommitted logSystemInv (R_select q)
    (selectAllLogEffect (selectTxnId q) q)

/-- Indexed insert guarantee bridge. -/
theorem insertLogIndexedEffect_guarantee_final (i : Nat) :
    ∀ localDb visibleDb,
      txnSnapshotPost (logSystemInvAtNext i) R_insert
          (insertLogEffect (insertTxnId i) i) localDb visibleDb →
        G_insert visibleDb (Database.flush localDb visibleDb) := by
  sorry

/-- Archive guarantee bridge. -/
theorem archiveLogEffect_guarantee_final (i : Nat) :
    ∀ localDb visibleDb,
      txnSnapshotPost logSystemInv R_archive (archiveLogEffect (archiveTxnId i) i)
          localDb visibleDb →
        G_archive visibleDb (Database.flush localDb visibleDb) := by
  sorry

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
  intro localDb visibleDb hPost hVisInv
  exact selectAllLogEffect_guaranteeCore_final q localDb visibleDb hVisInv hPost

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
        (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).exec)
        (archiveTxnId i) logSystemInv SetLanguage.empty (archiveLogBody i)
        (archiveLogEffect (archiveTxnId i) i))
    (hQstable :
      Logic.stableBiAssertion
        (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).commit)
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
      globalValid_readCommitted_of_paperObligations_post
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
  archiveLogIndexedTxnSpec_of_paperObligations i
    (paperInfer_archiveLogBody_final i)
    (archiveLogEffect_qstable_final i)
    (archiveLogEffect_guarantee_final i)

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
