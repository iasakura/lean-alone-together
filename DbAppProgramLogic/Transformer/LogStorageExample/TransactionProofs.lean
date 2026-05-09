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

/-- Indexed `PaperInfer` derivation for `archiveLogBody` against the
strengthened invariant `logSystemInv ∧ archiveKeysFreshFrom i`. The
strengthening lets the guarantee bridge know archive-id `i` is fresh in the
visible database. -/
theorem paperInfer_archiveLogBody_indexed_final (i : Nat) :
    PaperInfer
      (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).exec)
      (archiveTxnId i)
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
      SetLanguage.empty (archiveLogBody i)
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

theorem archiveLogIndexedEffect_qstable_final (i : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        R_archive (archiveLogEffect (archiveTxnId i) i)) :=
  txnSnapshotPost_stable_readCommitted (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
    R_archive (archiveLogEffect (archiveTxnId i) i)

theorem selectAllLogEffect_qstable_final (q : Nat) :
    Logic.stableBiAssertion
      (Logic.relyMod (R_select q) (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost logSystemInv (R_select q) (selectAllLogEffect (selectTxnId q) q)) :=
  txnSnapshotPost_stable_readCommitted logSystemInv (R_select q)
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
  intro localDb visibleDb hPost _hVisInv
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
  intro localDb visibleDb hPost hVisInv
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
  have hVisLogInv : logSystemInv visibleDb := hVisInv
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
      sorry
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
        · -- snapCut ≤ n < snapNext: need local archive insert
          have hCase' : snapCut ≤ n := by omega
          -- This requires constructing the local archive row when snap had logs.
          -- Construction needs finite-set reasoning for selectedLogMin/Max.
          sorry
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

/-- Indexed archive wrapper that threads `archiveKeysFreshFrom i` into the
PaperInfer invariant. The bridge therefore receives a snapshot post over the
strengthened invariant `logSystemInv ∧ archiveKeysFreshFrom i`, which in turn
gives visible's freshness for the storage-shape transition (no archive-id
collision means the local archive row purely extends archive coverage). -/
theorem archiveLogIndexedTxnSpec_of_indexedPaperObligations (i : Nat)
    (hInfer :
      PaperInfer
        (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).exec)
        (archiveTxnId i)
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
        SetLanguage.empty (archiveLogBody i)
        (archiveLogEffect (archiveTxnId i) i))
    (hQstable :
      Logic.stableBiAssertion
        (Logic.relyMod R_archive (IsolationSpec.readCommitted Database).commit)
        (txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
          R_archive (archiveLogEffect (archiveTxnId i) i)))
    (hGuarantee :
      ∀ localDb visibleDb,
        txnSnapshotPost (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db)
            R_archive (archiveLogEffect (archiveTxnId i) i) localDb visibleDb →
          G_archive visibleDb (Database.flush localDb visibleDb)) :
    archiveLogIndexedTxnSpec i := by
  let hObligations :
      TxnPaperObligations R_archive
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom i db) G_archive
        (archiveTxnId i) (archiveLogBody i) :=
    { effect := archiveLogEffect (archiveTxnId i) i
      infer := hInfer
      qstable := hQstable
      guarantee := hGuarantee }
  simpa [archiveLogIndexedTxnSpec, txnSpecValid, txnSpecProgram,
    archiveLogIndexedSpec, archiveLogTxn]
    using
      globalValid_readCommitted_of_paperObligations_post
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
