import DbAppProgramLogic.Transformer.LogStorageExample.Model

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Rely/guarantee specification for the log-storage example
-/

structure TxnSpec where
  body : Semantics.Program
  pre : Assertion
  post : Assertion
  R : Rely
  G : Guarantee

def sameResultRows (oldDb newDb : Database) : Prop :=
  ∀ q n, resultRowFor newDb q n ↔ resultRowFor oldDb q n

def sameResultRowsExcept (q : Nat) (oldDb newDb : Database) : Prop :=
  ∀ q' n, q' ≠ q → (resultRowFor newDb q' n ↔ resultRowFor oldDb q' n)

def sameStorageShape (oldDb newDb : Database) : Prop :=
  ∀ cut next, storageShape oldDb cut next ↔ storageShape newDb cut next

/-- Operations that do not write to the archive table preserve archive-key
freshness. With table-typed keys this is a structural fact, not the arithmetic
inequality of the previous design. -/
def preservesArchiveKeyFreshness (oldDb newDb : Database) : Prop :=
  ∀ i : Nat,
    (∀ row, row ∈ oldDb → row.key? ≠ some (archiveTable, (i : Int))) →
      (∀ row, row ∈ newDb → row.key? ≠ some (archiveTable, (i : Int)))

/-- The guarantees do not erase the explicit-tableField property of rows that
were already present, and any rows added by the local delta have their
`tableField` set. -/
def preservesWellFormedTableFields (oldDb newDb : Database) : Prop :=
  wellFormedTableFields oldDb → wellFormedTableFields newDb

/-- `insertLog` preserves the archived prefix and advances the generated-log
frontier by one. Result rows are untouched, archive table is untouched. -/
def G_insertCore : Guarantee :=
  fun oldDb newDb =>
    ∃ cut next,
      storageShape oldDb cut next ∧
        storageShape newDb cut (next + 1) ∧
        sameResultRows oldDb newDb ∧
        preservesArchiveKeyFreshness oldDb newDb ∧
        preservesWellFormedTableFields oldDb newDb

def G_insert : Guarantee := G_insertCore

/-- `archiveLog` preserves `next` and may move `cut` forward to any point up to
`next`. Result rows are untouched. -/
def G_archiveCore : Guarantee :=
  fun oldDb newDb =>
    ∃ cut cut' next,
      storageShape oldDb cut next ∧
        cut ≤ cut' ∧
        cut' ≤ next ∧
        storageShape newDb cut' next ∧
        sameResultRows oldDb newDb ∧
        preservesWellFormedTableFields oldDb newDb

def G_archive : Guarantee := G_archiveCore

/-- `selectAllLog q` does not change storage, leaves other query outputs alone,
and adds a prefix of the log stream visible in its snapshot. -/
def G_selectCore (q : Nat) : Guarantee :=
  fun oldDb newDb =>
    sameStorageShape oldDb newDb ∧
      sameResultRowsExcept q oldDb newDb ∧
      preservesArchiveKeyFreshness oldDb newDb ∧
      preservesWellFormedTableFields oldDb newDb ∧
      ∃ k : Nat,
        (∀ n : Nat, resultRowFor newDb q n ↔ resultRowFor oldDb q n ∨ n < k) ∧
          (∀ n : Nat, n < k → expandedLog oldDb n)

def G_select (q : Nat) : Guarantee := G_selectCore q

def R_insert : Rely :=
  fun oldDb newDb => G_archive oldDb newDb ∨ ∃ q, G_select q oldDb newDb

def R_archive : Rely :=
  fun oldDb newDb => G_insert oldDb newDb ∨ ∃ q, G_select q oldDb newDb

def R_select (_q : Nat) : Rely :=
  fun oldDb newDb => G_insert oldDb newDb ∨ G_archive oldDb newDb

def insertLogSpec (i : Nat) : TxnSpec :=
  { body := insertLogBody i
    pre := logSystemInv
    post := logSystemInv
    R := R_insert
    G := G_insert }

def archiveLogSpec (i : Nat) : TxnSpec :=
  { body := archiveLogBody i
    pre := logSystemInv
    post := logSystemInv
    R := R_archive
    G := G_archive }

def selectAllLogSpec (q : Nat) : TxnSpec :=
  { body := selectAllLogBody q
    pre := logSystemInv
    post := logSystemInv
    R := R_select q
    G := G_select q }

def insertLogIndexedSpec (i : Nat) : TxnSpec :=
  { body := insertLogBody i
    pre := logSystemInvAtNext i
    post := logSystemInvAtNext (i + 1)
    R := R_insert
    G := G_insert }

def archiveLogIndexedSpec (i : Nat) : TxnSpec :=
  { body := archiveLogBody i
    pre := fun db => logSystemInv db ∧ archiveKeysFreshFrom i db
    post := fun db => logSystemInv db ∧ archiveKeysFreshFrom (i + 1) db
    R := R_archive
    G := G_archive }

def txnSpecProgram (txnId : TxnId) (isolation : IsolationSpec Database)
    (spec : TxnSpec) : Semantics.Program :=
  .txn txnId isolation spec.body

def txnSpecValid (txnId : TxnId) (isolation : IsolationSpec Database)
    (spec : TxnSpec) : Prop :=
  Logic.GlobalValid spec.pre spec.R (txnSpecProgram txnId isolation spec) spec.G spec.post

def insertLogTxnSpec (i : Nat) : Prop :=
  txnSpecValid (insertTxnId i) (IsolationSpec.readCommitted Database) (insertLogSpec i)

def archiveLogTxnSpec (i : Nat) : Prop :=
  txnSpecValid (archiveTxnId i) IsolationSpec.snapshot (archiveLogSpec i)

def selectAllLogTxnSpec (q : Nat) : Prop :=
  txnSpecValid (selectTxnId q) IsolationSpec.snapshot (selectAllLogSpec q)

def insertLogIndexedTxnSpec (i : Nat) : Prop :=
  txnSpecValid (insertTxnId i) (IsolationSpec.readCommitted Database) (insertLogIndexedSpec i)

def archiveLogIndexedTxnSpec (i : Nat) : Prop :=
  txnSpecValid (archiveTxnId i) IsolationSpec.snapshot (archiveLogIndexedSpec i)

def G_system (q : Nat) : Guarantee :=
  fun oldDb newDb => G_insert oldDb newDb ∨ G_archive oldDb newDb ∨ G_select q oldDb newDb

def initialLogSystemInv : Assertion :=
  fun db => db = initialDb ∧ logSystemInv db

def logStorageFinalPost (q : Nat) : Assertion :=
  fun db => logSystemInv db ∧ resultPrefixFor db q

def logStorageProgramSpec (n m q : Nat) : Prop :=
  Logic.GlobalValid
    initialLogSystemInv
    (fun _ _ => False)
    (logStorageProgram n m q)
    (G_system q)
    (logStorageFinalPost q)

theorem logSystemInv_resultPrefixFor {db : Database} {q : Nat}
    (hInv : logSystemInv db) :
    resultPrefixFor db q := by
  rcases hInv with ⟨_cut, _next, _hShape, hResults, _hWF⟩
  exact hResults q

theorem initialLogSystemInv_initialDb :
    initialLogSystemInv initialDb :=
  ⟨rfl, logSystemInv_initialDb⟩

theorem sameResultRows_resultPrefixAll {oldDb newDb : Database}
    (hSame : sameResultRows oldDb newDb)
    (hResults : resultPrefixAll oldDb) :
    resultPrefixAll newDb := by
  intro q
  rcases hResults q with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  rw [hSame q n]
  exact hk n

theorem sameResultRowsExcept_resultPrefixFor {oldDb newDb : Database} {q q' : Nat}
    (hSame : sameResultRowsExcept q oldDb newDb)
    (hResults : resultPrefixFor oldDb q')
    (hNe : q' ≠ q) :
    resultPrefixFor newDb q' := by
  rcases hResults with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  rw [hSame q' n hNe]
  exact hk n

theorem resultPrefixFor_unionPrefix {oldDb newDb : Database} {q k : Nat}
    (hOld : resultPrefixFor oldDb q)
    (hNew : ∀ n : Nat, resultRowFor newDb q n ↔ resultRowFor oldDb q n ∨ n < k) :
    resultPrefixFor newDb q := by
  rcases hOld with ⟨oldK, hOld⟩
  refine ⟨max oldK k, ?_⟩
  intro n
  rw [hNew n, hOld n]
  omega

/-! ## Freshness lemmas (static, from invariant) -/

/-- Under `logSystemInvAtNext i`, the log key `(logTable, i)` is fresh: no row
in the database has that key. This is the static-freshness witness needed by
`PaperInfer.insert` for `logRecordExpr (.int i)`. -/
theorem logSystemInvAtNext_no_log_at_next {db : Database} {i : Nat}
    (hInv : logSystemInvAtNext i db) :
    ¬ Database.hasKey db (logTable, (i : Int)) := by
  rcases hInv with ⟨cut, hShape, _, _⟩
  rcases hShape with ⟨_hCut, _, _, _, hStorageLive, hLiveLog, _, _⟩
  intro hKey
  -- `hasKey db key` ↔ key ∈ db.filterMap Row.key? ↔ ∃ row ∈ db, row.key? = some key.
  rcases List.mem_filterMap.mp hKey with ⟨row, hMem, hRowKey⟩
  have hTable : rowInTable row logTable := rowInTable_of_key? hRowKey
  have hLive : liveRow row := hStorageLive row hMem (Or.inr (Or.inl hTable))
  have hLogAt : liveLog db (i : Int) := ⟨row, hMem, hLive, hRowKey⟩
  have hRange := (hLiveLog i).mp hLogAt
  omega

/-! ## Invariant preservation lemmas -/

theorem G_insert_preserves_logSystemInv {oldDb newDb : Database}
    (hInv : logSystemInv oldDb) (hG : G_insert oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨_cut, _next, _hShape, hResults, hWF⟩
  rcases hCore with ⟨cut, next, _hOldShape, hNewShape, hSame, _hPreserve, hWFPreserve⟩
  exact ⟨cut, next + 1, hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_archive_preserves_logSystemInv {oldDb newDb : Database}
    (hInv : logSystemInv oldDb) (hG : G_archive oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨_cut, _next, _hShape, hResults, hWF⟩
  rcases hCore with ⟨_cut, cut', next, _hOldShape, _hMono, _hBound, hNewShape, hSame, hWFPreserve⟩
  exact ⟨cut', next, hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_select_preserves_logSystemInv {oldDb newDb : Database} {q : Nat}
    (hInv : logSystemInv oldDb) (hG : G_select q oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨cut, next, hShape, hResults, hWF⟩
  rcases hCore with ⟨hSameShape, hSameExcept, _hPreserve, hWFPreserve, k, hNewQ, _hExpanded⟩
  refine ⟨cut, next, ?_, ?_, hWFPreserve hWF⟩
  · exact (hSameShape cut next).1 hShape
  · intro q'
    by_cases hEq : q' = q
    · subst q'
      exact resultPrefixFor_unionPrefix (hResults q) hNewQ
    · exact sameResultRowsExcept_resultPrefixFor hSameExcept (hResults q') hEq

/-! ## At-next invariant preservation -/

theorem G_archive_preserves_logSystemInvAtNext {oldDb newDb : Database} {next : Nat}
    (hInv : logSystemInvAtNext next oldDb) (hG : G_archive oldDb newDb) :
    logSystemInvAtNext next newDb := by
  rcases hInv with ⟨cutOld, hShapeAt, hResults, hWF⟩
  have hCore := hG
  rcases hCore with ⟨_cut, cut', next', hOldShape, _hMono, _hBound, hNewShape, hSame, hWFPreserve⟩
  have hNext : next' = next := storageShape_next_unique hOldShape hShapeAt
  subst hNext
  exact ⟨cut', hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_select_preserves_logSystemInvAtNext {oldDb newDb : Database} {q next : Nat}
    (hInv : logSystemInvAtNext next oldDb) (hG : G_select q oldDb newDb) :
    logSystemInvAtNext next newDb := by
  rcases hInv with ⟨cut, hShape, hResults, hWF⟩
  have hCore := hG
  rcases hCore with ⟨hSameShape, hSameExcept, _hPreserve, hWFPreserve, k, hNewQ, _hExpanded⟩
  refine ⟨cut, ?_, ?_, hWFPreserve hWF⟩
  · exact (hSameShape cut next).1 hShape
  · intro q'
    by_cases hEq : q' = q
    · subst q'
      exact resultPrefixFor_unionPrefix (hResults q) hNewQ
    · exact sameResultRowsExcept_resultPrefixFor hSameExcept (hResults q') hEq

theorem G_insert_preserves_logSystemInvAtNext_succ {oldDb newDb : Database}
    {next : Nat}
    (hInv : logSystemInvAtNext next oldDb) (hG : G_insert oldDb newDb) :
    logSystemInvAtNext (next + 1) newDb := by
  rcases hInv with ⟨cutOld, hShapeAt, hResults, hWF⟩
  have hCore := hG
  rcases hCore with ⟨cut, next', hOldShape, hNewShape, hSame, _hPreserve, hWFPreserve⟩
  have hNext : next' = next := storageShape_next_unique hOldShape hShapeAt
  subst hNext
  exact ⟨cut, hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

/-! ## Stability under relies -/

theorem logSystemInv_stable_R_insert :
    Logic.stableAssertion R_insert logSystemInv := by
  intro oldDb newDb hInv hStep
  rcases hStep with hArchive | hSelect
  · exact G_archive_preserves_logSystemInv hInv hArchive
  · rcases hSelect with ⟨_q, hSelect⟩
    exact G_select_preserves_logSystemInv hInv hSelect

theorem logSystemInv_stable_R_archive :
    Logic.stableAssertion R_archive logSystemInv := by
  intro oldDb newDb hInv hStep
  rcases hStep with hInsert | hSelect
  · exact G_insert_preserves_logSystemInv hInv hInsert
  · rcases hSelect with ⟨_q, hSelect⟩
    exact G_select_preserves_logSystemInv hInv hSelect

theorem logSystemInv_stable_R_select (q : Nat) :
    Logic.stableAssertion (R_select q) logSystemInv := by
  intro oldDb newDb hInv hStep
  rcases hStep with hInsert | hArchive
  · exact G_insert_preserves_logSystemInv hInv hInsert
  · exact G_archive_preserves_logSystemInv hInv hArchive

theorem logSystemInvAtNext_stable_R_insert (next : Nat) :
    Logic.stableAssertion R_insert (logSystemInvAtNext next) := by
  intro oldDb newDb hInv hStep
  rcases hStep with hArchive | hSelect
  · exact G_archive_preserves_logSystemInvAtNext hInv hArchive
  · rcases hSelect with ⟨_q, hSelect⟩
    exact G_select_preserves_logSystemInvAtNext hInv hSelect

theorem preservesArchiveKeyFreshness_archiveKeysFreshFrom {oldDb newDb : Database}
    {start : Nat}
    (hPreserve : preservesArchiveKeyFreshness oldDb newDb)
    (hFresh : archiveKeysFreshFrom start oldDb) :
    archiveKeysFreshFrom start newDb := by
  intro i hi row hMem
  exact hPreserve i (fun row' hMem' => hFresh i hi row' hMem') row hMem

theorem G_insert_preserves_archiveKeysFreshFrom {oldDb newDb : Database} {start : Nat}
    (hInv : logSystemInv oldDb)
    (hFresh : archiveKeysFreshFrom start oldDb)
    (hG : G_insert oldDb newDb) :
    archiveKeysFreshFrom start newDb := by
  rcases hG with ⟨_cut, _next, _hOldShape, _hNewShape, _hSame, hPreserve, _hWFP⟩
  exact preservesArchiveKeyFreshness_archiveKeysFreshFrom hPreserve hFresh

theorem G_select_preserves_archiveKeysFreshFrom {oldDb newDb : Database} {q start : Nat}
    (hInv : logSystemInv oldDb)
    (hFresh : archiveKeysFreshFrom start oldDb)
    (hG : G_select q oldDb newDb) :
    archiveKeysFreshFrom start newDb := by
  rcases hG with ⟨_hSameShape, _hSameExcept, hPreserve, _hWFP, _k, _hNewQ, _hExpanded⟩
  exact preservesArchiveKeyFreshness_archiveKeysFreshFrom hPreserve hFresh

theorem archiveIndexedInv_stable_R_archive (start : Nat) :
    Logic.stableAssertion R_archive
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom start db) := by
  intro oldDb newDb hInv hStep
  rcases hInv with ⟨hLogInv, hFresh⟩
  rcases hStep with hInsert | hSelect
  · exact
      ⟨ G_insert_preserves_logSystemInv hLogInv hInsert
      , G_insert_preserves_archiveKeysFreshFrom hLogInv hFresh hInsert
      ⟩
  · rcases hSelect with ⟨q, hSelect⟩
    exact
      ⟨ G_select_preserves_logSystemInv hLogInv hSelect
      , G_select_preserves_archiveKeysFreshFrom hLogInv hFresh hSelect
      ⟩

/-! ## ExpandedLog stability under relies -/

theorem G_insertCore_preserves_expandedLog {oldDb newDb : Database} {n : Nat}
    (hG : G_insertCore oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hG with ⟨cut, next, hOldShape, hNewShape, _hSameResults, _hPreserve, _hWFP⟩
  have hOld := (storageShape_expandedLog_iff hOldShape n).1 hExpanded
  exact (storageShape_expandedLog_iff hNewShape n).2 (by omega)

theorem G_archiveCore_preserves_expandedLog {oldDb newDb : Database} {n : Nat}
    (hG : G_archiveCore oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hG with ⟨cut, cut', next, hOldShape, _hCutMono, _hCutBound, hNewShape, _hSameResults, _hWFP⟩
  have hOld := (storageShape_expandedLog_iff hOldShape n).1 hExpanded
  exact (storageShape_expandedLog_iff hNewShape n).2 hOld

theorem sameStorageShape_preserves_expandedLog {oldDb newDb : Database}
    {cut next n : Nat}
    (hSameShape : sameStorageShape oldDb newDb)
    (hOldShape : storageShape oldDb cut next)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  have hNewShape : storageShape newDb cut next := (hSameShape cut next).1 hOldShape
  have hOld := (storageShape_expandedLog_iff hOldShape n).1 hExpanded
  exact (storageShape_expandedLog_iff hNewShape n).2 hOld

theorem G_selectCore_preserves_expandedLog {oldDb newDb : Database} {q n : Nat}
    {cut next : Nat}
    (hOldShape : storageShape oldDb cut next)
    (hG : G_selectCore q oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hG with ⟨hSameShape, _hSameResults, _hPreserve, _hWFP, _k, _hNewQ, _hExpanded⟩
  exact sameStorageShape_preserves_expandedLog hSameShape hOldShape hExpanded

theorem R_insert_preserves_expandedLog_step {oldDb newDb : Database} {n : Nat}
    (hInv : logSystemInv oldDb)
    (hStep : R_insert oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hStep with hArchive | hSelect
  · exact G_archiveCore_preserves_expandedLog hArchive hExpanded
  · rcases hSelect with ⟨q, hSelect⟩
    have hCore := hSelect
    rcases hInv with ⟨cut, next, hShape, _hResults, _hWF⟩
    exact G_selectCore_preserves_expandedLog (q := q) hShape hCore hExpanded

theorem R_archive_preserves_expandedLog_step {oldDb newDb : Database} {n : Nat}
    (hInv : logSystemInv oldDb)
    (hStep : R_archive oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hStep with hInsert | hSelect
  · exact G_insertCore_preserves_expandedLog hInsert hExpanded
  · rcases hSelect with ⟨q, hSelect⟩
    have hCore := hSelect
    rcases hInv with ⟨cut, next, hShape, _hResults, _hWF⟩
    exact G_selectCore_preserves_expandedLog (q := q) hShape hCore hExpanded

theorem R_select_preserves_expandedLog_step {oldDb newDb : Database} {q n : Nat}
    (hInv : logSystemInv oldDb)
    (hStep : R_select q oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hStep with hInsert | hArchive
  · exact G_insertCore_preserves_expandedLog hInsert hExpanded
  · exact G_archiveCore_preserves_expandedLog hArchive hExpanded

theorem logSystemInv_stable_multiStep {R : Rely} {oldDb newDb : Database}
    (hStable : Logic.stableAssertion R logSystemInv)
    (hReach : Logic.MultiStep R oldDb newDb)
    (hInv : logSystemInv oldDb) :
    logSystemInv newDb := by
  induction hReach with
  | refl => exact hInv
  | tail _hPrev hLast ih => exact hStable _ _ ih hLast

/-! ## R_archive preserves cut and only weakly increases next -/

/-- Each `R_archive` step preserves `cut` and either keeps or increments `next`. -/
theorem R_archive_step_storageShape {oldDb newDb : Database}
    (hStep : R_archive oldDb newDb)
    (hOldInv : logSystemInv oldDb)
    {cut next : Nat} (hOld : storageShape oldDb cut next) :
    storageShape newDb cut next ∨ storageShape newDb cut (next + 1) := by
  rcases hStep with hInsert | hSelect
  · rcases hInsert with ⟨c', n', hOldShape', hNewShape', _, _, _⟩
    have hCut : c' = cut := storageShape_cut_unique hOldShape' hOld
    have hNext : n' = next := storageShape_next_unique hOldShape' hOld
    subst hCut; subst hNext
    exact Or.inr hNewShape'
  · rcases hSelect with ⟨_q, hSelect⟩
    rcases hSelect with ⟨hSameShape, _⟩
    exact Or.inl ((hSameShape cut next).1 hOld)

/-- `R_archive` multi-steps preserve `cut` and weakly increase `next`. -/
theorem R_archive_multiStep_storageShape
    {snapDb visDb : Database}
    (hReach : Logic.MultiStep R_archive snapDb visDb)
    (hSnapInv : logSystemInv snapDb)
    {snapCut snapNext : Nat}
    (hSnapShape : storageShape snapDb snapCut snapNext) :
    ∃ visNext, snapNext ≤ visNext ∧ storageShape visDb snapCut visNext := by
  induction hReach with
  | refl => exact ⟨snapNext, Nat.le_refl _, hSnapShape⟩
  | tail hPrev hLast ih =>
      rcases ih with ⟨midNext, hMidLe, hMidShape⟩
      have hMidInv :=
        logSystemInv_stable_multiStep logSystemInv_stable_R_archive hPrev hSnapInv
      rcases R_archive_step_storageShape hLast hMidInv hMidShape with hSame | hAdv
      · exact ⟨midNext, hMidLe, hSame⟩
      · exact ⟨midNext + 1, by omega, hAdv⟩

theorem multiStep_preserves_expandedLog_of_step {R : Rely}
    {oldDb newDb : Database} {n : Nat}
    (hStable : Logic.stableAssertion R logSystemInv)
    (hStepPreserve :
      ∀ {db db' : Database},
        logSystemInv db → R db db' → expandedLog db n → expandedLog db' n)
    (hReach : Logic.MultiStep R oldDb newDb)
    (hInv : logSystemInv oldDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  induction hReach with
  | refl => exact hExpanded
  | tail hPrev hLast ih =>
      have hMidInv := logSystemInv_stable_multiStep hStable hPrev hInv
      exact hStepPreserve hMidInv hLast ih

theorem R_insert_multiStep_preserves_expandedLog {oldDb newDb : Database} {n : Nat}
    (hReach : Logic.MultiStep R_insert oldDb newDb)
    (hInv : logSystemInv oldDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n :=
  multiStep_preserves_expandedLog_of_step
    logSystemInv_stable_R_insert
    (fun {_db} {_db'} hInv hStep hExpanded =>
      R_insert_preserves_expandedLog_step hInv hStep hExpanded)
    hReach hInv hExpanded

theorem R_archive_multiStep_preserves_expandedLog {oldDb newDb : Database} {n : Nat}
    (hReach : Logic.MultiStep R_archive oldDb newDb)
    (hInv : logSystemInv oldDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n :=
  multiStep_preserves_expandedLog_of_step
    logSystemInv_stable_R_archive
    (fun {_db} {_db'} hInv hStep hExpanded =>
      R_archive_preserves_expandedLog_step hInv hStep hExpanded)
    hReach hInv hExpanded

theorem R_select_multiStep_preserves_expandedLog {oldDb newDb : Database} {q n : Nat}
    (hReach : Logic.MultiStep (R_select q) oldDb newDb)
    (hInv : logSystemInv oldDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n :=
  multiStep_preserves_expandedLog_of_step
    (logSystemInv_stable_R_select q)
    (fun {_db} {_db'} hInv hStep hExpanded =>
      R_select_preserves_expandedLog_step hInv hStep hExpanded)
    hReach hInv hExpanded

theorem G_system_preserves_logSystemInv {oldDb newDb : Database} {q : Nat}
    (hInv : logSystemInv oldDb) (hG : G_system q oldDb newDb) :
    logSystemInv newDb := by
  rcases hG with hInsert | hArchive | hSelect
  · exact G_insert_preserves_logSystemInv hInv hInsert
  · exact G_archive_preserves_logSystemInv hInv hArchive
  · exact G_select_preserves_logSystemInv hInv hSelect

theorem G_system_preserves_logStorageFinalPost {oldDb newDb : Database} {q : Nat}
    (hInv : logSystemInv oldDb) (hG : G_system q oldDb newDb) :
    logStorageFinalPost q newDb := by
  have hNewInv := G_system_preserves_logSystemInv hInv hG
  exact ⟨hNewInv, logSystemInv_resultPrefixFor hNewInv⟩

/-! ## Worker composition -/

theorem insertWorkerFrom_valid_of_indexedTxnSpecs (start count : Nat)
    (hInsert : ∀ i, insertLogIndexedTxnSpec i) :
    Logic.GlobalValid (logSystemInvAtNext start) R_insert
      (insertWorkerFrom start count) G_insert (logSystemInvAtNext (start + count)) := by
  induction count generalizing start with
  | zero =>
      simpa [insertWorkerFrom_zero, Nat.add_zero] using
        (Logic.globalValid_skip
          (I := logSystemInvAtNext start) (R := R_insert) (G := G_insert)
          (logSystemInvAtNext_stable_R_insert start))
  | succ count ih =>
      rw [insertWorkerFrom_succ]
      have hHead :
          Logic.GlobalValid (logSystemInvAtNext start) R_insert
            (insertLogTxn start) G_insert (logSystemInvAtNext (start + 1)) := by
        simpa [insertLogIndexedTxnSpec, txnSpecValid, txnSpecProgram,
          insertLogIndexedSpec, insertLogTxn] using hInsert start
      cases count with
      | zero =>
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hHead
      | succ count' =>
          have hTail :
              Logic.GlobalValid (logSystemInvAtNext (start + 1)) R_insert
                (insertWorkerFrom (start + 1) (count' + 1)) G_insert
                (logSystemInvAtNext ((start + 1) + (count' + 1))) :=
            ih (start + 1)
          have hSeq :
              Logic.GlobalValid (logSystemInvAtNext start) R_insert
                (.seq (insertLogTxn start) (insertWorkerFrom (start + 1) (count' + 1)))
                (fun db db' => G_insert db db' ∨ G_insert db db')
                (logSystemInvAtNext ((start + 1) + (count' + 1))) :=
            Logic.globalValid_seq hHead hTail
          have hSeq' :
              Logic.GlobalValid (logSystemInvAtNext start) R_insert
                (.seq (insertLogTxn start) (insertWorkerFrom (start + 1) (count' + 1)))
                G_insert
                (logSystemInvAtNext ((start + 1) + (count' + 1))) :=
            Logic.globalValid_conseq hSeq (fun _ h => h) (by
              intro _ _ hG; rcases hG with hG | hG <;> exact hG)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hSeq'

theorem insertWorker_valid_of_indexedTxnSpecs (n : Nat)
    (hInsert : ∀ i, insertLogIndexedTxnSpec i) :
    Logic.GlobalValid (logSystemInvAtNext 0) R_insert
      (insertWorker n) G_insert (logSystemInvAtNext n) := by
  rw [insertWorker_eq_insertWorkerFrom]
  simpa using insertWorkerFrom_valid_of_indexedTxnSpecs 0 n hInsert

theorem archiveWorkerFrom_valid_of_indexedTxnSpecs (start count : Nat)
    (hArchive : ∀ i, archiveLogIndexedTxnSpec i) :
    Logic.GlobalValid
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom start db)
      R_archive
      (archiveWorkerFrom start count)
      G_archive
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom (start + count) db) := by
  induction count generalizing start with
  | zero =>
      simpa [archiveWorkerFrom_zero, Nat.add_zero] using
        (Logic.globalValid_skip
          (I := fun db => logSystemInv db ∧ archiveKeysFreshFrom start db)
          (R := R_archive) (G := G_archive)
          (archiveIndexedInv_stable_R_archive start))
  | succ count ih =>
      rw [archiveWorkerFrom_succ]
      have hHead :
          Logic.GlobalValid
            (fun db => logSystemInv db ∧ archiveKeysFreshFrom start db)
            R_archive
            (archiveLogTxn start)
            G_archive
            (fun db => logSystemInv db ∧ archiveKeysFreshFrom (start + 1) db) := by
        simpa [archiveLogIndexedTxnSpec, txnSpecValid, txnSpecProgram,
          archiveLogIndexedSpec, archiveLogTxn] using hArchive start
      cases count with
      | zero =>
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hHead
      | succ count' =>
          have hTail :
              Logic.GlobalValid
                (fun db => logSystemInv db ∧ archiveKeysFreshFrom (start + 1) db)
                R_archive
                (archiveWorkerFrom (start + 1) (count' + 1))
                G_archive
                (fun db => logSystemInv db ∧
                  archiveKeysFreshFrom ((start + 1) + (count' + 1)) db) :=
            ih (start + 1)
          have hSeq :
              Logic.GlobalValid
                (fun db => logSystemInv db ∧ archiveKeysFreshFrom start db)
                R_archive
                (.seq (archiveLogTxn start) (archiveWorkerFrom (start + 1) (count' + 1)))
                (fun db db' => G_archive db db' ∨ G_archive db db')
                (fun db => logSystemInv db ∧
                  archiveKeysFreshFrom ((start + 1) + (count' + 1)) db) :=
            Logic.globalValid_seq hHead hTail
          have hSeq' :
              Logic.GlobalValid
                (fun db => logSystemInv db ∧ archiveKeysFreshFrom start db)
                R_archive
                (.seq (archiveLogTxn start) (archiveWorkerFrom (start + 1) (count' + 1)))
                G_archive
                (fun db => logSystemInv db ∧
                  archiveKeysFreshFrom ((start + 1) + (count' + 1)) db) :=
            Logic.globalValid_conseq hSeq (fun _ h => h) (by
              intro _ _ hG; rcases hG with hG | hG <;> exact hG)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hSeq'

theorem archiveWorker_valid_of_indexedTxnSpecs (m : Nat)
    (hArchive : ∀ i, archiveLogIndexedTxnSpec i) :
    Logic.GlobalValid
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom 0 db)
      R_archive
      (archiveWorker m)
      G_archive
      (fun db => logSystemInv db ∧ archiveKeysFreshFrom m db) := by
  rw [archiveWorker_eq_archiveWorkerFrom]
  simpa using archiveWorkerFrom_valid_of_indexedTxnSpecs 0 m hArchive

theorem insertArchiveWorkers_valid_of_indexedTxnSpecs (n m q : Nat)
    (hInsert : ∀ i, insertLogIndexedTxnSpec i)
    (hArchive : ∀ i, archiveLogIndexedTxnSpec i) :
    Logic.GlobalValid initialLogSystemInv (G_select q)
      (.par (insertWorker n) (archiveWorker m))
      (fun db db' => G_insert db db' ∨ G_archive db db') logSystemInv := by
  have hInsertBase := insertWorker_valid_of_indexedTxnSpecs n hInsert
  have hArchiveBase := archiveWorker_valid_of_indexedTxnSpecs m hArchive
  have hInsert' :
      Logic.GlobalValid (logSystemInvAtNext 0)
        (fun db db' => G_select q db db' ∨ G_archive db db')
        (insertWorker n) G_insert (logSystemInvAtNext n) :=
    Logic.globalValid_of_relySubset hInsertBase (by
      intro _ _ hStep
      rcases hStep with hSelect | hArchive
      · exact Or.inr ⟨q, hSelect⟩
      · exact Or.inl hArchive)
  have hArchive' :
      Logic.GlobalValid
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom 0 db)
        (fun db db' => G_select q db db' ∨ G_insert db db')
        (archiveWorker m) G_archive
        (fun db => logSystemInv db ∧ archiveKeysFreshFrom m db) :=
    Logic.globalValid_of_relySubset hArchiveBase (by
      intro _ _ hStep
      rcases hStep with hSelect | hInsert
      · exact Or.inr ⟨q, hSelect⟩
      · exact Or.inl hInsert)
  have hPar :
      Logic.GlobalValid
        (fun db => logSystemInvAtNext 0 db ∧
          (logSystemInv db ∧ archiveKeysFreshFrom 0 db))
        (G_select q)
        (.par (insertWorker n) (archiveWorker m))
        (fun db db' => G_insert db db' ∨ G_archive db db')
        (fun db => logSystemInvAtNext n db ∧
          (logSystemInv db ∧ archiveKeysFreshFrom m db)) :=
    Logic.globalValid_par2 hInsert' hArchive'
  have hParPre :
      Logic.GlobalValid initialLogSystemInv (G_select q)
        (.par (insertWorker n) (archiveWorker m))
        (fun db db' => G_insert db db' ∨ G_archive db db')
        (fun db => logSystemInvAtNext n db ∧
          (logSystemInv db ∧ archiveKeysFreshFrom m db)) :=
    Logic.globalValid_conseq hPar (by
      intro db hInit
      rcases hInit with ⟨hDb, _hInv⟩
      subst hDb
      exact
        ⟨ logSystemInvAtNext_initialDb
        , logSystemInv_initialDb
        , archiveKeysFreshFrom_initialDb 0
        ⟩) (by
      intro _ _ hG
      exact hG)
  exact Logic.globalValid_post_conseq hParPre (fun _ hPost => hPost.2.1)

theorem logStorageProgramSpec_of_indexedTxnSpecs (n m q : Nat)
    (hInsert : ∀ i, insertLogIndexedTxnSpec i)
    (hArchive : ∀ i, archiveLogIndexedTxnSpec i)
    (hSelect : selectAllLogTxnSpec q) :
    logStorageProgramSpec n m q := by
  have hInsertArchive :=
    insertArchiveWorkers_valid_of_indexedTxnSpecs n m q hInsert hArchive
  have hInsertArchive' :
      Logic.GlobalValid initialLogSystemInv
        (fun db db' => False ∨ G_select q db db')
        (.par (insertWorker n) (archiveWorker m))
        (fun db db' => G_insert db db' ∨ G_archive db db') logSystemInv :=
    Logic.globalValid_of_relySubset hInsertArchive (by
      intro _ _ hStep
      rcases hStep with hFalse | hSelectStep
      · cases hFalse
      · exact hSelectStep)
  have hSelectBase :
      Logic.GlobalValid logSystemInv (R_select q) (selectAllLogTxn q)
        (G_select q) logSystemInv := by
    simpa [selectAllLogTxnSpec, txnSpecValid, txnSpecProgram, selectAllLogSpec,
      selectAllLogTxn] using hSelect
  have hSelect' :
      Logic.GlobalValid logSystemInv
        (fun db db' => False ∨ (G_insert db db' ∨ G_archive db db'))
        (selectAllLogTxn q) (G_select q) logSystemInv :=
    Logic.globalValid_of_relySubset hSelectBase (by
      intro _ _ hStep
      rcases hStep with hFalse | hInsertArchive
      · cases hFalse
      · exact hInsertArchive)
  have hPar :
      Logic.GlobalValid
        (fun db => initialLogSystemInv db ∧ logSystemInv db)
        (fun _ _ => False)
        (.par (.par (insertWorker n) (archiveWorker m)) (selectAllLogTxn q))
        (fun db db' =>
          (G_insert db db' ∨ G_archive db db') ∨ G_select q db db')
        (fun db => logSystemInv db ∧ logSystemInv db) :=
    Logic.globalValid_par2 hInsertArchive' hSelect'
  have hParPre :
      Logic.GlobalValid initialLogSystemInv
        (fun _ _ => False)
        (logStorageProgram n m q)
        (fun db db' =>
          (G_insert db db' ∨ G_archive db db') ∨ G_select q db db')
        (fun db => logSystemInv db ∧ logSystemInv db) :=
    Logic.globalValid_conseq (by
      simpa [logStorageProgram] using hPar) (by
      intro db hInit
      exact ⟨hInit, hInit.2⟩) (by
      intro _ _ hG
      exact hG)
  have hPost :
      Logic.GlobalValid initialLogSystemInv
        (fun _ _ => False)
        (logStorageProgram n m q)
        (fun db db' =>
          (G_insert db db' ∨ G_archive db db') ∨ G_select q db db')
        (logStorageFinalPost q) :=
    Logic.globalValid_post_conseq hParPre (by
      intro _ hInvs
      exact ⟨hInvs.1, logSystemInv_resultPrefixFor hInvs.1⟩)
  exact Logic.globalValid_conseq hPost (fun _ h => h) (by
    intro _ _ hStep
    rcases hStep with hInsertArchiveStep | hSelectStep
    · rcases hInsertArchiveStep with hInsertStep | hArchiveStep
      · exact Or.inl hInsertStep
      · exact Or.inr (Or.inl hArchiveStep)
    · exact Or.inr (Or.inr hSelectStep))

theorem logStorageProgramSpec_finalPost {n m q : Nat} {db : Database}
    {finalCfg : GlobalConfig}
    (hSpec : logStorageProgramSpec n m q)
    (hInit : initialLogSystemInv db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False) ⟨logStorageProgram n m q, db⟩ finalCfg)
    (hDone : Logic.ProgramDone finalCfg.program) :
    logStorageFinalPost q finalCfg.globalDb :=
  (hSpec db hInit).1 finalCfg hRun hDone

theorem logStorageProgramSpec_resultPrefix {n m q : Nat} {db : Database}
    {finalCfg : GlobalConfig}
    (hSpec : logStorageProgramSpec n m q)
    (hInit : initialLogSystemInv db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False) ⟨logStorageProgram n m q, db⟩ finalCfg)
    (hDone : Logic.ProgramDone finalCfg.program) :
    resultPrefixFor finalCfg.globalDb q :=
  (logStorageProgramSpec_finalPost hSpec hInit hRun hDone).2

end LogStorageExample

end Transformer

end DbAppProgramLogic
