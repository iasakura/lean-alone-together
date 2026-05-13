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
  ∀ q (n : Nat), resultRowFor newDb q (n : Int) ↔ resultRowFor oldDb q (n : Int)

/-- `db` has no result rows for query `q`: no row in `db` has key
`(resultTable q, _)`. This is the freshness precondition for
`selectAllLogBody q`: the body's `.insert` of `resultRowLit q n` succeeds
only if `(resultTable q, n) ∉ db`, and we propagate this property through
the rely chain (`R_select q` = `G_insert ∨ G_archive`, neither of which
adds result rows). -/
def noResultRowsFor (q : Nat) (db : Database) : Prop :=
  ∀ row n, row ∈ db → row.key? ≠ some (resultTable q, n)

/-- `G_insert` / `G_archive` preserve the property "no rows at (resultTable q, _)
exist", because neither body adds rows at any `resultTable` key. -/
def preservesNoResultRows (oldDb newDb : Database) : Prop :=
  ∀ q : Nat, noResultRowsFor q oldDb → noResultRowsFor q newDb

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
        preservesWellFormedTableFields oldDb newDb ∧
        preservesNoResultRows oldDb newDb

def G_insert : Guarantee := G_insertCore

/-- `archiveLog` preserves `next` and may move `cut` forward to any point up to
`next`. Result rows are untouched.

The trailing `cut = cut' → newDb = oldDb` clause expresses that an
"archive step" with no actual compaction (cut frontier unchanged) is a no-op
at the list level. This is needed to derive `relyNoUndo` for `R_select q`,
where every round-trip step must have `cut` preserved (by monotonicity),
and hence collapses to identity. -/
def G_archiveCore : Guarantee :=
  fun oldDb newDb =>
    ∃ cut cut' next,
      storageShape oldDb cut next ∧
        cut ≤ cut' ∧
        cut' ≤ next ∧
        storageShape newDb cut' next ∧
        sameResultRows oldDb newDb ∧
        preservesWellFormedTableFields oldDb newDb ∧
        preservesNoResultRows oldDb newDb ∧
        (cut = cut' → newDb = oldDb)

def G_archive : Guarantee := G_archiveCore

/-- `selectAllLog q` does not change storage, leaves other query outputs alone,
and adds a prefix of the log stream visible in its snapshot.

The trailing `sameResultRows oldDb newDb → newDb = oldDb` clause expresses that
a select step preserving all result rows is the identity at the list level.
This is needed to derive `relyNoUndo` for `R_archive`: in a round-trip chain,
the result-row prefix grows monotonically in both directions, so it stays
constant; under the body's freshness invariant (`noResultRowsFor q` carried as
Ipre), each individual step has `sameResultRows` and is identity. -/
def G_selectCore (q : Nat) : Guarantee :=
  fun oldDb newDb =>
    sameStorageShape oldDb newDb ∧
      sameResultRowsExcept q oldDb newDb ∧
      preservesArchiveKeyFreshness oldDb newDb ∧
      preservesWellFormedTableFields oldDb newDb ∧
      (sameResultRows oldDb newDb → newDb = oldDb) ∧
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
    pre := fun db => logSystemInv db ∧ noResultRowsFor q db
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

/-- Under `archiveKeysFreshFrom i`, the archive key `(archiveTable, i)` is fresh:
no row in the database has that key. This is the static-freshness witness for
the archive-row `PaperInfer.insert` in `archiveLogBody`. -/
theorem archiveKeysFreshFrom_no_archive_at {db : Database} {i : Nat}
    (hFresh : archiveKeysFreshFrom i db) :
    ¬ Database.hasKey db (archiveTable, (i : Int)) := by
  intro hKey
  rcases List.mem_filterMap.mp hKey with ⟨row, hMem, hRowKey⟩
  exact hFresh i (Nat.le_refl i) row hMem hRowKey

/-! ## Invariant preservation lemmas -/

theorem G_insert_preserves_logSystemInv {oldDb newDb : Database}
    (hInv : logSystemInv oldDb) (hG : G_insert oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨_cut, _next, _hShape, hResults, hWF⟩
  rcases hCore with ⟨cut, next, _hOldShape, hNewShape, hSame, _hPreserve, hWFPreserve, _hPresNoRes⟩
  exact ⟨cut, next + 1, hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_archive_preserves_logSystemInv {oldDb newDb : Database}
    (hInv : logSystemInv oldDb) (hG : G_archive oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨_cut, _next, _hShape, hResults, hWF⟩
  rcases hCore with ⟨_cut, cut', next, _hOldShape, _hMono, _hBound, hNewShape, hSame, hWFPreserve, _hPresNoRes, _hCutEq⟩
  exact ⟨cut', next, hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_select_preserves_logSystemInv {oldDb newDb : Database} {q : Nat}
    (hInv : logSystemInv oldDb) (hG : G_select q oldDb newDb) :
    logSystemInv newDb := by
  have hCore := hG
  rcases hInv with ⟨cut, next, hShape, hResults, hWF⟩
  rcases hCore with ⟨hSameShape, hSameExcept, _hPreserve, hWFPreserve, _hSameResultsIdentity, k, hNewQ, _hExpanded⟩
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
  rcases hCore with ⟨_cut, cut', next', hOldShape, _hMono, _hBound, hNewShape, hSame, hWFPreserve, _hPresNoRes, _hCutEq⟩
  have hNext : next' = next := storageShape_next_unique hOldShape hShapeAt
  subst hNext
  exact ⟨cut', hNewShape, sameResultRows_resultPrefixAll hSame hResults, hWFPreserve hWF⟩

theorem G_select_preserves_logSystemInvAtNext {oldDb newDb : Database} {q next : Nat}
    (hInv : logSystemInvAtNext next oldDb) (hG : G_select q oldDb newDb) :
    logSystemInvAtNext next newDb := by
  rcases hInv with ⟨cut, hShape, hResults, hWF⟩
  have hCore := hG
  rcases hCore with ⟨hSameShape, hSameExcept, _hPreserve, hWFPreserve, _hSameResultsIdentity, k, hNewQ, _hExpanded⟩
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
  rcases hCore with ⟨cut, next', hOldShape, hNewShape, hSame, _hPreserve, hWFPreserve, _hPresNoRes⟩
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
  rcases hG with ⟨_cut, _next, _hOldShape, _hNewShape, _hSame, hPreserve, _hWFP, _hPresNoRes⟩
  exact preservesArchiveKeyFreshness_archiveKeysFreshFrom hPreserve hFresh

theorem G_select_preserves_archiveKeysFreshFrom {oldDb newDb : Database} {q start : Nat}
    (hInv : logSystemInv oldDb)
    (hFresh : archiveKeysFreshFrom start oldDb)
    (hG : G_select q oldDb newDb) :
    archiveKeysFreshFrom start newDb := by
  rcases hG with ⟨_hSameShape, _hSameExcept, hPreserve, _hWFP, _hSameResultsIdentity, _k, _hNewQ, _hExpanded⟩
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
  rcases hG with ⟨cut, next, hOldShape, hNewShape, _hSameResults, _hPreserve, _hWFP, _hPresNoRes⟩
  have hOld := (storageShape_expandedLog_iff hOldShape n).1 hExpanded
  exact (storageShape_expandedLog_iff hNewShape n).2 (by omega)

theorem G_archiveCore_preserves_expandedLog {oldDb newDb : Database} {n : Nat}
    (hG : G_archiveCore oldDb newDb)
    (hExpanded : expandedLog oldDb n) :
    expandedLog newDb n := by
  rcases hG with ⟨cut, cut', next, hOldShape, _hCutMono, _hCutBound, hNewShape, _hSameResults, _hWFP, _hPresNoRes, _hCutEq⟩
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
  rcases hG with ⟨hSameShape, _hSameResults, _hPreserve, _hWFP, _hSameResultsIdentity, _k, _hNewQ, _hExpanded⟩
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
  · rcases hInsert with ⟨c', n', hOldShape', hNewShape', _, _, _, _⟩
    have hCut : c' = cut := storageShape_cut_unique hOldShape' hOld
    have hNext : n' = next := storageShape_next_unique hOldShape' hOld
    subst hCut; subst hNext
    exact Or.inr hNewShape'
  · rcases hSelect with ⟨_q, hSelect⟩
    rcases hSelect with ⟨hSameShape, _⟩
    exact Or.inl ((hSameShape cut next).1 hOld)

/-- Each `R_archive` step preserves `cut` and either keeps or increments `next`.
This version doesn't require `logSystemInv` and is used by `relyNoUndo_R_archive`. -/
theorem R_archive_step_storageShape_no_inv {oldDb newDb : Database}
    (hStep : R_archive oldDb newDb)
    {cut next : Nat} (hOld : storageShape oldDb cut next) :
    storageShape newDb cut next ∨ storageShape newDb cut (next + 1) := by
  rcases hStep with hInsert | hSelect
  · rcases hInsert with ⟨c', n', hOldShape', hNewShape', _, _, _, _⟩
    have hCut : c' = cut := storageShape_cut_unique hOldShape' hOld
    have hNext : n' = next := storageShape_next_unique hOldShape' hOld
    subst hCut; subst hNext
    exact Or.inr hNewShape'
  · rcases hSelect with ⟨_q, hSelect⟩
    rcases hSelect with ⟨hSameShape, _⟩
    exact Or.inl ((hSameShape cut next).1 hOld)

/-- MultiStep variant of `R_archive_step_storageShape_no_inv`. -/
theorem R_archive_multiStep_storageShape_no_inv {oldDb newDb : Database}
    (hReach : Logic.MultiStep R_archive oldDb newDb)
    {cut next : Nat} (hOld : storageShape oldDb cut next) :
    ∃ next', next ≤ next' ∧ storageShape newDb cut next' := by
  induction hReach with
  | refl => exact ⟨next, Nat.le_refl _, hOld⟩
  | tail _hPrev hLast ih =>
      rcases ih with ⟨midNext, hMidLe, hMidShape⟩
      rcases R_archive_step_storageShape_no_inv hLast hMidShape with hSame | hAdv
      · exact ⟨midNext, hMidLe, hSame⟩
      · exact ⟨midNext + 1, by omega, hAdv⟩

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

/-! ## R_select_q storage-shape monotonicity (for relyNoUndo proof) -/

/-- Each `R_select q` step preserves cut and weakly advances next/cut. Specifically:
- `G_insert` requires `oldDb` to have shape (cut, next), and produces shape (cut, next+1).
- `G_archive` requires shape (cut, next), produces shape (cut', next) with cut ≤ cut' ≤ next. -/
theorem R_select_step_storageShape {q : Nat} {oldDb newDb : Database}
    (hStep : R_select q oldDb newDb)
    {cut next : Nat} (hOld : storageShape oldDb cut next) :
    ∃ cut' next', cut ≤ cut' ∧ next ≤ next' ∧ storageShape newDb cut' next' := by
  rcases hStep with hInsert | hArchive
  · rcases hInsert with ⟨c', n', hOldShape', hNewShape, _, _, _, _⟩
    have hCutEq : c' = cut := storageShape_cut_unique hOldShape' hOld
    have hNextEq : n' = next := storageShape_next_unique hOldShape' hOld
    refine ⟨cut, next + 1, Nat.le_refl _, ?_, ?_⟩
    · omega
    · rw [← hCutEq, ← hNextEq]; exact hNewShape
  · rcases hArchive with ⟨c', c'', n', hOldShape', hCutMono, _hCutBound, hNewShape, _, _, _, _⟩
    have hCutEq : c' = cut := storageShape_cut_unique hOldShape' hOld
    have hNextEq : n' = next := storageShape_next_unique hOldShape' hOld
    refine ⟨c'', next, ?_, Nat.le_refl _, ?_⟩
    · rw [← hCutEq]; exact hCutMono
    · rw [← hNextEq]; exact hNewShape

/-- MultiStep variant of `R_select_step_storageShape`. -/
theorem R_select_multiStep_storageShape {q : Nat} {oldDb newDb : Database}
    (hReach : Logic.MultiStep (R_select q) oldDb newDb)
    {cut next : Nat} (hOld : storageShape oldDb cut next) :
    ∃ cut' next', cut ≤ cut' ∧ next ≤ next' ∧ storageShape newDb cut' next' := by
  induction hReach with
  | refl => exact ⟨cut, next, Nat.le_refl _, Nat.le_refl _, hOld⟩
  | tail _hPrev hLast ih =>
      rcases ih with ⟨midCut, midNext, hCutLe, hNextLe, hMidShape⟩
      rcases R_select_step_storageShape hLast hMidShape with
        ⟨newCut, newNext, hNewCutLe, hNewNextLe, hNewShape⟩
      exact ⟨newCut, newNext, by omega, by omega, hNewShape⟩

/-- Without a storage shape, no `R_select q` step is possible (both `G_insert` and
`G_archive` require their `oldDb` to have a storage shape). -/
theorem R_select_step_requires_shape {q : Nat} {oldDb newDb : Database}
    (hStep : R_select q oldDb newDb) :
    ∃ cut next, storageShape oldDb cut next := by
  rcases hStep with hInsert | hArchive
  · rcases hInsert with ⟨cut, next, hShape, _, _, _, _, _⟩
    exact ⟨cut, next, hShape⟩
  · rcases hArchive with ⟨cut, _, next, hShape, _, _, _, _, _, _, _⟩
    exact ⟨cut, next, hShape⟩

/-- If `oldDb` has no storage shape, then any `R_select q` MultiStep from it is `refl`. -/
theorem R_select_multiStep_noShape {q : Nat} {oldDb newDb : Database}
    (hReach : Logic.MultiStep (R_select q) oldDb newDb)
    (hNoShape : ¬ ∃ cut next, storageShape oldDb cut next) :
    newDb = oldDb := by
  induction hReach with
  | refl => rfl
  | tail _hPrev hLast ih =>
      have hMidEq := ih
      subst hMidEq
      exact absurd (R_select_step_requires_shape hLast) hNoShape

/-- Under fixed storage shape (same cut, next at both ends), every step in an
`R_select q` MultiStep chain has `cut = cut'` (G_archive) and is therefore the identity. -/
theorem R_select_multiStep_identity_under_fixed_shape {q : Nat} {oldDb newDb : Database}
    {cut next : Nat}
    (hReach : Logic.MultiStep (R_select q) oldDb newDb)
    (hOld : storageShape oldDb cut next)
    (hNew : storageShape newDb cut next) :
    newDb = oldDb := by
  -- Strong induction: maintain a "current shape" parameter and show each step is identity.
  induction hReach with
  | refl => rfl
  | tail hPrev hLast ih =>
      -- midDb's shape: cut ≤ cutM, next ≤ nextM.
      rcases R_select_multiStep_storageShape hPrev hOld with
        ⟨cutM, nextM, hCutOM, hNextOM, hMidShape⟩
      -- From step: cutM ≤ cutN, nextM ≤ nextN. newDb has (cutN, nextN).
      rcases R_select_step_storageShape hLast hMidShape with
        ⟨cutN, nextN, hCutMN, hNextMN, hNewShape'⟩
      -- By uniqueness, (cutN, nextN) = (cut, next).
      have hCutN : cutN = cut := storageShape_cut_unique hNewShape' hNew
      have hNextN : nextN = next := storageShape_next_unique hNewShape' hNew
      -- Combined: cut ≤ cutM ≤ cutN = cut, so cutM = cut. Similarly nextM = next.
      have hCutM : cutM = cut := by omega
      have hNextM : nextM = next := by omega
      -- Rewrite midShape to have (cut, next).
      have hMidShape' := hMidShape
      rw [hCutM, hNextM] at hMidShape'
      -- IH: midDb = oldDb.
      have hMidEq := ih hMidShape'
      -- Step hLast: from midDb to newDb. Both have shape (cut, next). Use G_archive's clause.
      rcases hLast with hInsert | hArchive
      · exfalso
        rcases hInsert with ⟨c'', n'', hOldShape'', hNewShape'', _, _, _, _⟩
        have hN' : n'' = next := storageShape_next_unique hOldShape'' hMidShape'
        have hN'next : n'' + 1 = next := by
          have := storageShape_next_unique hNewShape'' hNew
          omega
        omega
      · rcases hArchive with ⟨c'', c''', n'', hOldShape'', _hCutMono, _hCutBound,
          hNewShape'', _hSame, _hWFP, _hPresNoRes, hCutEqImpl⟩
        have hC'' : c'' = cut := storageShape_cut_unique hOldShape'' hMidShape'
        have hN'' : n'' = next := storageShape_next_unique hOldShape'' hMidShape'
        have hC''' : c''' = cut := storageShape_cut_unique hNewShape'' hNew
        have hCutEqWit : c'' = c''' := by omega
        have hStepEq := hCutEqImpl hCutEqWit
        rw [hStepEq]; exact hMidEq

/-! ## Result-row preservation across `R_select q` -/

/-- Single-step result-row preservation under `R_select q`: both `G_insert` and
`G_archive` carry `sameResultRows`. -/
theorem R_select_step_preserves_resultRowFor {oldDb newDb : Database} {q : Nat}
    {q' : Nat} {n : Nat}
    (hStep : R_select q oldDb newDb) :
    resultRowFor oldDb q' (n : Int) ↔ resultRowFor newDb q' (n : Int) := by
  rcases hStep with hInsert | hArchive
  · rcases hInsert with ⟨_cut, _next, _hOldShape, _hNewShape, hSame, _, _, _⟩
    exact (hSame q' n).symm
  · rcases hArchive with ⟨_cut, _cut', _next, _hOldShape, _hMono, _hBound, _hNewShape,
      hSame, _hWFP, _hPresNoRes, _hCutEq⟩
    exact (hSame q' n).symm

/-- MultiStep result-row preservation under `R_select q`. -/
theorem R_select_multiStep_preserves_resultRowFor {oldDb newDb : Database} {q : Nat}
    {q' : Nat} {n : Nat}
    (hReach : Logic.MultiStep (R_select q) oldDb newDb) :
    resultRowFor oldDb q' (n : Int) ↔ resultRowFor newDb q' (n : Int) := by
  induction hReach with
  | refl => exact Iff.rfl
  | tail _hPrev hLast ih =>
      exact ih.trans (R_select_step_preserves_resultRowFor (q := q) (q' := q') (n := n) hLast)

/-- Single-step result-row preservation under `R_archive` at `Nat` positions.
For negative-id positions, the spec's iff doesn't constrain, so we use only
Nat positions in `relyNoUndo R_archive`. -/
theorem R_archive_step_monotone_resultRowFor_nat {oldDb newDb : Database}
    {q' : Nat} {n : Nat}
    (hStep : R_archive oldDb newDb) :
    resultRowFor oldDb q' (n : Int) → resultRowFor newDb q' (n : Int) := by
  rcases hStep with hInsert | hSelect
  · rcases hInsert with ⟨_cut, _next, _hOldShape, _hNewShape, hSame, _, _, _⟩
    exact fun h => (hSame q' n).mpr h
  · rcases hSelect with ⟨q'', hSelect⟩
    by_cases hEq : q' = q''
    · subst hEq
      rcases hSelect with ⟨_hSameShape, _hSameExcept, _, _, _, k, hIff, _⟩
      intro h
      exact (hIff n).mpr (Or.inl h)
    · rcases hSelect with ⟨_hSameShape, hSameExcept, _, _, _, _, _, _⟩
      intro h
      exact (hSameExcept q' (n : Int) hEq).mpr h

/-- MultiStep version of `R_archive_step_monotone_resultRowFor_nat`. -/
theorem R_archive_multiStep_monotone_resultRowFor_nat {oldDb newDb : Database}
    {q' n : Nat}
    (hReach : Logic.MultiStep R_archive oldDb newDb) :
    resultRowFor oldDb q' (n : Int) → resultRowFor newDb q' (n : Int) := by
  induction hReach with
  | refl => exact id
  | tail _hPrev hLast ih =>
      exact fun h => R_archive_step_monotone_resultRowFor_nat (q' := q') (n := n) hLast (ih h)

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
      Logic.GlobalValid (fun db => logSystemInv db ∧ noResultRowsFor q db) (R_select q)
        (selectAllLogTxn q) (G_select q) logSystemInv := by
    simpa [selectAllLogTxnSpec, txnSpecValid, txnSpecProgram, selectAllLogSpec,
      selectAllLogTxn] using hSelect
  have hSelect' :
      Logic.GlobalValid (fun db => logSystemInv db ∧ noResultRowsFor q db)
        (fun db db' => False ∨ (G_insert db db' ∨ G_archive db db'))
        (selectAllLogTxn q) (G_select q) logSystemInv :=
    Logic.globalValid_of_relySubset hSelectBase (by
      intro _ _ hStep
      rcases hStep with hFalse | hInsertArchive
      · cases hFalse
      · exact hInsertArchive)
  have hPar :
      Logic.GlobalValid
        (fun db => initialLogSystemInv db ∧ (logSystemInv db ∧ noResultRowsFor q db))
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
      rcases hInit with ⟨hDb, hInv⟩
      refine ⟨⟨hDb, hInv⟩, hInv, ?_⟩
      -- Show noResultRowsFor q db: db = initialDb has no result rows.
      subst hDb
      intro row n hMem hKey
      rw [mem_initialDb_iff] at hMem
      subst hMem
      rw [counterRow_key?] at hKey
      have : counterTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
      exact resultTable_ne_counterTable q this.symm) (by
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
