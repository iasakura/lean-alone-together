import DbAppProgramLogic.ReadableSyntax
import DbAppProgramLogic.Logic

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Log storage / archive example — table-first model

This rewrite drops the old `kindField`-vs-`tableField` duplication and the
`archiveId i = -((i : Int) + 2)` arithmetic encoding. Every record carries an
explicit `tableField`, and the `idField` is the identity within its table.

* `counterTable`, `logTable`, `archiveTable`, `resultTable q` are pairwise
  disjoint table names.
* The counter is a singleton at `(counterTable, 0)`.
* Log row `n` lives at `(logTable, n)`.
* Archive row `i` lives at `(archiveTable, i)` and stores an interval
  `[lo, hi)`.
* Result row for query `q` and log number `n` lives at `(resultTable q, n)`.
-/

/-! ## Tables and fields -/

def counterTable : TableName := 1
def logTable     : TableName := 2
def archiveTable : TableName := 3
def resultTable (q : Nat) : TableName := ((100 + q : Nat) : Int)

theorem counterTable_ne_logTable : counterTable ≠ logTable := by
  unfold counterTable logTable; decide

theorem counterTable_ne_archiveTable : counterTable ≠ archiveTable := by
  unfold counterTable archiveTable; decide

theorem logTable_ne_archiveTable : logTable ≠ archiveTable := by
  unfold logTable archiveTable; decide

theorem resultTable_ne_counterTable (q : Nat) : resultTable q ≠ counterTable := by
  intro h
  unfold resultTable counterTable at h
  have : (100 + q : Nat) = 1 := by exact_mod_cast h
  omega

theorem resultTable_ne_logTable (q : Nat) : resultTable q ≠ logTable := by
  intro h
  unfold resultTable logTable at h
  have : (100 + q : Nat) = 2 := by exact_mod_cast h
  omega

theorem resultTable_ne_archiveTable (q : Nat) : resultTable q ≠ archiveTable := by
  intro h
  unfold resultTable archiveTable at h
  have : (100 + q : Nat) = 3 := by exact_mod_cast h
  omega

theorem resultTable_injective {q q' : Nat} (h : resultTable q = resultTable q') : q = q' := by
  unfold resultTable at h
  have : (100 + q : Nat) = 100 + q' := by exact_mod_cast h
  omega

def tableField : FieldName := "table"
def idField    : FieldName := "id"
def nextField  : FieldName := "next"
def loField    : FieldName := "lo"
def hiField    : FieldName := "hi"

/-! ## Concrete record literals -/

def counterRecord (next : Int) : RecordLit :=
  ⟨[(tableField, .int counterTable), (idField, .int 0), (nextField, .int next)]⟩

def logRecord (n : Int) : RecordLit :=
  ⟨[(tableField, .int logTable), (idField, .int n)]⟩

def archiveRecord (i : Nat) (lo hi : Int) : RecordLit :=
  ⟨[(tableField, .int archiveTable), (idField, .int i),
    (loField, .int lo), (hiField, .int hi)]⟩

def resultRecord (q : Nat) (n : Int) : RecordLit :=
  ⟨[(tableField, .int (resultTable q)), (idField, .int n)]⟩

def counterRow (txnId : TxnId) (next : Int) : Row :=
  Row.fromInsert txnId (counterRecord next)

def logRow (txnId : TxnId) (n : Int) : Row :=
  Row.fromInsert txnId (logRecord n)

def archiveRow (txnId : TxnId) (i : Nat) (lo hi : Int) : Row :=
  Row.fromInsert txnId (archiveRecord i lo hi)

def resultRowLit (txnId : TxnId) (q : Nat) (n : Int) : Row :=
  Row.fromInsert txnId (resultRecord q n)

/-! ## Record key/id facts -/

theorem counterRecord_key? (next : Int) :
    (counterRecord next).key? = some (counterTable, 0) := by
  simp [counterRecord, RecordLit.key?, RecordLit.table?, RecordLit.id?,
    RecordLit.lookup?, tableField, idField, nextField]

theorem logRecord_key? (n : Int) :
    (logRecord n).key? = some (logTable, n) := by
  simp [logRecord, RecordLit.key?, RecordLit.table?, RecordLit.id?,
    RecordLit.lookup?, tableField, idField]

theorem archiveRecord_key? (i : Nat) (lo hi : Int) :
    (archiveRecord i lo hi).key? = some (archiveTable, (i : Int)) := by
  simp [archiveRecord, RecordLit.key?, RecordLit.table?, RecordLit.id?,
    RecordLit.lookup?, tableField, idField, loField, hiField]

theorem resultRecord_key? (q : Nat) (n : Int) :
    (resultRecord q n).key? = some (resultTable q, n) := by
  simp [resultRecord, RecordLit.key?, RecordLit.table?, RecordLit.id?,
    RecordLit.lookup?, tableField, idField]

theorem counterRow_key? (txnId : TxnId) (next : Int) :
    (counterRow txnId next).key? = some (counterTable, 0) := by
  simp [counterRow, Row.key?, Row.fromInsert, counterRecord_key?]

theorem logRow_key? (txnId : TxnId) (n : Int) :
    (logRow txnId n).key? = some (logTable, n) := by
  simp [logRow, Row.key?, Row.fromInsert, logRecord_key?]

theorem archiveRow_key? (txnId : TxnId) (i : Nat) (lo hi : Int) :
    (archiveRow txnId i lo hi).key? = some (archiveTable, (i : Int)) := by
  simp [archiveRow, Row.key?, Row.fromInsert, archiveRecord_key?]

theorem resultRowLit_key? (txnId : TxnId) (q : Nat) (n : Int) :
    (resultRowLit txnId q n).key? = some (resultTable q, n) := by
  simp [resultRowLit, Row.key?, Row.fromInsert, resultRecord_key?]

/-! ## Field projection from concrete records -/

def rowFieldInt? (row : Row) (field : FieldName) : Option Int :=
  match row.visible.lookup? field with
  | some (.int value) => some value
  | _ => none

theorem rowFieldInt?_idField_eq_id? (row : Row) :
    rowFieldInt? row idField = row.id? := by
  unfold rowFieldInt? idField Row.id? RecordLit.id?
  rfl

theorem rowFieldInt?_idField_of_key {row : Row} {table : TableName} {id : Int}
    (h : row.key? = some (table, id)) :
    rowFieldInt? row idField = some id := by
  rw [rowFieldInt?_idField_eq_id?]
  unfold Row.key? RecordLit.key? at h
  cases hT : row.visible.table? with
  | none => rw [hT] at h; cases h
  | some t =>
    cases hI : row.visible.id? with
    | none => rw [hT, hI] at h; cases h
    | some idVal =>
      rw [hT, hI] at h
      simp at h
      simp [Row.id?, hI, h.2]

/-- If a row has explicit `tableField` and `idField` integer fields, its key
agrees. Used to bridge effect-denotation reasoning (which works on field
lookups) with key-based predicates. -/
theorem rowKey?_of_table_id_fields {row : Row} {table : TableName} {id : Int}
    (hTable : rowFieldInt? row tableField = some table)
    (hId : rowFieldInt? row idField = some id) :
    row.key? = some (table, id) := by
  unfold rowFieldInt? at hTable hId
  unfold tableField at hTable
  unfold idField at hId
  unfold Row.key? RecordLit.key? RecordLit.table? RecordLit.id?
  cases hT : row.visible.lookup? "table" with
  | none => rw [hT] at hTable; cases hTable
  | some litT =>
    cases litT with
    | bool _ => rw [hT] at hTable; cases hTable
    | int v =>
      rw [hT] at hTable; simp at hTable
      cases hI : row.visible.lookup? "id" with
      | none => rw [hI] at hId; cases hId
      | some litI =>
        cases litI with
        | bool _ => rw [hI] at hId; cases hId
        | int w =>
          rw [hI] at hId; simp at hId
          subst hTable; subst hId
          simp [hT, hI]

theorem rowFieldInt?_counterRow_next (txnId : TxnId) (next : Int) :
    rowFieldInt? (counterRow txnId next) nextField = some next := by
  simp [rowFieldInt?, counterRow, counterRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField, nextField]

theorem rowFieldInt?_archiveRow_lo (txnId : TxnId) (i : Nat) (lo hi : Int) :
    rowFieldInt? (archiveRow txnId i lo hi) loField = some lo := by
  simp [rowFieldInt?, archiveRow, archiveRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField, loField, hiField]

theorem rowFieldInt?_counterRow_table (txnId : TxnId) (next : Int) :
    rowFieldInt? (counterRow txnId next) tableField = some counterTable := by
  simp [rowFieldInt?, counterRow, counterRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField, nextField]

theorem rowFieldInt?_logRow_table (txnId : TxnId) (n : Int) :
    rowFieldInt? (logRow txnId n) tableField = some logTable := by
  simp [rowFieldInt?, logRow, logRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField]

theorem rowFieldInt?_archiveRow_table (txnId : TxnId) (i : Nat) (lo hi : Int) :
    rowFieldInt? (archiveRow txnId i lo hi) tableField = some archiveTable := by
  simp [rowFieldInt?, archiveRow, archiveRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField, loField, hiField]

theorem rowFieldInt?_resultRowLit_table (txnId : TxnId) (q : Nat) (n : Int) :
    rowFieldInt? (resultRowLit txnId q n) tableField = some (resultTable q) := by
  simp [rowFieldInt?, resultRowLit, resultRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField]

theorem rowFieldInt?_archiveRow_hi (txnId : TxnId) (i : Nat) (lo hi : Int) :
    rowFieldInt? (archiveRow txnId i lo hi) hiField = some hi := by
  simp [rowFieldInt?, archiveRow, archiveRecord, Row.fromInsert,
    RecordLit.lookup?, tableField, idField, loField, hiField]

/-! ## Table-membership predicate -/

def rowInTable (row : Row) (table : TableName) : Prop :=
  ∃ id, row.key? = some (table, id)

theorem rowInTable_of_key? {row : Row} {table : TableName} {id : Int}
    (h : row.key? = some (table, id)) : rowInTable row table :=
  ⟨id, h⟩

theorem rowInTable_counterRow (txnId : TxnId) (next : Int) :
    rowInTable (counterRow txnId next) counterTable :=
  ⟨0, counterRow_key? txnId next⟩

theorem rowInTable_logRow (txnId : TxnId) (n : Int) :
    rowInTable (logRow txnId n) logTable :=
  ⟨n, logRow_key? txnId n⟩

theorem rowInTable_archiveRow (txnId : TxnId) (i : Nat) (lo hi : Int) :
    rowInTable (archiveRow txnId i lo hi) archiveTable :=
  ⟨(i : Int), archiveRow_key? txnId i lo hi⟩

theorem rowInTable_resultRowLit (txnId : TxnId) (q : Nat) (n : Int) :
    rowInTable (resultRowLit txnId q n) (resultTable q) :=
  ⟨n, resultRowLit_key? txnId q n⟩

/-! ## SELECT predicate expressions -/

def fieldExpr (rowVar : VarName) (field : FieldName) : Expr :=
  .proj (.var rowVar) field

def addExpr (lhs rhs : Expr) : Expr := .binop BinOp.add lhs rhs
def leExpr  (lhs rhs : Expr) : Expr := .binop BinOp.le lhs rhs
def eqExpr  (lhs rhs : Expr) : Expr := .binop BinOp.eq lhs rhs
def andExpr (lhs rhs : Expr) : Expr := .binop BinOp.and lhs rhs
def orExpr  (lhs rhs : Expr) : Expr := .binop BinOp.or lhs rhs

def isTableExpr (rowVar : VarName) (table : TableName) : Expr :=
  eqExpr (fieldExpr rowVar tableField) (.int table)

def isCounterExpr (rowVar : VarName) : Expr := isTableExpr rowVar counterTable
def isLogExpr     (rowVar : VarName) : Expr := isTableExpr rowVar logTable
def isArchiveExpr (rowVar : VarName) : Expr := isTableExpr rowVar archiveTable
def isStorageEntryExpr (rowVar : VarName) : Expr :=
  orExpr (isLogExpr rowVar) (isArchiveExpr rowVar)

theorem satisfiesPredicate_isTableExpr_iff (row : Row) (table : TableName) :
    Semantics.satisfiesPredicate "row" (isTableExpr "row" table) row.visible = some true ↔
      rowFieldInt? row tableField = some table := by
  unfold Semantics.satisfiesPredicate isTableExpr eqExpr fieldExpr rowFieldInt?
  cases hLookup : row.visible.lookup? tableField
  · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
      Literal.toValue]
  · rename_i lit
    cases lit <;> simp [hLookup, Expr.eval, Expr.subst, Expr.int,
      Semantics.instantiateRecord, Literal.toValue]

theorem satisfiesPredicate_isStorageEntryExpr_iff (row : Row) :
    Semantics.satisfiesPredicate "row" (isStorageEntryExpr "row") row.visible = some true ↔
      rowFieldInt? row tableField = some logTable ∨
        rowFieldInt? row tableField = some archiveTable := by
  unfold Semantics.satisfiesPredicate isStorageEntryExpr isLogExpr isArchiveExpr
    isTableExpr orExpr eqExpr fieldExpr rowFieldInt?
  cases hLookup : row.visible.lookup? tableField
  · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
      Literal.toValue]
  · rename_i lit
    cases lit
    · rename_i value
      by_cases hLog : value = logTable
      · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
          Literal.toValue, hLog]
      · by_cases hArchive : value = archiveTable
        · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
            Literal.toValue, hLog, hArchive, logTable, archiveTable]
        · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
            Literal.toValue, hLog, hArchive]
    · simp [hLookup, Expr.eval, Expr.subst, Expr.int, Semantics.instantiateRecord,
        Literal.toValue]

/-! ## Concrete record-level expressions used by the bodies -/

def counterRecordExpr (next : Expr) : Expr :=
  .record
    [ (tableField, .int counterTable)
    , (idField, .int 0)
    , (nextField, next)
    ]

def logRecordExpr (n : Expr) : Expr :=
  .record
    [ (tableField, .int logTable)
    , (idField, n)
    ]

def archiveRecordExpr (i : Nat) (lo hi : Expr) : Expr :=
  .record
    [ (tableField, .int archiveTable)
    , (idField, .int i)
    , (loField, lo)
    , (hiField, hi)
    ]

def resultRecordExpr (q : Nat) (n : Expr) : Expr :=
  .record
    [ (tableField, .int (resultTable q))
    , (idField, n)
    ]

/-! ## Concrete transaction bodies -/

def logsVar      : VarName := "logs"
def entriesVar   : VarName := "entries"
def rowVar       : VarName := "row"
def entryVar     : VarName := "entry"
def rangeElemVar : VarName := "num"
def doneVar      : VarName := "done"
def rangeDoneVar : VarName := "rangeDone"
def loVar        : VarName := "lo"
def hi0Var       : VarName := "hi0"

/-- Insert externally supplied log number `i` and advance the counter to `i+1`. -/
def insertLogBody (i : Nat) : Semantics.Program :=
  .seq
    (.insert (logRecordExpr (.int i)))
    (.update rowVar
      (.withUpdates (.var rowVar) [(nextField, .int (i + 1))])
      (isCounterExpr rowVar))

def archiveDeletePredicate : Expr :=
  andExpr (isLogExpr rowVar)
    (andExpr
      (leExpr (.var loVar) (fieldExpr rowVar idField))
      (leExpr (fieldExpr rowVar idField) (.var hi0Var)))

def archiveCompactBody (i : Nat) : Semantics.Program :=
  .letE loVar (.setMinField (.var logsVar) idField)
    (.letE hi0Var (.setMaxField (.var logsVar) idField)
      (.seq
        (.insert (archiveRecordExpr i (.var loVar) (addExpr (.var hi0Var) (.int 1))))
        (.delete rowVar archiveDeletePredicate)))

/-- Compact currently visible log rows into one archive interval and delete the
compacted live log rows. Empty log sets are a no-op. -/
def archiveLogBody (i : Nat) : Semantics.Program :=
  .select logsVar rowVar (isLogExpr rowVar)
    (.ite (.setNonempty (.var logsVar)) (archiveCompactBody i) .skip)

/-- Expand the selected log/archive snapshot into result rows for query `q`. -/
def selectAllLogBody (q : Nat) : Semantics.Program :=
  .select entriesVar rowVar (isStorageEntryExpr rowVar)
    (.foreach (.var entriesVar) doneVar entryVar
      (.ite (isLogExpr entryVar)
        (.insert (resultRecordExpr q (fieldExpr entryVar idField)))
        (.foreach
          (.rangeRows idField (fieldExpr entryVar loField) (fieldExpr entryVar hiField))
          rangeDoneVar
          rangeElemVar
          (.insert (resultRecordExpr q (fieldExpr rangeElemVar idField))))))

/-! ## Finite-prefix top-level program shape -/

def insertTxnId  (i : Nat) : TxnId := 1000 + i
def archiveTxnId (i : Nat) : TxnId := 2000 + i
def selectTxnId  (q : Nat) : TxnId := 3000 + q

def txSeq : List Semantics.Program → Semantics.Program
  | [] => .skip
  | [program] => program
  | program :: programs => .seq program (txSeq programs)

def insertLogTxn (i : Nat) : Semantics.Program :=
  .txn (insertTxnId i) (IsolationSpec.readCommitted Database) (insertLogBody i)

def archiveLogTxn (i : Nat) : Semantics.Program :=
  .txn (archiveTxnId i) (IsolationSpec.readCommitted Database) (archiveLogBody i)

def selectAllLogTxn (q : Nat) : Semantics.Program :=
  .txn (selectTxnId q) (IsolationSpec.readCommitted Database) (selectAllLogBody q)

def insertWorker (n : Nat) : Semantics.Program :=
  txSeq ((List.range n).map insertLogTxn)

def archiveWorker (m : Nat) : Semantics.Program :=
  txSeq ((List.range m).map archiveLogTxn)

def insertWorkerFrom (start count : Nat) : Semantics.Program :=
  txSeq ((List.range count).map (fun offset => insertLogTxn (start + offset)))

def archiveWorkerFrom (start count : Nat) : Semantics.Program :=
  txSeq ((List.range count).map (fun offset => archiveLogTxn (start + offset)))

def logStorageProgram (n m q : Nat) : Semantics.Program :=
  .par (.par (insertWorker n) (archiveWorker m)) (selectAllLogTxn q)

theorem txSeq_nil : txSeq [] = (.skip : Semantics.Program) := rfl

theorem txSeq_singleton (program : Semantics.Program) : txSeq [program] = program := rfl

theorem txSeq_cons_cons (program next : Semantics.Program) (rest : List Semantics.Program) :
    txSeq (program :: next :: rest) = .seq program (txSeq (next :: rest)) := rfl

theorem insertWorker_zero : insertWorker 0 = .skip := rfl
theorem archiveWorker_zero : archiveWorker 0 = .skip := rfl

theorem insertWorker_eq_insertWorkerFrom (n : Nat) :
    insertWorker n = insertWorkerFrom 0 n := by
  simp [insertWorker, insertWorkerFrom]

theorem archiveWorker_eq_archiveWorkerFrom (n : Nat) :
    archiveWorker n = archiveWorkerFrom 0 n := by
  simp [archiveWorker, archiveWorkerFrom]

theorem insertWorkerFrom_zero (start : Nat) : insertWorkerFrom start 0 = .skip := rfl
theorem archiveWorkerFrom_zero (start : Nat) : archiveWorkerFrom start 0 = .skip := rfl

theorem insertWorkerFrom_succ (start count : Nat) :
    insertWorkerFrom start (count + 1) =
      match count with
      | 0 => insertLogTxn start
      | count' + 1 => .seq (insertLogTxn start) (insertWorkerFrom (start + 1) (count' + 1)) := by
  unfold insertWorkerFrom
  rw [List.range_succ_eq_map]
  cases count with
  | zero => simp [txSeq]
  | succ count' =>
      simp [List.map_map, Function.comp_def, txSeq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem archiveWorkerFrom_succ (start count : Nat) :
    archiveWorkerFrom start (count + 1) =
      match count with
      | 0 => archiveLogTxn start
      | count' + 1 => .seq (archiveLogTxn start) (archiveWorkerFrom (start + 1) (count' + 1)) := by
  unfold archiveWorkerFrom
  rw [List.range_succ_eq_map]
  cases count with
  | zero => simp [txSeq]
  | succ count' =>
      simp [List.map_map, Function.comp_def, txSeq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-! ## Live-row predicates -/

def liveRow (row : Row) : Prop := row.del = false

def liveLog (db : Database) (n : Int) : Prop :=
  ∃ row, row ∈ db ∧ liveRow row ∧ row.key? = some (logTable, n)

def liveCounterAt (db : Database) (next : Int) : Prop :=
  ∃ row,
    row ∈ db ∧ liveRow row ∧ row.key? = some (counterTable, 0) ∧
      rowFieldInt? row nextField = some next

/-- Every live counter row carries the same `next`. Together with the existence
of a live counter (`liveCounterAt`), this pins down the frontier value. -/
def liveCountersHaveNext (db : Database) (next : Int) : Prop :=
  ∀ row, row ∈ db → liveRow row → rowInTable row counterTable →
    rowFieldInt? row nextField = some next

/-- Every counter-table row uses key `(counterTable, 0)`. -/
def counterRowsAtZero (db : Database) : Prop :=
  ∀ row, row ∈ db → rowInTable row counterTable → row.key? = some (counterTable, 0)

def archiveCovers (db : Database) (n : Int) : Prop :=
  ∃ row i lo hi,
    row ∈ db ∧ liveRow row ∧ row.key? = some (archiveTable, i) ∧
      rowFieldInt? row loField = some lo ∧ rowFieldInt? row hiField = some hi ∧
      lo ≤ n ∧ n < hi

def resultRowFor (db : Database) (q : Nat) (n : Int) : Prop :=
  ∃ row, row ∈ db ∧ liveRow row ∧ row.key? = some (resultTable q, n)

/-! ## flush helpers -/

theorem mem_flush_iff {row : Row} {localDb globalDb : Database} :
    row ∈ Database.flush localDb globalDb ↔
      (row ∈ globalDb ∧
        match row.key? with
        | some key => key ∉ localDb.keyDom
        | none => True) ∨
      (row ∈ localDb ∧ row.del = false) := by
  unfold Database.flush
  simp only [List.mem_append, List.mem_filter]
  cases hKey : row.key? <;> simp [hKey]

theorem liveLog_of_flush {localDb globalDb : Database} {n : Int} :
    liveLog (Database.flush localDb globalDb) n →
      liveLog globalDb n ∨ liveLog localDb n := by
  rintro ⟨row, hMem, hLive, hKey⟩
  rw [mem_flush_iff] at hMem
  rcases hMem with hG | hL
  · exact Or.inl ⟨row, hG.1, hLive, hKey⟩
  · exact Or.inr ⟨row, hL.1, hLive, hKey⟩

theorem liveCounterAt_of_flush {localDb globalDb : Database} {next : Int} :
    liveCounterAt (Database.flush localDb globalDb) next →
      liveCounterAt globalDb next ∨ liveCounterAt localDb next := by
  rintro ⟨row, hMem, hLive, hKey, hNext⟩
  rw [mem_flush_iff] at hMem
  rcases hMem with hG | hL
  · exact Or.inl ⟨row, hG.1, hLive, hKey, hNext⟩
  · exact Or.inr ⟨row, hL.1, hLive, hKey, hNext⟩

theorem archiveCovers_of_flush {localDb globalDb : Database} {n : Int} :
    archiveCovers (Database.flush localDb globalDb) n →
      archiveCovers globalDb n ∨ archiveCovers localDb n := by
  rintro ⟨row, i, lo, hi, hMem, hLive, hKey, hLo, hHi, hLe, hLt⟩
  rw [mem_flush_iff] at hMem
  rcases hMem with hG | hL
  · exact Or.inl ⟨row, i, lo, hi, hG.1, hLive, hKey, hLo, hHi, hLe, hLt⟩
  · exact Or.inr ⟨row, i, lo, hi, hL.1, hLive, hKey, hLo, hHi, hLe, hLt⟩

theorem resultRowFor_of_flush {localDb globalDb : Database} {q : Nat} {n : Int} :
    resultRowFor (Database.flush localDb globalDb) q n →
      resultRowFor globalDb q n ∨ resultRowFor localDb q n := by
  rintro ⟨row, hMem, hLive, hKey⟩
  rw [mem_flush_iff] at hMem
  rcases hMem with hG | hL
  · exact Or.inl ⟨row, hG.1, hLive, hKey⟩
  · exact Or.inr ⟨row, hL.1, hLive, hKey⟩

theorem liveLog_flush_of_global {localDb globalDb : Database} {n : Int}
    (hNoClobber : (logTable, n) ∉ localDb.keyDom) :
    liveLog globalDb n → liveLog (Database.flush localDb globalDb) n := by
  rintro ⟨row, hMem, hLive, hKey⟩
  refine ⟨row, ?_, hLive, hKey⟩
  rw [mem_flush_iff]
  refine Or.inl ⟨hMem, ?_⟩
  rw [hKey]
  exact hNoClobber

theorem liveCounterAt_flush_of_global {localDb globalDb : Database} {next : Int}
    (hNoClobber : (counterTable, (0 : Int)) ∉ localDb.keyDom) :
    liveCounterAt globalDb next → liveCounterAt (Database.flush localDb globalDb) next := by
  rintro ⟨row, hMem, hLive, hKey, hNext⟩
  refine ⟨row, ?_, hLive, hKey, hNext⟩
  rw [mem_flush_iff]
  refine Or.inl ⟨hMem, ?_⟩
  rw [hKey]
  exact hNoClobber

theorem archiveCovers_flush_of_global {localDb globalDb : Database} {n : Int}
    (hNoClobber : ∀ i, (archiveTable, (i : Int)) ∉ localDb.keyDom) :
    archiveCovers globalDb n → archiveCovers (Database.flush localDb globalDb) n := by
  rintro ⟨row, i, lo, hi, hMem, hLive, hKey, hLo, hHi, hLe, hLt⟩
  refine ⟨row, i, lo, hi, ?_, hLive, hKey, hLo, hHi, hLe, hLt⟩
  rw [mem_flush_iff]
  refine Or.inl ⟨hMem, ?_⟩
  rw [hKey]
  exact hNoClobber i

theorem resultRowFor_flush_of_global {localDb globalDb : Database} {q : Nat} {n : Int}
    (hNoClobber : (resultTable q, n) ∉ localDb.keyDom) :
    resultRowFor globalDb q n → resultRowFor (Database.flush localDb globalDb) q n := by
  rintro ⟨row, hMem, hLive, hKey⟩
  refine ⟨row, ?_, hLive, hKey⟩
  rw [mem_flush_iff]
  refine Or.inl ⟨hMem, ?_⟩
  rw [hKey]
  exact hNoClobber

theorem resultRowFor_flush_of_local {localDb globalDb : Database} {q : Nat} {n : Int} :
    resultRowFor localDb q n → resultRowFor (Database.flush localDb globalDb) q n := by
  rintro ⟨row, hMem, hLive, hKey⟩
  refine ⟨row, ?_, hLive, hKey⟩
  rw [mem_flush_iff]
  exact Or.inr ⟨hMem, hLive⟩

/-! ## Storage shape and invariants -/

def archiveIntervalsWellFormed (db : Database) : Prop :=
  ∀ row i lo hi,
    row ∈ db → liveRow row → row.key? = some (archiveTable, i) →
      rowFieldInt? row loField = some lo → rowFieldInt? row hiField = some hi →
        lo ≤ hi

/-- Every row whose `key?` falls into a storage table is live. The select bodies
filter on visible fields rather than `Row.del`, so this invariant connects table
membership back to liveness. -/
def storageRowsLive (db : Database) : Prop :=
  ∀ row, row ∈ db →
    (rowInTable row counterTable ∨ rowInTable row logTable ∨ rowInTable row archiveTable) →
      liveRow row

/-- Every row in the database has both a complete `key?` and a `tableField`
that agrees with the key's table. This rules out (a) rows with `kindField`-only
fallback and (b) rows with `tableField` set but missing `idField`, both of
which would break the bridge between SELECT-predicate evaluation (field-based)
and key-based reasoning. Reachable databases satisfy this because every
operation either preserves a row from the initial DB (which sets both fields)
or inserts/updates via records that include both fields. -/
def wellFormedTableFields (db : Database) : Prop :=
  ∀ row, row ∈ db →
    ∃ table id,
      row.key? = some (table, id) ∧ rowFieldInt? row tableField = some table

theorem rowFieldInt?_tableField_of_key_wellFormed
    {db : Database} {row : Row} {table : TableName} {id : Int}
    (hWF : wellFormedTableFields db)
    (hMem : row ∈ db)
    (hKey : row.key? = some (table, id)) :
    rowFieldInt? row tableField = some table := by
  rcases hWF row hMem with ⟨table', id', hKey', hTab'⟩
  rw [hKey] at hKey'
  have hPair : (table, id) = (table', id') := Option.some.inj hKey'
  rw [(Prod.mk.inj hPair).1]
  exact hTab'

theorem key?_isSome_of_wellFormedTableFields
    {db : Database} {row : Row}
    (hWF : wellFormedTableFields db) (hMem : row ∈ db) :
    row.key?.isSome := by
  rcases hWF row hMem with ⟨_, _, hKey, _⟩
  rw [hKey]; rfl

theorem rowKey?_of_tableField_wellFormed
    {db : Database} {row : Row} {table : TableName}
    (hWF : wellFormedTableFields db) (hMem : row ∈ db)
    (hTab : rowFieldInt? row tableField = some table) :
    ∃ id, row.key? = some (table, id) := by
  rcases hWF row hMem with ⟨table', id', hKey, hTab'⟩
  rw [hTab] at hTab'
  have h : table = table' := Option.some.inj hTab'
  subst h
  exact ⟨id', hKey⟩

/-- `rowFieldInt? row field = some v` is equivalent to
`row.visible.lookup? field = some (.int v)`. -/
theorem rowFieldInt?_eq_some_iff_lookup
    {row : Row} {field : FieldName} {v : Int} :
    rowFieldInt? row field = some v ↔ row.visible.lookup? field = some (.int v) := by
  unfold rowFieldInt?
  constructor
  · intro h
    cases hL : row.visible.lookup? field with
    | none => rw [hL] at h; cases h
    | some lit =>
      cases lit with
      | int w =>
        rw [hL] at h
        simp at h
        subst h
        rfl
      | bool _ => rw [hL] at h; cases h
  · intro h
    rw [h]

/-- A row whose key is `some (table, id)` (with `wellFormedTableFields`) has
`lookup? "table"` set explicitly to `(.int table)`. -/
theorem lookup?_table_of_key_wellFormed
    {db : Database} {row : Row} {table : TableName} {id : Int}
    (hWF : wellFormedTableFields db) (hMem : row ∈ db)
    (hKey : row.key? = some (table, id)) :
    row.visible.lookup? "table" = some (.int table) :=
  rowFieldInt?_eq_some_iff_lookup.mp
    (rowFieldInt?_tableField_of_key_wellFormed hWF hMem hKey)

theorem lookup?_id_of_key
    {row : Row} {table : TableName} {id : Int}
    (hKey : row.key? = some (table, id)) :
    row.visible.lookup? "id" = some (.int id) :=
  rowFieldInt?_eq_some_iff_lookup.mp (rowFieldInt?_idField_of_key hKey)

/-- Storage shape: cut ≤ next, exactly one live counter row at `(counterTable, 0)`
holding `next`, live logs are precisely `[cut, next)`, archives cover `[0, cut)`,
intervals are well-formed, storage rows are live. The `wellFormedTableFields`
condition lives at the `logSystemInv` level rather than here so that
`sameStorageShape` (an iff over arbitrary `cut`, `next`) can transfer
storage-table information in both directions without dragging along
information about non-storage rows that may be clobbered by `Database.flush`. -/
def storageShape (db : Database) (cut next : Nat) : Prop :=
  cut ≤ next ∧
    liveCounterAt db next ∧
    counterRowsAtZero db ∧
    liveCountersHaveNext db next ∧
    storageRowsLive db ∧
    (∀ n : Nat, liveLog db n ↔ cut ≤ n ∧ n < next) ∧
    (∀ n : Nat, archiveCovers db n ↔ n < cut) ∧
    archiveIntervalsWellFormed db

def expandedLog (db : Database) (n : Int) : Prop :=
  liveLog db n ∨ archiveCovers db n

def resultPrefixFor (db : Database) (q : Nat) : Prop :=
  ∃ k : Nat, ∀ n : Nat, resultRowFor db q n ↔ n < k

def resultPrefixAll (db : Database) : Prop :=
  ∀ q, resultPrefixFor db q

def logSystemInv : Assertion :=
  fun db => ∃ cut next,
    storageShape db cut next ∧ resultPrefixAll db ∧ wellFormedTableFields db

def logSystemInvFor (q : Nat) : Assertion :=
  fun db => ∃ cut next,
    storageShape db cut next ∧ resultPrefixFor db q ∧ wellFormedTableFields db

def logSystemInvAtNext (next : Nat) : Assertion :=
  fun db => ∃ cut,
    storageShape db cut next ∧ resultPrefixAll db ∧ wellFormedTableFields db

theorem logSystemInv_of_logSystemInvAtNext {db : Database} {next : Nat}
    (h : logSystemInvAtNext next db) : logSystemInv db := by
  rcases h with ⟨cut, hShape, hResults, hWF⟩
  exact ⟨cut, next, hShape, hResults, hWF⟩

theorem storageShape_expandedLog_iff {db : Database} {cut next : Nat}
    (hShape : storageShape db cut next) :
    ∀ n : Nat, expandedLog db n ↔ n < next := by
  rcases hShape with ⟨hCut, _, _, _, _, hLive, hArchive, _⟩
  intro n
  unfold expandedLog
  rw [hLive n, hArchive n]
  omega

theorem logSystemInv_expandedLog_prefix {db : Database} (hInv : logSystemInv db) :
    ∃ next : Nat, ∀ n : Nat, expandedLog db n ↔ n < next := by
  rcases hInv with ⟨_cut, next, hShape, _hResults, _hWF⟩
  exact ⟨next, storageShape_expandedLog_iff hShape⟩

theorem storageShape_next_unique {db : Database} {cut₁ cut₂ next₁ next₂ : Nat}
    (h₁ : storageShape db cut₁ next₁) (h₂ : storageShape db cut₂ next₂) :
    next₁ = next₂ := by
  rcases h₁ with ⟨_, _, _, hHaveNext₁, _, _, _, _⟩
  rcases h₂ with ⟨_, hCounter₂, _, _, _, _, _, _⟩
  rcases hCounter₂ with ⟨row, hMem, hLive, hKey, hNext₂⟩
  have hInTable : rowInTable row counterTable := ⟨0, hKey⟩
  have hNext₁ := hHaveNext₁ row hMem hLive hInTable
  have hEqInt : (next₁ : Int) = (next₂ : Int) :=
    Option.some.inj (hNext₁.symm.trans hNext₂)
  exact Int.ofNat.inj hEqInt

/-! ## Initial database -/

def initialDb : Database :=
  [counterRow 0 0]

theorem mem_initialDb_iff {row : Row} : row ∈ initialDb ↔ row = counterRow 0 0 := by
  simp [initialDb]

theorem initialDb_keyDom : initialDb.keyDom = [(counterTable, 0)] := by
  simp [initialDb, Database.keyDom, counterRow_key?]

theorem liveCounterAt_initialDb : liveCounterAt initialDb 0 := by
  refine ⟨counterRow 0 0, ?_, ?_, ?_, ?_⟩
  · simp [initialDb]
  · simp [liveRow, counterRow, Row.fromInsert]
  · exact counterRow_key? 0 0
  · exact rowFieldInt?_counterRow_next 0 0

theorem liveCountersHaveNext_initialDb : liveCountersHaveNext initialDb 0 := by
  intro row hMem _hLive hInTable
  rw [mem_initialDb_iff] at hMem
  subst row
  exact rowFieldInt?_counterRow_next 0 0

theorem storageRowsLive_initialDb : storageRowsLive initialDb := by
  intro row hMem _hTable
  rw [mem_initialDb_iff] at hMem
  subst row
  simp [liveRow, counterRow, Row.fromInsert]

theorem liveLog_initialDb_false (n : Int) : ¬ liveLog initialDb n := by
  rintro ⟨row, hMem, _hLive, hKey⟩
  rw [mem_initialDb_iff] at hMem
  subst row
  rw [counterRow_key?] at hKey
  have : counterTable = logTable := (Prod.mk.inj (Option.some.inj hKey)).1
  exact counterTable_ne_logTable this

theorem archiveCovers_initialDb_false (n : Int) : ¬ archiveCovers initialDb n := by
  rintro ⟨row, i, lo, hi, hMem, _hLive, hKey, _, _, _, _⟩
  rw [mem_initialDb_iff] at hMem
  subst row
  rw [counterRow_key?] at hKey
  have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
  exact counterTable_ne_archiveTable this

theorem archiveIntervalsWellFormed_initialDb : archiveIntervalsWellFormed initialDb := by
  intro row i lo hi hMem _hLive hKey _ _
  rw [mem_initialDb_iff] at hMem
  subst row
  rw [counterRow_key?] at hKey
  have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
  exact absurd this counterTable_ne_archiveTable

theorem counterRowsAtZero_initialDb : counterRowsAtZero initialDb := by
  intro row hMem _hTable
  rw [mem_initialDb_iff] at hMem
  subst row
  exact counterRow_key? 0 0

theorem wellFormedTableFields_initialDb : wellFormedTableFields initialDb := by
  intro row hMem
  rw [mem_initialDb_iff] at hMem
  subst row
  exact ⟨counterTable, 0, counterRow_key? 0 0, rowFieldInt?_counterRow_table 0 0⟩

theorem storageShape_initialDb : storageShape initialDb 0 0 := by
  refine ⟨Nat.le_refl _, liveCounterAt_initialDb, counterRowsAtZero_initialDb,
    liveCountersHaveNext_initialDb, storageRowsLive_initialDb, ?_, ?_,
    archiveIntervalsWellFormed_initialDb⟩
  · intro n
    constructor
    · intro h; exact absurd h (liveLog_initialDb_false (n : Int))
    · intro ⟨_, h⟩; omega
  · intro n
    constructor
    · intro h; exact absurd h (archiveCovers_initialDb_false (n : Int))
    · intro h; omega

theorem resultRowFor_initialDb_false (q : Nat) (n : Int) : ¬ resultRowFor initialDb q n := by
  rintro ⟨row, hMem, _hLive, hKey⟩
  rw [mem_initialDb_iff] at hMem
  subst row
  rw [counterRow_key?] at hKey
  have hEq : counterTable = resultTable q := (Prod.mk.inj (Option.some.inj hKey)).1
  exact (resultTable_ne_counterTable q hEq.symm)

theorem resultPrefixFor_initialDb (q : Nat) : resultPrefixFor initialDb q := by
  refine ⟨0, ?_⟩
  intro n
  constructor
  · intro h; exact absurd h (resultRowFor_initialDb_false q n)
  · intro h; omega

theorem resultPrefixAll_initialDb : resultPrefixAll initialDb :=
  fun q => resultPrefixFor_initialDb q

theorem logSystemInv_initialDb : logSystemInv initialDb :=
  ⟨0, 0, storageShape_initialDb, resultPrefixAll_initialDb,
    wellFormedTableFields_initialDb⟩

theorem logSystemInvAtNext_initialDb : logSystemInvAtNext 0 initialDb :=
  ⟨0, storageShape_initialDb, resultPrefixAll_initialDb,
    wellFormedTableFields_initialDb⟩

theorem logSystemInvFor_initialDb (q : Nat) : logSystemInvFor q initialDb :=
  ⟨0, 0, storageShape_initialDb, resultPrefixFor_initialDb q,
    wellFormedTableFields_initialDb⟩

/-! ## Archive-key freshness invariant -/

/-- All archive keys `i, i+1, ...` are absent from the database. The indexed
archive worker uses this as both pre- and postcondition to express that each
`archiveLog i` writes a fresh archive key. -/
def archiveKeysFreshFrom (start : Nat) : Assertion :=
  fun db => ∀ i : Nat, start ≤ i →
    ∀ row, row ∈ db → row.key? ≠ some (archiveTable, (i : Int))

theorem archiveKeysFreshFrom_initialDb (start : Nat) :
    archiveKeysFreshFrom start initialDb := by
  intro i _hi row hMem hKey
  rw [mem_initialDb_iff] at hMem
  subst row
  rw [counterRow_key?] at hKey
  have : counterTable = archiveTable := (Prod.mk.inj (Option.some.inj hKey)).1
  exact counterTable_ne_archiveTable this

end LogStorageExample

end Transformer

end DbAppProgramLogic
