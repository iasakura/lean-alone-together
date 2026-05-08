import DbAppProgramLogic.Transformer.Basic
import DbAppProgramLogic.Transformer.LogStorageExample.Model

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Concrete inferred effects — sanity checkpoints

These small concrete `inferEffect` facts validate the table-first model end to
end before the proof scaffolding goes up.
-/

theorem insertLog_inferEffect_initialDb_first :
    inferEffect (insertTxnId 0) [] (insertLogBody 0) initialDb =
      some [logRow (insertTxnId 0) 0, counterRow (insertTxnId 0) 1] := by
  native_decide

theorem archiveLog_inferEffect_initialDb (i : Nat) :
    inferEffect (archiveTxnId i) [] (archiveLogBody i) initialDb = some [] := by
  simp [archiveLogBody, initialDb, inferEffect, emptyEffect, logsVar,
    Semantics.collectSelected, Semantics.collectSelected.go, isLogExpr, isTableExpr,
    eqExpr, fieldExpr, rowVar, tableField, logTable, counterTable, counterRecord,
    counterRow, Row.fromInsert, Semantics.satisfiesPredicate,
    Semantics.instantiateRecord, Expr.eval, Expr.int, RecordLit.lookup?, idField,
    nextField, evalInEnv, instantiateExpr, Expr.subst, Literal.toValue,
    Value.toExpr, Env.insert, Env.erase]

theorem selectAllLog_inferEffect_initialDb (q : Nat) :
    inferEffect (selectTxnId q) [] (selectAllLogBody q) initialDb = some [] := by
  simp [selectAllLogBody, initialDb, inferEffect, inferForeach, emptyEffect,
    entriesVar, rowVar, isStorageEntryExpr, isLogExpr, isArchiveExpr, isTableExpr,
    eqExpr, orExpr, fieldExpr, tableField, logTable, archiveTable, counterTable,
    counterRecord, counterRow, Row.fromInsert, Semantics.collectSelected,
    Semantics.collectSelected.go, Semantics.satisfiesPredicate,
    Semantics.instantiateRecord, Expr.eval, Expr.int, RecordLit.lookup?, idField,
    nextField, evalInEnv, instantiateExpr, Expr.subst, Literal.toValue,
    Value.toExpr, Env.insert, Env.erase]

def afterInsert0Db : Database :=
  Database.flush [logRow (insertTxnId 0) 0, counterRow (insertTxnId 0) 1] initialDb

theorem afterInsert0Db_eq :
    afterInsert0Db = [logRow (insertTxnId 0) 0, counterRow (insertTxnId 0) 1] := by
  native_decide

theorem archiveLog_inferEffect_afterInsert0_first :
    inferEffect (archiveTxnId 0) [] (archiveLogBody 0) afterInsert0Db =
      some
        [ archiveRow (archiveTxnId 0) 0 0 1
        , (logRow (insertTxnId 0) 0).markDeleted (archiveTxnId 0)
        ] := by
  native_decide

theorem selectAllLog_inferEffect_afterInsert0_first :
    inferEffect (selectTxnId 0) [] (selectAllLogBody 0) afterInsert0Db =
      some [resultRowLit (selectTxnId 0) 0 0] := by
  native_decide

def afterArchive0Db : Database :=
  Database.flush
    [ archiveRow (archiveTxnId 0) 0 0 1
    , (logRow (insertTxnId 0) 0).markDeleted (archiveTxnId 0)
    ]
    afterInsert0Db

theorem afterArchive0Db_eq :
    afterArchive0Db = [counterRow (insertTxnId 0) 1, archiveRow (archiveTxnId 0) 0 0 1] := by
  native_decide

theorem selectAllLog_inferEffect_afterArchive0_first :
    inferEffect (selectTxnId 0) [] (selectAllLogBody 0) afterArchive0Db =
      some [resultRowLit (selectTxnId 0) 0 0] := by
  native_decide

end LogStorageExample

end Transformer

end DbAppProgramLogic
