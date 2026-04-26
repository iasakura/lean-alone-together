import DbAppProgramLogic.ReadableSyntax
import DbAppProgramLogic.Server
import DbAppProgramLogic.Legacy

namespace DbAppProgramLogic

namespace ReadWriteWorkflowExample

/-!
A self-contained VCG walkthrough for more meaningful read/modify/write handlers.

This file is narrower than `AppWorkflowExample`. It does **not** try to prove the full parallel
server theorem. Instead, it shows the part many readers care about first:

1. write handler bodies that actually read a balance and write back a new balance
2. run `Transformer.vcg`
3. inspect the generated `effect`
4. prove the resulting concrete verification conditions on the intended base state

The two handlers are:

* credit one account by reading its balance and writing back `bal + 1`
* withdraw from another account by reading its balance and, when `bal >= 2`, writing back
  `bal - 2`

The purpose of this file is to make the VCG shape concrete before looking at the heavier
rely-aware parallel story.
-/

def nonnegativeBalances : Assertion :=
  fun db =>
    ∀ row, row ∈ db →
      match row.visible.lookup? "bal" with
      | some (.int bal) => 0 <= bal
      | _ => True

def accountRecord (acctId bal : Int) : RecordLit :=
  ⟨[("id", .int acctId), ("bal", .int bal)]⟩

def accountRow (txnId : TxnId) (acctId bal : Int) : Row :=
  Row.fromInsert txnId (accountRecord acctId bal)

def creditTxnId : TxnId := 31
def withdrawalTxnId : TxnId := 32

def creditBaseRow : Row :=
  accountRow 0 1 4

def creditUpdatedRow : Row :=
  accountRow creditTxnId 1 5

def withdrawalBaseRow : Row :=
  accountRow 0 2 4

def withdrawalUpdatedRow : Row :=
  accountRow withdrawalTxnId 2 2

def creditBaseRowOf (bal : Int) : Row :=
  accountRow 0 1 bal

def creditUpdatedRowOf (bal : Int) : Row :=
  accountRow creditTxnId 1 (bal + 1)

def creditSourceRowOf (srcTxnId : TxnId) (bal : Int) : Row :=
  accountRow srcTxnId 1 bal

def withdrawalBaseRowOf (bal : Int) : Row :=
  accountRow 0 2 bal

def withdrawalUpdatedRowOf (bal : Int) : Row :=
  accountRow withdrawalTxnId 2 (bal - 2)

def withdrawalSourceRowOf (srcTxnId : TxnId) (bal : Int) : Row :=
  accountRow srcTxnId 2 bal

/--
Rely relation used by the tutorial handlers: environment steps may happen, but rows carrying the
observed account id must be preserved exactly.
-/
def preservesObservedId (acctId : Int) : Rely :=
  fun db db' =>
    ∀ row, row.id? = some acctId → (row ∈ db ↔ row ∈ db')

def identityRely : Rely :=
  fun db db' => db' = db

def creditBodyFor (acctId delta : Int) : Semantics.Program :=
  let! selected = selectRows where acct => (col(acct, id)) .==. (Expr.int acctId) in
    foreach! acct in v! selected with done do
      UPDATE! row SET (v! row with! bal := (col(acct, bal)) .+. (Expr.int delta))
        WHERE (col(row, id)) .==. (col(acct, id))

def guardedWithdrawalBodyFor (acctId amount : Int) : Semantics.Program :=
  let! selected = selectRows where acct => (col(acct, id)) .==. (Expr.int acctId) in
    foreach! acct in v! selected with done do
      IF! (col(acct, bal)) .>=. (Expr.int amount) THEN
        UPDATE! row SET (v! row with! bal := (col(acct, bal)) .-. (Expr.int amount))
        WHERE (col(row, id)) .==. (col(acct, id))
    ELSE
      SKIP!

def creditBody : Semantics.Program :=
  creditBodyFor 1 1

def guardedWithdrawalBody : Semantics.Program :=
  guardedWithdrawalBodyFor 2 2

def creditRely : Rely :=
  identityRely

def withdrawalRely : Rely :=
  identityRely

def creditInvariant : Assertion :=
  fun db => ∃ srcTxnId : TxnId, ∃ bal, 0 <= bal ∧ db = [creditSourceRowOf srcTxnId bal]

def withdrawalInvariant : Assertion :=
  fun db => ∃ srcTxnId : TxnId, ∃ bal, 0 <= bal ∧ db = [withdrawalSourceRowOf srcTxnId bal]

def creditGuarantee : Guarantee :=
  fun db db' =>
    ∃ localDb,
      Transformer.inferEffect creditTxnId [] creditBody db = some localDb ∧
      db' = Database.flush localDb db

def withdrawalGuarantee : Guarantee :=
  fun db db' =>
    ∃ localDb,
      Transformer.inferEffect withdrawalTxnId [] guardedWithdrawalBody db = some localDb ∧
      db' = Database.flush localDb db

def creditInfo : Transformer.TransactionVCG :=
  Transformer.vcg creditRely creditInvariant
    creditGuarantee
    creditTxnId (IsolationSpec.readCommitted Database) creditBody

def withdrawalInfo : Transformer.TransactionVCG :=
  Transformer.vcg withdrawalRely withdrawalInvariant
    withdrawalGuarantee
    withdrawalTxnId (IsolationSpec.readCommitted Database) guardedWithdrawalBody

theorem accountRecord_lookup_id (acctId bal : Int) :
    (accountRecord acctId bal).lookup? "id" = some (.int acctId) := by
  simp [accountRecord, RecordLit.lookup?]

theorem accountRecord_lookup_bal (acctId bal : Int) :
    (accountRecord acctId bal).lookup? "bal" = some (.int bal) := by
  simp [accountRecord, RecordLit.lookup?]

/-! ## Credit example: inspect the generated effect and prove the concrete obligations -/

theorem credit_effect_on_base :
    creditInfo.effect [creditBaseRow] = some [creditUpdatedRow] := by
  native_decide

theorem credit_effect_defined_on_base :
    ∃ localDb, creditInfo.effect [creditBaseRow] = some localDb := by
  exact ⟨[creditUpdatedRow], credit_effect_on_base⟩

theorem credit_guarantee_on_base :
    (fun db db' => db' = Database.flush [creditUpdatedRow] db)
      [creditBaseRow]
      (Database.flush [creditUpdatedRow] [creditBaseRow]) := by
  rfl

theorem credit_post_invariant_on_base :
    nonnegativeBalances (Database.flush [creditUpdatedRow] [creditBaseRow]) := by
  rw [show Database.flush [creditUpdatedRow] [creditBaseRow] = [creditUpdatedRow] by native_decide]
  intro row hMem
  rcases List.mem_singleton.mp hMem with rfl
  simp [creditUpdatedRow, accountRow, accountRecord, Row.fromInsert, RecordLit.lookup?]

/-! ## Withdrawal example: same flow, but now the body contains a read-dependent branch -/

theorem withdrawal_effect_on_base :
    withdrawalInfo.effect [withdrawalBaseRow] = some [withdrawalUpdatedRow] := by
  native_decide

theorem withdrawal_effect_defined_on_base :
    ∃ localDb, withdrawalInfo.effect [withdrawalBaseRow] = some localDb := by
  exact ⟨[withdrawalUpdatedRow], withdrawal_effect_on_base⟩

theorem withdrawal_guarantee_on_base :
    (fun db db' => db' = Database.flush [withdrawalUpdatedRow] db)
      [withdrawalBaseRow]
      (Database.flush [withdrawalUpdatedRow] [withdrawalBaseRow]) := by
  rfl

theorem withdrawal_post_invariant_on_base :
    nonnegativeBalances (Database.flush [withdrawalUpdatedRow] [withdrawalBaseRow]) := by
  rw [show Database.flush [withdrawalUpdatedRow] [withdrawalBaseRow] = [withdrawalUpdatedRow] by native_decide]
  intro row hMem
  rcases List.mem_singleton.mp hMem with rfl
  simp [withdrawalUpdatedRow, accountRow, accountRecord, Row.fromInsert, RecordLit.lookup?]

/-!
This tutorial file stops at concrete VCG obligations on the intended base states.

For the full rely-aware and parallel story, see `AppWorkflowExample.lean`, which packages
transaction proofs into handler refinement and then composes them with the server-level results.
-/

end ReadWriteWorkflowExample

end DbAppProgramLogic
