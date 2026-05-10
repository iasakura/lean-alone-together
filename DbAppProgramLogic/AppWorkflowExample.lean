import DbAppProgramLogic.ReadableSyntax
import DbAppProgramLogic.Refinement

namespace DbAppProgramLogic

namespace AppWorkflowExample

/-!
A worked example organized around the question:

> "If I want to verify my own small application, what proof steps do I actually follow?"

The flow in this file is intentionally linear and self-contained:

1. define the application transactions and the parallel server program
2. define the global invariant
3. define request-level abstract specifications and per-transaction rely/guarantee
4. run the VCG for each transaction
5. prove the resulting verification conditions
6. derive handler refinements from `vcg_sound`
7. compose the handlers in parallel and read the result as a request-level `foldl`

The toy application is an event-sourced banking ledger. One transaction records a one-unit interest
payment event, the other records a two-unit withdrawal event. The example stays small enough to be
read as a tutorial, but the domain is less artificial than two unrelated inserts.
-/

/-! ## 1. Application definition -/

inductive Request where
  | creditInterest
  | recordWithdrawal
  deriving DecidableEq, Repr

def interestTxnId : TxnId := 10
def withdrawalTxnId : TxnId := 20

def creditInterestBody : Semantics.Program :=
  INSERT! (.record [("kind", i![1]), ("amt", i![1])])

def recordWithdrawalBody : Semantics.Program :=
  INSERT! (.record [("kind", i![2]), ("amt", i![2])])

def creditInterestTxn : Semantics.Program :=
  .txn interestTxnId (IsolationSpec.readCommitted Database) creditInterestBody

def recordWithdrawalTxn : Semantics.Program :=
  .txn withdrawalTxnId (IsolationSpec.readCommitted Database) recordWithdrawalBody

def ledgerProgram : Semantics.Program :=
  .par creditInterestTxn recordWithdrawalTxn

/-! ## 2. Global invariant -/

/-- Structural invariant for the ledger: every event amount is nonnegative. -/
def LedgerInvariant : Assertion :=
  fun db =>
    ∀ row, row ∈ db →
      match row.visible.lookup? "amt" with
      | some (.int amt) => 0 <= amt
      | _ => True

/-! ## 3. Abstract specs, rely, and guarantee -/

def interestEventRecord : RecordLit :=
  ⟨[("kind", .int 1), ("amt", .int 1)]⟩

def withdrawalEventRecord : RecordLit :=
  ⟨[("kind", .int 2), ("amt", .int 2)]⟩

def interestEventRowOf (txnId : TxnId) : Row :=
  Row.fromInsert txnId interestEventRecord

def withdrawalEventRowOf (txnId : TxnId) : Row :=
  Row.fromInsert txnId withdrawalEventRecord

def creditInterestApply : StateTransformer :=
  fun db => Database.flush [interestEventRowOf interestTxnId] db

def recordWithdrawalApply : StateTransformer :=
  fun db => Database.flush [withdrawalEventRowOf withdrawalTxnId] db

def creditInterestSpec : StateSpec :=
  StateSpec.graph creditInterestApply

def recordWithdrawalSpec : StateSpec :=
  StateSpec.graph recordWithdrawalApply

/-- Each transaction assumes either no external step or one commit by its sibling. -/
def creditInterestRely : Rely :=
  fun db db' => False ∨ recordWithdrawalSpec db db'

def recordWithdrawalRely : Rely :=
  fun db db' => False ∨ creditInterestSpec db db'

def requestOfTxn : TxnId → Request
  | 10 => .creditInterest
  | _ => .recordWithdrawal

def requestApply : RequestTransformer Request
  | .creditInterest => creditInterestApply
  | .recordWithdrawal => recordWithdrawalApply

/-! ## 4. Run the VCG -/

def creditInterestInfo : Transformer.TransactionVCG :=
  Transformer.vcg creditInterestRely LedgerInvariant creditInterestSpec
    interestTxnId (IsolationSpec.readCommitted Database) creditInterestBody

def recordWithdrawalInfo : Transformer.TransactionVCG :=
  Transformer.vcg recordWithdrawalRely LedgerInvariant recordWithdrawalSpec
    withdrawalTxnId (IsolationSpec.readCommitted Database) recordWithdrawalBody

/-! ## 5. Prove the verification conditions for each transaction -/

theorem false_rely_silent :
    ∀ db db' : Database, (fun _ _ => False) db db' → db' = db := by
  intro db db' hFalse
  exact False.elim hFalse

theorem ledgerInvariant_flush_interestEvent {db : Database}
    (hDb : LedgerInvariant db) :
    LedgerInvariant (Database.flush [interestEventRowOf interestTxnId] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [interestEventRowOf, interestEventRecord, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [interestEventRowOf, interestEventRecord, Row.fromInsert, RecordLit.lookup?]

theorem ledgerInvariant_flush_withdrawalEvent {db : Database}
    (hDb : LedgerInvariant db) :
    LedgerInvariant (Database.flush [withdrawalEventRowOf withdrawalTxnId] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [withdrawalEventRowOf, withdrawalEventRecord, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [withdrawalEventRowOf, withdrawalEventRecord, Row.fromInsert, RecordLit.lookup?]

theorem creditInterest_insert_eval :
    Expr.eval (.record [("kind", i![1]), ("amt", i![1])]) =
      some (.record interestEventRecord) := by
  native_decide

theorem recordWithdrawal_insert_eval :
    Expr.eval (.record [("kind", i![2]), ("amt", i![2])]) =
      some (.record withdrawalEventRecord) := by
  native_decide

theorem creditInterest_inferEffect (visibleDb : Database) :
    Transformer.inferEffect interestTxnId [] creditInterestBody visibleDb =
      some [interestEventRowOf interestTxnId] := by
  simp [creditInterestBody, Transformer.inferEffect, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, interestEventRowOf]
  rw [creditInterest_insert_eval]
  rfl

theorem recordWithdrawal_inferEffect (visibleDb : Database) :
    Transformer.inferEffect withdrawalTxnId [] recordWithdrawalBody visibleDb =
      some [withdrawalEventRowOf withdrawalTxnId] := by
  simp [recordWithdrawalBody, Transformer.inferEffect, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, withdrawalEventRowOf]
  rw [recordWithdrawal_insert_eval]
  rfl

theorem ledgerInvariant_stable_creditInterestRely :
    Logic.stableAssertion creditInterestRely LedgerInvariant := by
  intro db db' hInv hR
  rcases hR with hFalse | hGraph
  · exact False.elim hFalse
  · subst hGraph
    exact ledgerInvariant_flush_withdrawalEvent hInv

theorem ledgerInvariant_stable_recordWithdrawalRely :
    Logic.stableAssertion recordWithdrawalRely LedgerInvariant := by
  intro db db' hInv hR
  rcases hR with hFalse | hGraph
  · exact False.elim hFalse
  · subst hGraph
    exact ledgerInvariant_flush_interestEvent hInv

theorem creditInterest_guarantee_ok :
    creditInterestInfo.guaranteeOk := by
  intro visibleDb localDb hEffect
  have hConst :
      Transformer.inferEffect interestTxnId [] creditInterestBody visibleDb =
        some [interestEventRowOf interestTxnId] := by
    exact creditInterest_inferEffect visibleDb
  rw [hConst] at hEffect
  injection hEffect with hLocalDb
  subst hLocalDb
  rfl

theorem recordWithdrawal_guarantee_ok :
    recordWithdrawalInfo.guaranteeOk := by
  intro visibleDb localDb hEffect
  have hConst :
      Transformer.inferEffect withdrawalTxnId [] recordWithdrawalBody visibleDb =
        some [withdrawalEventRowOf withdrawalTxnId] := by
    exact recordWithdrawal_inferEffect visibleDb
  rw [hConst] at hEffect
  injection hEffect with hLocalDb
  subst hLocalDb
  rfl

theorem creditInterest_commitStable :
    creditInterestInfo.commitStable := by
  intro localDb visibleDb visibleDb' _hRely
  have hLeft :
      Transformer.inferEffect interestTxnId [] creditInterestBody visibleDb =
        some [interestEventRowOf interestTxnId] := by
    exact creditInterest_inferEffect visibleDb
  have hRight :
      Transformer.inferEffect interestTxnId [] creditInterestBody visibleDb' =
        some [interestEventRowOf interestTxnId] := by
    exact creditInterest_inferEffect visibleDb'
  rw [hLeft, hRight]

theorem recordWithdrawal_commitStable :
    recordWithdrawalInfo.commitStable := by
  intro localDb visibleDb visibleDb' _hRely
  have hLeft :
      Transformer.inferEffect withdrawalTxnId [] recordWithdrawalBody visibleDb =
        some [withdrawalEventRowOf withdrawalTxnId] := by
    exact recordWithdrawal_inferEffect visibleDb
  have hRight :
      Transformer.inferEffect withdrawalTxnId [] recordWithdrawalBody visibleDb' =
        some [withdrawalEventRowOf withdrawalTxnId] := by
    exact recordWithdrawal_inferEffect visibleDb'
  rw [hLeft, hRight]

theorem creditInterest_localValid :
    Logic.LocalValid
      (Logic.relyMod creditInterestRely (IsolationSpec.readCommitted Database).exec)
      interestTxnId
      (fun localDb visible => localDb = [] ∧ LedgerInvariant visible)
      creditInterestBody
      (Transformer.effectPost LedgerInvariant creditInterestInfo.effect) := by
  refine Logic.localValid_insert
    (R := Logic.relyMod creditInterestRely (IsolationSpec.readCommitted Database).exec)
    (txnId := interestTxnId)
    (P := fun localDb visible => localDb = [] ∧ LedgerInvariant visible)
    (Q := Transformer.effectPost LedgerInvariant creditInterestInfo.effect)
    (.record [("kind", i![1]), ("amt", i![1])])
    ?_
    ?_
  · intro localDb visibleDb visibleDb' hPre hRely
    rcases hPre with ⟨hLocal, hInv⟩
    rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
    exact ⟨hLocal, ledgerInvariant_stable_creditInterestRely _ _ hInv hR⟩
  · intro localDb visibleDb record hPre hEval _hFresh
    rcases hPre with ⟨hLocal, hInv⟩
    subst hLocal
    have hValueEq : some (Value.record interestEventRecord) = some (Value.record record) := by
      rw [← creditInterest_insert_eval]
      exact hEval
    injection hValueEq with hRecordEq
    cases hRecordEq
    constructor
    · simpa [Transformer.effectPost, creditInterestInfo, Transformer.vcg] using
        creditInterest_inferEffect visibleDb
    · exact hInv

theorem recordWithdrawal_localValid :
    Logic.LocalValid
      (Logic.relyMod recordWithdrawalRely (IsolationSpec.readCommitted Database).exec)
      withdrawalTxnId
      (fun localDb visible => localDb = [] ∧ LedgerInvariant visible)
      recordWithdrawalBody
      (Transformer.effectPost LedgerInvariant recordWithdrawalInfo.effect) := by
  refine Logic.localValid_insert
    (R := Logic.relyMod recordWithdrawalRely (IsolationSpec.readCommitted Database).exec)
    (txnId := withdrawalTxnId)
    (P := fun localDb visible => localDb = [] ∧ LedgerInvariant visible)
    (Q := Transformer.effectPost LedgerInvariant recordWithdrawalInfo.effect)
    (.record [("kind", i![2]), ("amt", i![2])])
    ?_
    ?_
  · intro localDb visibleDb visibleDb' hPre hRely
    rcases hPre with ⟨hLocal, hInv⟩
    rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
    exact ⟨hLocal, ledgerInvariant_stable_recordWithdrawalRely _ _ hInv hR⟩
  · intro localDb visibleDb record hPre hEval _hFresh
    rcases hPre with ⟨hLocal, hInv⟩
    subst hLocal
    have hValueEq : some (Value.record withdrawalEventRecord) = some (Value.record record) := by
      rw [← recordWithdrawal_insert_eval]
      exact hEval
    injection hValueEq with hRecordEq
    cases hRecordEq
    constructor
    · simpa [Transformer.effectPost, recordWithdrawalInfo, Transformer.vcg] using
        recordWithdrawal_inferEffect visibleDb
    · exact hInv

theorem creditInterest_preserves_invariant :
    creditInterestInfo.preservesInvariant := by
  intro db db' hDb hSpec
  subst hSpec
  exact ledgerInvariant_flush_interestEvent hDb

theorem recordWithdrawal_preserves_invariant :
    recordWithdrawalInfo.preservesInvariant := by
  intro db db' hDb hSpec
  subst hSpec
  exact ledgerInvariant_flush_withdrawalEvent hDb

/-! ## 6. Use `vcg_sound` to obtain handler-level refinement theorems -/

theorem creditInterest_handlerRefines :
    Server.HandlerRefines LedgerInvariant creditInterestRely
      creditInterestTxn
      creditInterestSpec
      LedgerInvariant := by
  exact Transformer.vcg_sound
    interestTxnId
    (IsolationSpec.readCommitted Database)
    creditInterestBody
    ledgerInvariant_stable_creditInterestRely
    (by
      intro localDb baseDb midDb finalDb _ _ _hR
      constructor <;> simp [IsolationSpec.readCommitted])
    creditInterest_localValid
    (by
      intro localDb baseDb midDb finalDb _ _ _hR
      constructor <;> simp [IsolationSpec.readCommitted])
    creditInterest_commitStable
    creditInterest_guarantee_ok
    creditInterest_preserves_invariant

theorem recordWithdrawal_handlerRefines :
    Server.HandlerRefines LedgerInvariant recordWithdrawalRely
      recordWithdrawalTxn
      recordWithdrawalSpec
      LedgerInvariant := by
  exact Transformer.vcg_sound
    withdrawalTxnId
    (IsolationSpec.readCommitted Database)
    recordWithdrawalBody
    ledgerInvariant_stable_recordWithdrawalRely
    (by
      intro localDb baseDb midDb finalDb _ _ _hR
      constructor <;> simp [IsolationSpec.readCommitted])
    recordWithdrawal_localValid
    (by
      intro localDb baseDb midDb finalDb _ _ _hR
      constructor <;> simp [IsolationSpec.readCommitted])
    recordWithdrawal_commitStable
    recordWithdrawal_guarantee_ok
    recordWithdrawal_preserves_invariant

/-! ## 7. Compose the transactions in parallel and read the result as a request trace -/

theorem ledgerProgram_request_foldl
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : LedgerInvariant db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨ledgerProgram, db⟩
        finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl
          (fun current req => requestApply req current)
          db
          (Server.CommitLog.requests requestOfTxn events) := by
  exact Refinement.txnPair_request_foldl_of_handlerRefines
    (leftTxnId := interestTxnId)
    (rightTxnId := withdrawalTxnId)
    (leftIsolation := IsolationSpec.readCommitted Database)
    (rightIsolation := IsolationSpec.readCommitted Database)
    (leftBody := creditInterestBody)
    (rightBody := recordWithdrawalBody)
    (requestOf := requestOfTxn)
    (fs := requestApply)
    creditInterest_handlerRefines
    recordWithdrawal_handlerRefines
    false_rely_silent
    hDb
    hRun

end AppWorkflowExample

end DbAppProgramLogic
