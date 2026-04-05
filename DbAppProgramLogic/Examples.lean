import DbAppProgramLogic.FirstOrder
import DbAppProgramLogic.Refinement
import DbAppProgramLogic.Server

namespace DbAppProgramLogic

namespace Examples

/-!
Small end-to-end examples for the corrected development.

The `zeroBalance` fragment is the recommended first example: it shows a simple VCG proof, its
symbolic postcondition, and the minimal paper-faithful server wrapper for a single transaction. The
`addInterest` fragment exercises the symbolic set-language and first-order layers on a transaction
that both reads and writes.
-/

/-! ## Zero-balance insert example -/

def nonnegativeBalances : Assertion :=
  fun db =>
    ∀ row, row ∈ db →
      match row.visible.lookup? "bal" with
      | some (.int bal) => 0 <= bal
      | _ => True

def zeroBalanceRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 0)]⟩

def zeroBalanceRow : Row :=
  Row.fromInsert 0 zeroBalanceRecord

def zeroBalanceRowOf (txnId : TxnId) : Row :=
  Row.fromInsert txnId zeroBalanceRecord

def zeroBalanceInsertBody : Semantics.Program :=
  .insert (.record [("id", Expr.int 1), ("bal", Expr.int 0)])

def zeroBalanceGuarantee : Guarantee :=
  fun db db' => db' = Database.flush [zeroBalanceRow] db

def zeroBalanceGuaranteeOf (txnId : TxnId) : Guarantee :=
  fun db db' => db' = Database.flush [zeroBalanceRowOf txnId] db

def zeroBalanceApply : StateTransformer :=
  fun db => Database.flush [zeroBalanceRow] db

def zeroBalanceApplyOf (txnId : TxnId) : StateTransformer :=
  fun db => Database.flush [zeroBalanceRowOf txnId] db

def identityGuarantee : Guarantee :=
  StateSpec.graph id

def zeroBalanceRecordTwo : RecordLit :=
  ⟨[("id", .int 2), ("bal", .int 0)]⟩

def zeroBalanceRowTwoOf (txnId : TxnId) : Row :=
  Row.fromInsert txnId zeroBalanceRecordTwo

def zeroBalanceInsertBodyTwo : Semantics.Program :=
  .insert (.record [("id", Expr.int 2), ("bal", Expr.int 0)])

def zeroBalanceGuaranteeTwoOf (txnId : TxnId) : Guarantee :=
  fun db db' => db' = Database.flush [zeroBalanceRowTwoOf txnId] db

def zeroBalanceApplyTwoOf (txnId : TxnId) : StateTransformer :=
  fun db => Database.flush [zeroBalanceRowTwoOf txnId] db

def zeroBalanceParProgram : Semantics.Program :=
  .par
    (.txn 10 (IsolationSpec.readCommitted Database) zeroBalanceInsertBody)
    (.txn 20 (IsolationSpec.readCommitted Database) zeroBalanceInsertBodyTwo)

def zeroBalanceParGuarantee : Guarantee :=
  fun db db' => zeroBalanceGuaranteeOf 10 db db' ∨ zeroBalanceGuaranteeTwoOf 20 db db'

/-- The concrete VCG record produced for the zero-balance insert transaction.

Reading the fields of this definition is the easiest way to see the proof obligations that the
current concrete VCG generates:

* `effect` computes the transaction-local write set
* `guaranteeOk` says flushing that write set satisfies the chosen guarantee
* `preservesInvariant` says every guaranteed post-state preserves the invariant

The remaining side condition for `vcg_sound_false` is `effectDefinedOn`, proved separately below.
-/
def zeroBalanceInfo : Transformer.TransactionVCG :=
  Transformer.vcg (fun _ _ => False) nonnegativeBalances zeroBalanceGuarantee
    0 Database.uniqueIds zeroBalanceInsertBody

theorem identityGuarantee_silent :
    ∀ db db' : Database, identityGuarantee db db' → db' = db := by
  intro db db' hId
  exact hId

theorem false_rely_silent :
    ∀ db db' : Database, (fun _ _ => False) db db' → db' = db := by
  intro db db' hFalse
  exact False.elim hFalse

theorem nonnegativeBalances_flush_zeroBalanceRow {db : Database}
    (hDb : nonnegativeBalances db) :
    nonnegativeBalances (Database.flush [zeroBalanceRow] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [zeroBalanceRow, zeroBalanceRecord, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [zeroBalanceRow, zeroBalanceRecord, Row.fromInsert, RecordLit.lookup?]

theorem nonnegativeBalances_flush_zeroBalanceRowOf {txnId : TxnId} {db : Database}
    (hDb : nonnegativeBalances db) :
    nonnegativeBalances (Database.flush [zeroBalanceRowOf txnId] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [zeroBalanceRowOf, zeroBalanceRecord, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [zeroBalanceRowOf, zeroBalanceRecord, Row.fromInsert, RecordLit.lookup?]

theorem nonnegativeBalances_flush_zeroBalanceRowTwoOf {txnId : TxnId} {db : Database}
    (hDb : nonnegativeBalances db) :
    nonnegativeBalances (Database.flush [zeroBalanceRowTwoOf txnId] db) := by
  intro row hMem
  unfold Database.flush at hMem
  simp [zeroBalanceRowTwoOf, zeroBalanceRecordTwo, Row.fromInsert, Database.dom] at hMem
  rcases hMem with hPreserved | hInserted
  · exact hDb row hPreserved.1
  · subst hInserted
    simp [zeroBalanceRowTwoOf, zeroBalanceRecordTwo, Row.fromInsert, RecordLit.lookup?]

theorem zeroBalance_insert_eval :
    Expr.eval (.record [("id", Expr.int 1), ("bal", Expr.int 0)]) =
      some (.record zeroBalanceRecord) := by
  native_decide

theorem zeroBalanceTwo_insert_eval :
    Expr.eval (.record [("id", Expr.int 2), ("bal", Expr.int 0)]) =
      some (.record zeroBalanceRecordTwo) := by
  native_decide

theorem zeroBalance_effect (visibleDb : Database) :
    zeroBalanceInfo.effect visibleDb = some [zeroBalanceRow] := by
  simp [Transformer.vcg, Transformer.inferEffect, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, zeroBalanceInsertBody, zeroBalanceInfo]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_setEffect (visibleDb : Database) :
    Transformer.inferSetEffect 0 [] zeroBalanceInsertBody visibleDb =
      some (SetLanguage.singleton zeroBalanceRow) := by
  simp [Transformer.inferSetEffect, Transformer.insertSetExpr, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, zeroBalanceInsertBody]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_effect_defined :
    Transformer.effectDefinedOn nonnegativeBalances
      zeroBalanceInfo.effect := by
  intro visibleDb _hInv
  exact ⟨[zeroBalanceRow], zeroBalance_effect visibleDb⟩

theorem zeroBalance_guarantee_ok :
    zeroBalanceInfo.guaranteeOk := by
  intro visibleDb localDb hEffect
  have hConst :
      Transformer.inferEffect 0 [] zeroBalanceInsertBody visibleDb = some [zeroBalanceRow] := by
    simpa [zeroBalanceInfo, Transformer.vcg] using zeroBalance_effect visibleDb
  rw [hConst] at hEffect
  injection hEffect with hLocalDb
  subst hLocalDb
  rfl

theorem zeroBalance_preserves_invariant :
    zeroBalanceInfo.preservesInvariant := by
  intro db db' hDb hGuarantee
  subst hGuarantee
  exact nonnegativeBalances_flush_zeroBalanceRow hDb

/-- This is the actual VCG-style proof script for the simplest transaction example:

1. define the generated VCG object (`zeroBalanceInfo`)
2. prove the three obligations that `vcg_sound_false` asks for
3. discharge soundness in one line
-/
theorem zeroBalanceInsert_valid_via_info :
    Logic.GlobalValid nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      zeroBalanceGuarantee
      nonnegativeBalances := by
  exact Transformer.vcg_sound_false 0 Database.uniqueIds zeroBalanceInsertBody
    zeroBalance_effect_defined
    zeroBalance_guarantee_ok
    zeroBalance_preserves_invariant

theorem zeroBalance_effect_any (txnId : TxnId) (visibleDb : Database) :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances (zeroBalanceGuaranteeOf txnId)
      txnId Database.uniqueIds zeroBalanceInsertBody).effect visibleDb = some [zeroBalanceRowOf txnId] := by
  simp [Transformer.vcg, Transformer.inferEffect, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil, zeroBalanceInsertBody, zeroBalanceRowOf]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_effect_defined_any (txnId : TxnId) :
    Transformer.effectDefinedOn nonnegativeBalances
      ((Transformer.vcg (fun _ _ => False) nonnegativeBalances (zeroBalanceGuaranteeOf txnId)
        txnId Database.uniqueIds zeroBalanceInsertBody).effect) := by
  intro visibleDb _hInv
  exact ⟨[zeroBalanceRowOf txnId], zeroBalance_effect_any txnId visibleDb⟩

theorem zeroBalance_guarantee_ok_any (txnId : TxnId) :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances (zeroBalanceGuaranteeOf txnId)
      txnId Database.uniqueIds zeroBalanceInsertBody).guaranteeOk := by
  intro visibleDb localDb hEffect
  have hConst :
      Transformer.inferEffect txnId [] zeroBalanceInsertBody visibleDb = some [zeroBalanceRowOf txnId] := by
    simpa [Transformer.vcg] using zeroBalance_effect_any txnId visibleDb
  rw [hConst] at hEffect
  injection hEffect with hLocalDb
  subst hLocalDb
  rfl

theorem zeroBalance_preserves_invariant_any (txnId : TxnId) :
    (Transformer.vcg (fun _ _ => False) nonnegativeBalances (zeroBalanceGuaranteeOf txnId)
      txnId Database.uniqueIds zeroBalanceInsertBody).preservesInvariant := by
  intro db db' hDb hGuarantee
  subst hGuarantee
  exact nonnegativeBalances_flush_zeroBalanceRowOf hDb

theorem nonnegativeBalances_stable_zeroBalanceGuaranteeOf (txnId : TxnId) :
    Logic.stableAssertion (zeroBalanceGuaranteeOf txnId) nonnegativeBalances := by
  intro db db' hDb hGuarantee
  subst hGuarantee
  exact nonnegativeBalances_flush_zeroBalanceRowOf hDb

theorem nonnegativeBalances_stable_zeroBalanceGuaranteeTwoOf (txnId : TxnId) :
    Logic.stableAssertion (zeroBalanceGuaranteeTwoOf txnId) nonnegativeBalances := by
  intro db db' hDb hGuarantee
  subst hGuarantee
  exact nonnegativeBalances_flush_zeroBalanceRowTwoOf hDb

theorem nonnegativeBalances_stable_zeroBalanceApplyOf (txnId : TxnId) :
    Logic.stableAssertion (StateSpec.graph (zeroBalanceApplyOf txnId)) nonnegativeBalances := by
  intro db db' hDb hGraph
  subst hGraph
  exact nonnegativeBalances_flush_zeroBalanceRowOf hDb

theorem nonnegativeBalances_stable_zeroBalanceApplyTwoOf (txnId : TxnId) :
    Logic.stableAssertion (StateSpec.graph (zeroBalanceApplyTwoOf txnId)) nonnegativeBalances := by
  intro db db' hDb hGraph
  subst hGraph
  exact nonnegativeBalances_flush_zeroBalanceRowTwoOf hDb

theorem zeroBalanceInsert_rg_readCommitted_of_stable {R : Rely} (txnId : TxnId)
    (hStableI : Logic.stableAssertion R nonnegativeBalances) :
    Logic.GlobalRG R nonnegativeBalances
      (.txn txnId (IsolationSpec.readCommitted Database) zeroBalanceInsertBody)
      (zeroBalanceGuaranteeOf txnId)
      nonnegativeBalances := by
  refine Logic.GlobalRG.txn
    (I := nonnegativeBalances)
    (isolation := IsolationSpec.readCommitted Database)
    (txnId := txnId)
    (body := zeroBalanceInsertBody)
    (P := fun localDb visible => localDb = [] ∧ nonnegativeBalances visible)
    (Q := fun localDb visible => localDb = [zeroBalanceRowOf txnId] ∧ nonnegativeBalances visible)
    (G := zeroBalanceGuaranteeOf txnId)
    hStableI ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro localDb baseDb midDb finalDb _ _hR
    constructor <;> simp [IsolationSpec.readCommitted]
  · intro localDb baseDb midDb finalDb _ _hR
    constructor <;> simp [IsolationSpec.readCommitted]
  · intro localDb visibleDb
    simp
  · refine Logic.LocalRG.insert ?_ ?_
    · intro localDb visibleDb visibleDb' hPre hRely
      rcases hPre with ⟨hLocal, hInv⟩
      rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
      exact ⟨hLocal, hStableI _ _ hInv hR⟩
    · intro localDb visibleDb record hPre hEval _hFresh
      rcases hPre with ⟨hLocal, hInv⟩
      subst hLocal
      have hValueEq : some (Value.record zeroBalanceRecord) = some (Value.record record) := by
        rw [← zeroBalance_insert_eval]
        exact hEval
      injection hValueEq with hRecordEq
      cases hRecordEq
      constructor
      · simp [zeroBalanceRowOf]
      · exact hInv
  · intro localDb visibleDb visibleDb' hPost hRely
    rcases hPost with ⟨hLocal, hInv⟩
    rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
    exact ⟨hLocal, hStableI _ _ hInv hR⟩
  · intro localDb visibleDb hPost
    rcases hPost with ⟨hLocal, _hInv⟩
    subst hLocal
    rfl
  · intro db db' hInv hGuarantee
    subst hGuarantee
    exact nonnegativeBalances_flush_zeroBalanceRowOf hInv

theorem zeroBalanceInsertTwo_rg_readCommitted_of_stable {R : Rely} (txnId : TxnId)
    (hStableI : Logic.stableAssertion R nonnegativeBalances) :
    Logic.GlobalRG R nonnegativeBalances
      (.txn txnId (IsolationSpec.readCommitted Database) zeroBalanceInsertBodyTwo)
      (zeroBalanceGuaranteeTwoOf txnId)
      nonnegativeBalances := by
  refine Logic.GlobalRG.txn
    (I := nonnegativeBalances)
    (isolation := IsolationSpec.readCommitted Database)
    (txnId := txnId)
    (body := zeroBalanceInsertBodyTwo)
    (P := fun localDb visible => localDb = [] ∧ nonnegativeBalances visible)
    (Q := fun localDb visible => localDb = [zeroBalanceRowTwoOf txnId] ∧ nonnegativeBalances visible)
    (G := zeroBalanceGuaranteeTwoOf txnId)
    hStableI ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro localDb baseDb midDb finalDb _ _hR
    constructor <;> simp [IsolationSpec.readCommitted]
  · intro localDb baseDb midDb finalDb _ _hR
    constructor <;> simp [IsolationSpec.readCommitted]
  · intro localDb visibleDb
    simp
  · refine Logic.LocalRG.insert ?_ ?_
    · intro localDb visibleDb visibleDb' hPre hRely
      rcases hPre with ⟨hLocal, hInv⟩
      rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
      exact ⟨hLocal, hStableI _ _ hInv hR⟩
    · intro localDb visibleDb record hPre hEval _hFresh
      rcases hPre with ⟨hLocal, hInv⟩
      subst hLocal
      have hValueEq : some (Value.record zeroBalanceRecordTwo) = some (Value.record record) := by
        rw [← zeroBalanceTwo_insert_eval]
        exact hEval
      injection hValueEq with hRecordEq
      cases hRecordEq
      constructor
      · simp [zeroBalanceRowTwoOf]
      · exact hInv
  · intro localDb visibleDb visibleDb' hPost hRely
    rcases hPost with ⟨hLocal, hInv⟩
    rcases hRely with ⟨_baseDb, hR, _hExecOld, _hExecNew⟩
    exact ⟨hLocal, hStableI _ _ hInv hR⟩
  · intro localDb visibleDb hPost
    rcases hPost with ⟨hLocal, _hInv⟩
    subst hLocal
    rfl
  · intro db db' hInv hGuarantee
    subst hGuarantee
    exact nonnegativeBalances_flush_zeroBalanceRowTwoOf hInv

theorem zeroBalancePar_rg :
    Logic.GlobalRG (fun _ _ => False) nonnegativeBalances
      zeroBalanceParProgram
      zeroBalanceParGuarantee
      nonnegativeBalances := by
  refine Logic.GlobalRG.par ?_ ?_
  · exact zeroBalanceInsert_rg_readCommitted_of_stable 10 (by
      intro db db' hInv hR
      rcases hR with hFalse | hG
      · exact False.elim hFalse
      · exact nonnegativeBalances_stable_zeroBalanceGuaranteeTwoOf 20 _ _ hInv hG)
  · exact zeroBalanceInsertTwo_rg_readCommitted_of_stable 20 (by
      intro db db' hInv hR
      rcases hR with hFalse | hG
      · exact False.elim hFalse
      · exact nonnegativeBalances_stable_zeroBalanceGuaranteeOf 10 _ _ hInv hG)

theorem zeroBalancePar_valid :
    Logic.GlobalValid nonnegativeBalances (fun _ _ => False)
      zeroBalanceParProgram
      zeroBalanceParGuarantee
      nonnegativeBalances := by
  exact Logic.globalRG_sound zeroBalancePar_rg

theorem zeroBalanceInsert_valid :
    Logic.GlobalValid nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      zeroBalanceGuarantee
      nonnegativeBalances := by
  exact zeroBalanceInsert_valid_via_info

theorem zeroBalanceInsert_valid_any (txnId : TxnId) :
    Logic.GlobalValid nonnegativeBalances (fun _ _ => False)
      (.txn txnId Database.uniqueIds zeroBalanceInsertBody)
      (zeroBalanceGuaranteeOf txnId)
      nonnegativeBalances := by
  exact Transformer.vcg_sound_false txnId Database.uniqueIds zeroBalanceInsertBody
    (zeroBalance_effect_defined_any txnId)
    (zeroBalance_guarantee_ok_any txnId)
    (zeroBalance_preserves_invariant_any txnId)

theorem zeroBalanceHandler_refines_graph :
    Server.HandlerRefines nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      (StateSpec.graph zeroBalanceApply)
      nonnegativeBalances := by
  simpa [Server.HandlerRefines, StateSpec.graph, zeroBalanceApply, zeroBalanceGuarantee] using
    zeroBalanceInsert_valid

theorem zeroBalanceTxn_parallelValid :
    Server.ParallelValid nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      (fun _ => StateSpec.graph zeroBalanceApply)
      nonnegativeBalances := by
  exact Server.txnParallelValid_of_handlerRefines zeroBalanceHandler_refines_graph

theorem zeroBalanceTxn_parallelValid_exact_via_vcg :
    Server.ParallelValid nonnegativeBalances (fun _ _ => False)
      (.txn 0 Database.uniqueIds zeroBalanceInsertBody)
      (Server.ExactTxnSpec 0 (StateSpec.graph zeroBalanceApply))
      nonnegativeBalances := by
  exact Refinement.txnParallelValid_exact_of_vcg_sound_false
    0 Database.uniqueIds zeroBalanceInsertBody
    zeroBalance_effect_defined
    zeroBalance_guarantee_ok
    zeroBalance_preserves_invariant

theorem zeroBalanceTxn_commitLog_via_vcg
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨(.txn 0 Database.uniqueIds zeroBalanceInsertBody), db⟩
        finalCfg) :
    ∃ events,
      Server.CommitLog
        (Server.ExactTxnSpec 0 (StateSpec.graph zeroBalanceApply))
        db
        events
        finalCfg.globalDb := by
  exact Refinement.txnCommitLog_exact_of_vcg_sound_false
    0 Database.uniqueIds zeroBalanceInsertBody
    zeroBalance_effect_defined
    zeroBalance_guarantee_ok
    zeroBalance_preserves_invariant
    hDb
    hRun

theorem zeroBalanceTxn_parallelValid_invariant
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨(.txn 0 Database.uniqueIds zeroBalanceInsertBody), db⟩
        finalCfg)
    (hDone : Server.ProgramDone finalCfg.program) :
    nonnegativeBalances finalCfg.globalDb := by
  exact Server.ParallelValid.invariant zeroBalanceTxn_parallelValid hDb hRun hDone

theorem zeroBalanceHandler_refines_graph_readCommitted_of_stable {R : Rely} (txnId : TxnId)
    (hStableI : Logic.stableAssertion R nonnegativeBalances) :
    Server.HandlerRefines nonnegativeBalances R
      (.txn txnId (IsolationSpec.readCommitted Database) zeroBalanceInsertBody)
      (StateSpec.graph (zeroBalanceApplyOf txnId))
      nonnegativeBalances := by
  simpa [Server.HandlerRefines, StateSpec.graph, zeroBalanceApplyOf, zeroBalanceGuaranteeOf] using
    (Logic.globalRG_sound
      (zeroBalanceInsert_rg_readCommitted_of_stable (R := R) txnId hStableI))

theorem zeroBalanceHandlerTwo_refines_graph_readCommitted_of_stable {R : Rely} (txnId : TxnId)
    (hStableI : Logic.stableAssertion R nonnegativeBalances) :
    Server.HandlerRefines nonnegativeBalances R
      (.txn txnId (IsolationSpec.readCommitted Database) zeroBalanceInsertBodyTwo)
      (StateSpec.graph (zeroBalanceApplyTwoOf txnId))
      nonnegativeBalances := by
  simpa [Server.HandlerRefines, StateSpec.graph, zeroBalanceApplyTwoOf,
      zeroBalanceGuaranteeTwoOf] using
    (Logic.globalRG_sound
      (zeroBalanceInsertTwo_rg_readCommitted_of_stable (R := R) txnId hStableI))

theorem zeroBalancePar_parallelValid_exact :
    Server.ParallelValid nonnegativeBalances (fun _ _ => False)
      zeroBalanceParProgram
      (Server.CombinedSpecs
        (Server.ExactTxnSpec 10 (StateSpec.graph (zeroBalanceApplyOf 10)))
        (Server.ExactTxnSpec 20 (StateSpec.graph (zeroBalanceApplyTwoOf 20))))
      nonnegativeBalances := by
  refine Server.txnPair_parallelValid_of_handlerRefines ?_ ?_
  · exact zeroBalanceHandler_refines_graph_readCommitted_of_stable
      (R := fun db db' =>
        False ∨ StateSpec.graph (zeroBalanceApplyTwoOf 20) db db')
      10
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyTwoOf 20 _ _ hInv hGraph)
  · exact zeroBalanceHandlerTwo_refines_graph_readCommitted_of_stable
      (R := fun db db' =>
        False ∨ StateSpec.graph (zeroBalanceApplyOf 10) db db')
      20
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyOf 10 _ _ hInv hGraph)

def zeroBalanceParFs (txnId : TxnId) : StateTransformer :=
  if txnId = 10 then
    zeroBalanceApplyOf 10
  else if txnId = 20 then
    zeroBalanceApplyTwoOf 20
  else
    id

theorem zeroBalancePar_exact_specs_subset_graph :
    ∀ txnId db db',
      Server.CombinedSpecs
          (Server.ExactTxnSpec 10 (StateSpec.graph (zeroBalanceApplyOf 10)))
          (Server.ExactTxnSpec 20 (StateSpec.graph (zeroBalanceApplyTwoOf 20)))
          txnId db db' →
        StateSpec.graph (zeroBalanceParFs txnId) db db' := by
  intro txnId db db' hSpec
  rcases hSpec with hLeft | hRight
  · rcases hLeft with ⟨rfl, hGraph⟩
    simpa [StateSpec.graph, zeroBalanceParFs]
      using hGraph
  · rcases hRight with ⟨rfl, hGraph⟩
    simpa [StateSpec.graph, zeroBalanceParFs]
      using hGraph

theorem zeroBalancePar_parallelValid_graph :
    Server.ParallelValid nonnegativeBalances (fun _ _ => False)
      zeroBalanceParProgram
      (fun txnId => StateSpec.graph (zeroBalanceParFs txnId))
      nonnegativeBalances := by
  exact Server.parallelValid_of_specSubset
    zeroBalancePar_parallelValid_exact
    zeroBalancePar_exact_specs_subset_graph

theorem zeroBalancePar_commitSequence
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨zeroBalanceParProgram, db⟩
        finalCfg) :
    ∃ commits,
      Server.CommitSequence
        (fun txnId => StateSpec.graph (zeroBalanceParFs txnId))
        db
        commits
        finalCfg.globalDb := by
  exact Server.parallelValid_commitSequence_of_silentRely
    zeroBalancePar_parallelValid_graph
    false_rely_silent
    hDb
    hRun

theorem zeroBalancePar_foldl
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨zeroBalanceParProgram, db⟩
        finalCfg) :
    ∃ commits,
      finalCfg.globalDb =
        List.foldl (fun current txnId => zeroBalanceParFs txnId current) db commits := by
  rcases Server.parallelValid_foldl_of_graphSpecs
      zeroBalancePar_parallelValid_graph
      false_rely_silent
      hDb
      hRun with
    ⟨commits, _hSeq, hFold⟩
  exact ⟨commits, hFold⟩

inductive ZeroBalanceRequest where
  | first
  | second
deriving DecidableEq, Repr

def zeroBalanceRequestOf (txnId : TxnId) : ZeroBalanceRequest :=
  if txnId = 10 then .first else .second

def zeroBalanceRequestApply : RequestTransformer ZeroBalanceRequest
  | .first => zeroBalanceApplyOf 10
  | .second => zeroBalanceApplyTwoOf 20

theorem zeroBalancePar_exact_specs_subset_request_graph :
    ∀ txnId db db',
      Server.CombinedSpecs
          (Server.ExactTxnSpec 10 (StateSpec.graph (zeroBalanceApplyOf 10)))
          (Server.ExactTxnSpec 20 (StateSpec.graph (zeroBalanceApplyTwoOf 20)))
          txnId db db' →
        RequestSpec.graphAssign zeroBalanceRequestOf zeroBalanceRequestApply txnId db db' := by
  intro txnId db db' hSpec
  rcases hSpec with hLeft | hRight
  · rcases hLeft with ⟨rfl, hGraph⟩
    simpa [RequestSpec.graphAssign, RequestSpec.assign, zeroBalanceRequestOf,
      zeroBalanceRequestApply, StateSpec.graph]
      using hGraph
  · rcases hRight with ⟨rfl, hGraph⟩
    simpa [RequestSpec.graphAssign, RequestSpec.assign, zeroBalanceRequestOf,
      zeroBalanceRequestApply, StateSpec.graph]
      using hGraph

theorem zeroBalancePar_parallelValid_requests :
    Server.ParallelValid nonnegativeBalances (fun _ _ => False)
      zeroBalanceParProgram
      (RequestSpec.graphAssign zeroBalanceRequestOf zeroBalanceRequestApply)
      nonnegativeBalances := by
  exact Server.parallelValid_of_specSubset
    zeroBalancePar_parallelValid_exact
    zeroBalancePar_exact_specs_subset_request_graph

theorem zeroBalancePar_request_foldl
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨zeroBalanceParProgram, db⟩
        finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl
          (fun current req => zeroBalanceRequestApply req current)
          db
          (Server.CommitLog.requests zeroBalanceRequestOf events) := by
  rcases Server.parallelValid_request_foldl_of_graphAssign
      zeroBalancePar_parallelValid_requests
      false_rely_silent
      hDb
      hRun with
    ⟨events, _hLog, hFold⟩
  exact ⟨events, hFold⟩

theorem zeroBalancePar_foldl_via_refinement
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨zeroBalanceParProgram, db⟩
        finalCfg) :
    ∃ commits,
      finalCfg.globalDb =
        List.foldl
          (fun current txnId =>
            _root_.DbAppProgramLogic.Refinement.txnPairFs
              10
              (zeroBalanceApplyOf 10)
              20
              (zeroBalanceApplyTwoOf 20)
              txnId
              current)
          db
          commits := by
  exact _root_.DbAppProgramLogic.Refinement.txnPair_foldl_of_handlerRefines
    (by decide)
    (zeroBalanceHandler_refines_graph_readCommitted_of_stable
      (R := fun db db' => False ∨ StateSpec.graph (zeroBalanceApplyTwoOf 20) db db')
      10
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyTwoOf 20 _ _ hInv hGraph))
    (zeroBalanceHandlerTwo_refines_graph_readCommitted_of_stable
      (R := fun db db' => False ∨ StateSpec.graph (zeroBalanceApplyOf 10) db db')
      20
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyOf 10 _ _ hInv hGraph))
    false_rely_silent
    hDb
    hRun

theorem zeroBalancePar_request_foldl_via_refinement
    {db : Database} {finalCfg : GlobalConfig}
    (hDb : nonnegativeBalances db)
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨zeroBalanceParProgram, db⟩
        finalCfg) :
    ∃ events,
      finalCfg.globalDb =
        List.foldl
          (fun current req => zeroBalanceRequestApply req current)
          db
          (Server.CommitLog.requests zeroBalanceRequestOf events) := by
  exact _root_.DbAppProgramLogic.Refinement.txnPair_request_foldl_of_handlerRefines
    (zeroBalanceHandler_refines_graph_readCommitted_of_stable
      (R := fun db db' => False ∨ StateSpec.graph (zeroBalanceApplyTwoOf 20) db db')
      10
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyTwoOf 20 _ _ hInv hGraph))
    (zeroBalanceHandlerTwo_refines_graph_readCommitted_of_stable
      (R := fun db db' => False ∨ StateSpec.graph (zeroBalanceApplyOf 10) db db')
      20
      (by
        intro db db' hInv hR
        rcases hR with hFalse | hGraph
        · exact False.elim hFalse
        · exact nonnegativeBalances_stable_zeroBalanceApplyOf 10 _ _ hInv hGraph))
    false_rely_silent
    hDb
    hRun

theorem zeroBalance_symbolicVcg_shape (visibleDb : Database) :
    Transformer.symbolicVcg nonnegativeBalances "__inv" 0 zeroBalanceInsertBody visibleDb =
      some
        (SetLanguage.weakenToInvariant "__inv"
          (Transformer.assertionFormula nonnegativeBalances)
          (SetLanguage.singleton zeroBalanceRow)) := by
  simp [Transformer.symbolicVcg, Transformer.weakenSetEffect, zeroBalance_setEffect]

theorem zeroBalance_symbolicVcg_overapprox (visibleDb : Database)
    (hInv : nonnegativeBalances visibleDb) :
    Transformer.overapproximatesRows
      (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        (SetLanguage.singleton zeroBalanceRow))
      [zeroBalanceRow] := by
  exact Transformer.symbolicVcg_overapprox_sound
    nonnegativeBalances
    "__inv"
    0
    zeroBalanceInsertBody
    visibleDb
    [zeroBalanceRow]
    (SetLanguage.singleton zeroBalanceRow)
    hInv
    (zeroBalance_setEffect visibleDb)
    (by simpa [Transformer.vcg] using zeroBalance_effect visibleDb)

theorem zeroBalance_symbolicVcg_contains_row (visibleDb : Database)
    (hInv : nonnegativeBalances visibleDb) :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        (SetLanguage.singleton zeroBalanceRow))
      zeroBalanceRow := by
  exact zeroBalance_symbolicVcg_overapprox visibleDb hInv zeroBalanceRow (by simp)

def zeroBalanceWriteMembership : FirstOrder.MembershipFormula :=
  Option.get! (FirstOrder.inferWriteMembership 0 [] "x" zeroBalanceInsertBody)

theorem zeroBalance_inferWriteMembership :
    FirstOrder.inferWriteMembership 0 [] "x" zeroBalanceInsertBody =
      some zeroBalanceWriteMembership := by
  unfold zeroBalanceWriteMembership
  simp [FirstOrder.inferWriteMembership, zeroBalanceInsertBody, Transformer.evalInEnv,
    Transformer.instantiateExpr_nil]
  rw [zeroBalance_insert_eval]
  rfl

theorem zeroBalance_inferWriteMembership_contains_row (visibleDb : Database) :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem "x" zeroBalanceRow)
      zeroBalanceWriteMembership := by
  have hSound :=
    FirstOrder.inferWriteMembership_sound 0 [] "x" zeroBalanceInsertBody
      zeroBalanceWriteMembership visibleDb [zeroBalanceRow] zeroBalanceRow
      zeroBalance_inferWriteMembership
      (by simpa [Transformer.vcg] using zeroBalance_effect visibleDb)
  exact hSound.2 (by simp)

/-! ## Read/write symbolic example (`addInterest`) -/

def interestBaseRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 4)]⟩

def interestBaseRow : Row :=
  Row.fromInsert 0 interestBaseRecord

def interestUpdatedRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 5)]⟩

def interestUpdatedRow : Row :=
  interestBaseRow.overwrite 1 interestUpdatedRecord

def addInterestBody : Semantics.Program :=
  .select "selected" "r"
    (.binop .eq (.proj (.var "r") "id") (.int 1))
    (.foreach (.var "selected") "done" "acct"
      (.update "r"
        (.withUpdates (.var "r")
          [("bal", .binop .add (.proj (.var "acct") "bal") (.int 1))])
        (.binop .eq (.proj (.var "r") "id") (.proj (.var "acct") "id"))))

def addInterestTxn : Semantics.Program :=
  .txn 1 Database.snapshotIsolation addInterestBody

def addInterestSetExpr : SetLanguage.SetExpr :=
  Option.get! (Transformer.inferSetEffect 1 [] addInterestBody [interestBaseRow])

theorem interestBase_nonnegative :
    nonnegativeBalances [interestBaseRow] := by
  intro row hMem
  rcases List.mem_singleton.mp hMem with rfl
  simp [interestBaseRow, interestBaseRecord, Row.fromInsert, RecordLit.lookup?]

theorem addInterest_effect :
    Transformer.inferEffect 1 [] addInterestBody [interestBaseRow] = some [interestUpdatedRow] := by
  native_decide

/-- A concrete VCG object for the read/write example. Unlike `zeroBalanceInfo`, we only inspect its
effect on the intended initial state; proving `vcg_sound_false` for this example requires a more
careful global invariant than we want in this walkthrough. -/
def addInterestInfo : Transformer.TransactionVCG :=
  Transformer.vcg (fun _ _ => False) nonnegativeBalances
    (fun db db' => db' = Database.flush [interestUpdatedRow] db)
    1 Database.snapshotIsolation addInterestBody

theorem addInterest_effect_via_info :
    addInterestInfo.effect [interestBaseRow] = some [interestUpdatedRow] := by
  simpa [addInterestInfo, Transformer.vcg] using addInterest_effect

theorem interestUpdatedRow_id :
    interestUpdatedRow.id? = some 1 := by
  native_decide

theorem interestUpdatedRow_lookup_bal :
    interestUpdatedRow.visible.lookup? "bal" = some (.int 5) := by
  native_decide

theorem addInterest_flush_base :
    Database.flush [interestUpdatedRow] [interestBaseRow] = [interestUpdatedRow] := by
  native_decide

theorem nonnegativeBalances_flush_interestUpdatedRow :
    nonnegativeBalances (Database.flush [interestUpdatedRow] [interestBaseRow]) := by
  rw [addInterest_flush_base]
  intro row hMem
  rcases List.mem_singleton.mp hMem with rfl
  simpa [interestUpdatedRow_lookup_bal] using (show (0 : Int) <= 5 from by decide)

/-- The read/write VCG is defined on the intended singleton account state. -/
theorem addInterest_effect_defined_on_base :
    ∃ localDb, addInterestInfo.effect [interestBaseRow] = some localDb := by
  exact ⟨[interestUpdatedRow], addInterest_effect_via_info⟩

/-- On the intended input, the chosen guarantee is exactly the flush of the inferred delta. -/
theorem addInterest_guarantee_on_base :
    (fun db db' => db' = Database.flush [interestUpdatedRow] db)
      [interestBaseRow]
      (Database.flush [interestUpdatedRow] [interestBaseRow]) := by
  rfl

/-- The concrete post-state produced by the VCG still satisfies the running invariant. -/
theorem addInterest_preserves_invariant_on_base :
    nonnegativeBalances (Database.flush [interestUpdatedRow] [interestBaseRow]) := by
  exact nonnegativeBalances_flush_interestUpdatedRow

theorem addInterest_inferable :
    Transformer.SetInferable addInterestBody := by
  simp [Transformer.SetInferable, addInterestBody]

theorem addInterest_setEffect :
    Transformer.inferSetEffect 1 [] addInterestBody [interestBaseRow] = some addInterestSetExpr := by
  apply Transformer.option_eq_some_get!
  intro hNone
  rcases Transformer.inferSetEffect_some_of_inferEffect_some
      1 [] addInterestBody [interestBaseRow] [interestUpdatedRow]
      addInterest_inferable addInterest_effect with ⟨s, hSet⟩
  rw [hNone] at hSet
  cases hSet

theorem addInterest_symbolicVcg_shape :
    Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody [interestBaseRow] =
      some
        (SetLanguage.weakenToInvariant "__inv"
          (Transformer.assertionFormula nonnegativeBalances)
          addInterestSetExpr) := by
  simp [Transformer.symbolicVcg, Transformer.weakenSetEffect, addInterest_setEffect]

theorem addInterest_symbolicVcg_overapprox :
    Transformer.overapproximatesRows
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        addInterestSetExpr)
      [interestUpdatedRow] := by
  exact Transformer.symbolicVcg_overapprox_sound
    nonnegativeBalances
    "__inv"
    1
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    addInterestSetExpr
    interestBase_nonnegative
    addInterest_setEffect
    addInterest_effect

theorem addInterest_symbolicVcg_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        addInterestSetExpr)
      interestUpdatedRow := by
  exact addInterest_symbolicVcg_overapprox interestUpdatedRow (by simp)

theorem addInterest_symbolicVcg_contains_updatedRow_direct :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get! (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody [interestBaseRow]))
      interestUpdatedRow := by
  exact Transformer.symbolicVcg_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_symbolicVcgForTxn_info :
    ∃ info, Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn = some info := by
  refine ⟨Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody, ?_⟩
  simp [Transformer.symbolicVcgForTxn, addInterestTxn]

theorem addInterest_symbolicVcgForTxn_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get!
        ((Option.get! (Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn))
          [interestBaseRow]))
      interestUpdatedRow := by
  have hInfo :
      Transformer.symbolicVcgForTxn nonnegativeBalances "__inv" addInterestTxn =
        some (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody) := by
    simp [Transformer.symbolicVcgForTxn, addInterestTxn]
  exact Transformer.symbolicVcgForTxn_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    Database.snapshotIsolation
    addInterestBody
    (Transformer.symbolicVcg nonnegativeBalances "__inv" 1 addInterestBody)
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    hInfo
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_symbolicPostForTxn_contains_updatedRow :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (Option.get! (Transformer.symbolicPostForTxn nonnegativeBalances "__inv" addInterestTxn [interestBaseRow]))
      interestUpdatedRow := by
  exact Transformer.symbolicPostForTxn_sound_of_inferEffect_some
    nonnegativeBalances
    "__inv"
    1
    Database.snapshotIsolation
    addInterestBody
    [interestBaseRow]
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferable
    interestBase_nonnegative
    addInterest_effect
    (by simp)

theorem addInterest_rowPredicateFO_holds :
    FirstOrder.denote
      (DbAppProgramLogic.Env.insert [] "r" (.record interestBaseRecord))
      (FirstOrder.rowPredicateFormula [] "r"
        (.binop .eq (.proj (.var "r") "id") (.int 1))) := by
  rw [FirstOrder.denote_rowPredicateFormula]
  native_decide

def addInterestUpdateEnv : DbAppProgramLogic.Env :=
  [("acct", .record interestBaseRecord)]

def addInterestUpdateExpr : Expr :=
  .withUpdates (.var "r")
    [("bal", .binop .add (.proj (.var "acct") "bal") (.int 1))]

def addInterestUpdatePredicate : Expr :=
  .binop .eq (.proj (.var "r") "id") (.proj (.var "acct") "id")

theorem addInterest_updateMembershipFO_holds :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      (FirstOrder.encodeUpdateMembership
        "x" 1 addInterestUpdateEnv "r" addInterestUpdateExpr addInterestUpdatePredicate) := by
  have hNe : ("x" : VarName) ≠ "r" := by
    decide
  rw [FirstOrder.encodeUpdateMembership_sound
    "x" 1 addInterestUpdateEnv "r" addInterestUpdateExpr addInterestUpdatePredicate
    [interestBaseRow] interestUpdatedRow hNe]
  simp [Transformer.updateSetExpr, Transformer.updateSetExprWith, Transformer.rowPredicateFormula,
    SetLanguage.denote, SetLanguage.empty, addInterestUpdateEnv, addInterestUpdateExpr,
    addInterestUpdatePredicate, interestBaseRow, interestBaseRecord, interestUpdatedRow,
    interestUpdatedRecord, Row.fromInsert, Row.overwrite, RecordLit.lookup?]
  refine ⟨interestBaseRow, ?_, ?_, ?_⟩
  · simp [SetLanguage.Env.ofDatabases]
    rfl
  · native_decide
  · have hLookup :
        (((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "r" interestBaseRow).bindElem
          (Transformer.defaultOutVar "r") interestUpdatedRow).lookupElem? "r" = some interestBaseRow := by
      simp [Transformer.defaultOutVar, SetLanguage.Env.lookupElem?, SetLanguage.Env.lookupElemList?,
        SetLanguage.Env.bindElem]
    have hExists :
        ∃ updated,
          Expr.eval
              (Semantics.instantiateRecord "r" interestBaseRow.visible
                (Transformer.instantiateExpr addInterestUpdateEnv ["r"] addInterestUpdateExpr)) =
            some (.record updated) ∧
          interestUpdatedRow = interestBaseRow.overwrite 1 updated := by
      refine ⟨interestUpdatedRecord, ?_, ?_⟩
      · native_decide
      · simp [interestUpdatedRow, interestUpdatedRecord, interestBaseRow, Row.overwrite]
    simpa [hLookup] using hExists

def addInterestFullMembership : FirstOrder.MembershipFormula :=
  Option.get! (FirstOrder.inferMembershipFull 1 [] "x" addInterestBody [interestBaseRow])

theorem addInterest_membershipEncodable :
    FirstOrder.MembershipEncodable "x" addInterestBody := by
  simp [FirstOrder.MembershipEncodable, addInterestBody]

theorem addInterest_inferMembershipFull :
    FirstOrder.inferMembershipFull 1 [] "x" addInterestBody [interestBaseRow] =
      some addInterestFullMembership := by
  apply Transformer.option_eq_some_get!
  intro hNone
  rcases FirstOrder.inferMembershipFull_some_of_inferEffect_some
      1 [] "x" addInterestBody [interestBaseRow] [interestUpdatedRow]
      addInterest_membershipEncodable addInterest_effect with ⟨φ, hFormula⟩
  rw [hNone] at hFormula
  cases hFormula

theorem addInterest_inferMembershipFull_contains_updatedRow :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      addInterestFullMembership := by
  have hSound :=
    FirstOrder.inferMembershipFull_sound 1 [] "x" addInterestBody [interestBaseRow]
      addInterestFullMembership [interestUpdatedRow] interestUpdatedRow
      addInterest_inferMembershipFull addInterest_effect
  exact hSound.2 (by simp)

theorem addInterest_fullMembership_matches_setEffect :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] [interestBaseRow]).bindElem "x" interestUpdatedRow)
      addInterestFullMembership ↔
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      addInterestSetExpr
      interestUpdatedRow := by
  exact FirstOrder.inferMembershipFull_matches_inferSetEffect
    1 [] "x" addInterestBody [interestBaseRow]
    addInterestFullMembership
    addInterestSetExpr
    [interestUpdatedRow]
    interestUpdatedRow
    addInterest_inferMembershipFull
    addInterest_setEffect
    addInterest_effect

theorem addInterest_fullMembership_implies_symbolicVcg :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] [interestBaseRow])
      (SetLanguage.weakenToInvariant "__inv"
        (Transformer.assertionFormula nonnegativeBalances)
        addInterestSetExpr)
      interestUpdatedRow := by
  exact FirstOrder.inferMembershipFull_implies_weakened_setEffect
    nonnegativeBalances
    "__inv"
    1
    []
    "x"
    addInterestBody
    [interestBaseRow]
    addInterestFullMembership
    addInterestSetExpr
    [interestUpdatedRow]
    interestUpdatedRow
    interestBase_nonnegative
    addInterest_inferMembershipFull
    addInterest_setEffect
    addInterest_effect
    addInterest_inferMembershipFull_contains_updatedRow

theorem zeroBalance_singletonMembershipFO_holds :
    FirstOrder.denoteMembership
      ((SetLanguage.Env.ofDatabases [] []).bindElem "x" zeroBalanceRow)
      (FirstOrder.encodeSingletonMembership "x" zeroBalanceRow) := by
  rw [FirstOrder.encodeSingletonMembership_denote]
  simp [SetLanguage.denote, SetLanguage.singleton]

end Examples

end DbAppProgramLogic
