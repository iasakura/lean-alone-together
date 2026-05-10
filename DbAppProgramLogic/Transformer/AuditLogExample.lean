import DbAppProgramLogic.Transformer.InferenceCapstone

/-!
# Audit log: parallel INSERTs with a meaningful inter-transaction rely

Two transactions run in parallel; each one inserts an audit row tagged with
its own integer `auditId`. The inserted record exposes `auditId` in the
visible payload, while `Row.txn` separately tracks the inserting transaction.

The point of this example, compared to `zeroBalancePar_example`, is the
**non-trivial concrete rely**:

* The invariant is `auditAppendOnly db := ∀ row ∈ db, ¬row.del` — the
  database never holds tombstoned rows.
* Each transaction's guarantee is
  `auditAppendsOnly db db' := ∀ row ∈ db', row ∈ db ∨ ¬row.del` — anything
  the post-state contains was either already there or is alive.
* Each transaction therefore tolerates the *other* one's guarantee in its
  rely (`R ∨ Gother`): a concurrent audit-log INSERT only ever appends
  non-deleted rows, so `auditAppendOnly` is stable under it.

Side conditions that were abstract in `zeroBalancePar_example` are discharged
concretely here:

* `hPreserveLeft / hPreserveRight` (`I` preserved by `G`) — proved from
  the structure of `auditAppendsOnly`.
* `hGuaranteeLeft / hGuaranteeRight` (`transformerPost → G`) — proved
  structurally from the shape of `Database.flush`.
* `hExecStable*` / `hCommitIsoStable*` — by specializing to read-committed
  isolation (`exec`/`commit ≡ True`), these become trivial.
* `hQstable*` — the inserted-row set ignores the visible database, so
  `transformerPost` is invariant under any rely-mod step.
* `hStablePre*` — reduces to `auditAppendOnly`-stability under
  `R ∨ auditAppendsOnly`.

The only remaining hypotheses are: `R` preserves `auditAppendOnly`, and
the two insertions are fresh.
-/

namespace DbAppProgramLogic

namespace Transformer

open SetLanguage

/-! ## Audit-log program -/

/-- An audit-log payload literal tagged with an integer `auditId`. -/
private def auditPayload (auditId : Int) : RecordLit :=
  ⟨[("id", .int auditId), ("auditId", .int auditId)]⟩

/-- INSERT body that adds the `auditPayload auditId` row. -/
private def auditInsertBody (auditId : Int) : Semantics.Program :=
  .insert (.record [("id", Expr.int auditId), ("auditId", Expr.int auditId)])

/-- Symbolic inserted-row set produced by `PaperInfer.insert` for the audit-log body. -/
private def auditInsertedRowSet (txnId : TxnId) (auditId : Int) : SetLanguage.SetExpr :=
  insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv)
    (.record [("id", Expr.int auditId), ("auditId", Expr.int auditId)])

private theorem auditPayload_eval (auditId : Int) :
    Expr.eval (Expr.record [("id", Expr.int auditId), ("auditId", Expr.int auditId)]) =
      some (.record (auditPayload auditId)) := rfl

/-! ## Concrete invariant and guarantee -/

/-- Every row in the database is alive (not marked deleted). -/
def auditAppendOnly : Assertion := fun db => ∀ row ∈ db, ¬row.del

/-- Any row appearing in the post-state is either already in the pre-state, or is
not marked deleted. -/
def auditAppendsOnly : Guarantee :=
  fun db db' => ∀ row ∈ db', row ∈ db ∨ ¬row.del

/-- `auditAppendOnly` is preserved under `auditAppendsOnly`. -/
theorem auditAppendOnly_preserve :
    ∀ db db', auditAppendOnly db → auditAppendsOnly db db' → auditAppendOnly db' := by
  intro db db' hI hG row hRow
  rcases hG row hRow with hMem | hAlive
  · exact hI row hMem
  · exact hAlive

/-- `Database.flush` only ever adds rows that were already in the visible database
or are alive. This is a purely structural fact about `flush` and does not depend on
the symbolic post-condition produced by the transformer. -/
theorem auditAppendsOnly_flush (localDb visibleDb : Database) :
    auditAppendsOnly visibleDb (Database.flush localDb visibleDb) := by
  intro row hRow
  unfold Database.flush at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with hPreserved | hCommitted
  · exact Or.inl (List.mem_filter.mp hPreserved).1
  · have hAlive := (List.mem_filter.mp hCommitted).2
    have hDel : row.del = false := by
      cases hcase : row.del with
      | false => rfl
      | true => simp [hcase] at hAlive
    exact Or.inr (by simp [hDel])

/-- Stability of `auditAppendOnly` under the combined rely `R ∨ auditAppendsOnly`,
provided `R` itself preserves `auditAppendOnly`. -/
theorem auditAppendOnly_stable_under_R_or_appendsOnly
    (R : Rely)
    (hRpreserve : ∀ db db', auditAppendOnly db → R db db' → auditAppendOnly db') :
    Logic.stableAssertion (fun db db' => R db db' ∨ auditAppendsOnly db db') auditAppendOnly := by
  intro db db' hI hStep
  rcases hStep with hR | hG
  · exact hRpreserve db db' hI hR
  · exact auditAppendOnly_preserve db db' hI hG

/-! ## PaperInfer derivation for the audit-log INSERT body -/

/-- `PaperInfer.insert` derivation for the audit-log body, parameterized by `auditId`. -/
private theorem paperInfer_auditInsert
    (R : LocalRely) (txnId : TxnId) (I : Assertion) (auditId : Int)
    (hStablePre : Logic.stableBiAssertion R (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb (auditPayload auditId)) :
    PaperInfer R txnId I SetLanguage.empty (auditInsertBody auditId)
      (auditInsertedRowSet txnId auditId) := by
  refine PaperInfer.insert (env := { scalarVars := [], setVars := [] })
    (expr := .record [("id", Expr.int auditId), ("auditId", Expr.int auditId)])
    hStablePre ?hClosed ?hFresh
  · intro _visibleDb _row
    rfl
  · intro localDb visibleDb record hPre hEval
    have hEq : record = auditPayload auditId := by
      have hEvalLit :
          Expr.eval
              (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) []
                (.record [("id", Expr.int auditId), ("auditId", Expr.int auditId)])) =
            some (.record (auditPayload auditId)) := by
        simpa [instantiateSymExpr_noScalars] using auditPayload_eval auditId
      have := hEval.symm.trans hEvalLit
      simpa using this
    subst hEq
    exact hFresh localDb visibleDb hPre

/-! ## End-to-end parallel audit-log capstone

Specialized to **read-committed** isolation, where `exec`/`commit` are the trivial
relation `fun _ _ _ => True`. This kills four isolation-stability hypotheses
outright; the post-condition stability is also trivial because the inserted-row
set is independent of the visible database; and the precondition stability
reduces to `auditAppendOnly`-stability under `R ∨ auditAppendsOnly`.

What remains: the external rely must preserve `auditAppendOnly`, and each insert
must be fresh against the current local/visible databases. -/

theorem paperInfer_globalValid_auditLogPar_example
    (R : Rely)
    (txnIdLeft txnIdRight : TxnId)
    (auditIdLeft auditIdRight : Int)
    (hRpreserve : ∀ db db', auditAppendOnly db → R db db' → auditAppendOnly db')
    (hFreshLeft :
      ∀ localDb visibleDb,
        transformerPre auditAppendOnly SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb (auditPayload auditIdLeft))
    (hFreshRight :
      ∀ localDb visibleDb,
        transformerPre auditAppendOnly SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb (auditPayload auditIdRight)) :
    Logic.GlobalValid auditAppendOnly R
      (.par
        (.txn txnIdLeft (IsolationSpec.readCommitted Database) (auditInsertBody auditIdLeft))
        (.txn txnIdRight (IsolationSpec.readCommitted Database) (auditInsertBody auditIdRight)))
      (fun db db' => auditAppendsOnly db db' ∨ auditAppendsOnly db db') auditAppendOnly := by
  -- Stability of the invariant under the combined rely `R ∨ auditAppendsOnly`.
  have hStableI := auditAppendOnly_stable_under_R_or_appendsOnly R hRpreserve
  -- Read-committed makes `exec`/`commit` trivially `True`, so isolation stability is automatic.
  have hExecStable :
      Logic.stableIsolation
        (fun db db' => R db db' ∨ auditAppendsOnly db db')
        (IsolationSpec.readCommitted Database).exec := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  have hCommitIsoStable :
      Logic.stableIsolation
        (fun db db' => R db db' ∨ auditAppendsOnly db db')
        (IsolationSpec.readCommitted Database).commit := by
    intro _ _ _ _ _ _ _; exact ⟨trivial, trivial⟩
  -- The empty-context precondition is just `localDb = [] ∧ I visibleDb`, so its
  -- stability under any rely-mod step reduces to `I`-stability under `R ∨ G`.
  have hStablePre : ∀ (txnId : TxnId),
      Logic.stableBiAssertion
        (Logic.relyMod
          (fun db db' => R db db' ∨ auditAppendsOnly db db')
          (IsolationSpec.readCommitted Database).exec)
        (transformerPre auditAppendOnly SetLanguage.empty) := by
    intro _ localDb v v' hPre hStep
    obtain ⟨_, hRG, _, _⟩ := hStep
    exact ⟨hPre.1, hStableI v v' hPre.2 hRG⟩
  -- The post-condition mentions `auditInsertedRowSet`, which ignores the visible
  -- database, so it is invariant under any rely-mod step.
  have hQstable : ∀ (txnId : TxnId) (auditId : Int),
      Logic.stableBiAssertion
        (Logic.relyMod
          (fun db db' => R db db' ∨ auditAppendsOnly db db')
          (IsolationSpec.readCommitted Database).commit)
        (transformerPost SetLanguage.empty (auditInsertedRowSet txnId auditId)) := by
    intro _ _ _ _ _ hPost _; exact hPost
  have hInferLeft :=
    paperInfer_auditInsert
      (Logic.relyMod (fun db db' => R db db' ∨ auditAppendsOnly db db')
        (IsolationSpec.readCommitted Database).exec)
      txnIdLeft auditAppendOnly auditIdLeft (hStablePre txnIdLeft) hFreshLeft
  have hInferRight :=
    paperInfer_auditInsert
      (Logic.relyMod (fun db db' => R db db' ∨ auditAppendsOnly db db')
        (IsolationSpec.readCommitted Database).exec)
      txnIdRight auditAppendOnly auditIdRight (hStablePre txnIdRight) hFreshRight
  -- The guarantee discharge is uniform in the inserted-row set because it depends
  -- only on the structure of `Database.flush`.
  have hGuaranteeLeft :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty (auditInsertedRowSet txnIdLeft auditIdLeft)
            localDb visibleDb →
          auditAppendsOnly visibleDb (Database.flush localDb visibleDb) :=
    fun localDb visibleDb _ => auditAppendsOnly_flush localDb visibleDb
  have hGuaranteeRight :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty (auditInsertedRowSet txnIdRight auditIdRight)
            localDb visibleDb →
          auditAppendsOnly visibleDb (Database.flush localDb visibleDb) :=
    fun localDb visibleDb _ => auditAppendsOnly_flush localDb visibleDb
  exact PaperInfer.globalValid_txnPar
    hExecStable hCommitIsoStable hInferLeft (hQstable txnIdLeft auditIdLeft) hGuaranteeLeft
    hExecStable hCommitIsoStable hInferRight (hQstable txnIdRight auditIdRight) hGuaranteeRight
    auditAppendOnly_preserve auditAppendOnly_preserve hStableI hStableI

end Transformer

end DbAppProgramLogic


