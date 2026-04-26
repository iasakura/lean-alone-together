import DbAppProgramLogic.Transformer.InferenceCapstone
import DbAppProgramLogic.Transformer.InferenceExample

/-!
End-to-end worked example: a concrete INSERT transaction carried through the entire
paper-aligned pipeline (Fig. 13 derivation → Theorem C.18 → Theorem C.19 →
`GlobalValid` via `txnGlobalValid_of_localValid`).

The program under verification is the `zeroBalance`-style single-INSERT body
`.insert (.record [("id", Expr.int 1), ("bal", Expr.int 0)])`, wrapped in a `.txn`
with a user-supplied isolation level. Every side-condition of `PaperInfer.globalValid_txn`
is passed as a theorem-level hypothesis; the body of the theorem shows how the
INSERT rule of `PaperInfer` plugs into the single-txn capstone lemma.
-/

namespace DbAppProgramLogic

namespace Transformer

open SetLanguage

/-- The concrete record literal used by the worked example. -/
private def exampleRecord : RecordLit :=
  ⟨[("id", .int 1), ("bal", .int 0)]⟩

/-- The concrete insert body used by the worked example. -/
private def exampleInsertBody : Semantics.Program :=
  .insert (.record [("id", Expr.int 1), ("bal", Expr.int 0)])

/-- Symbolic `insertedRowSet` produced by `PaperInfer.insert` for the worked example, using an
empty symbolic environment. -/
private def exampleInsertedRowSet (txnId : TxnId) : SetLanguage.SetExpr :=
  insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv)
    (.record [("id", Expr.int 1), ("bal", Expr.int 0)])

/-- The closed record literal evaluates to the intended record. -/
private theorem exampleRecord_eval :
    Expr.eval (Expr.record [("id", Expr.int 1), ("bal", Expr.int 0)]) =
      some (.record exampleRecord) := by
  rfl

/-- Substituting `_row` inside a closed record literal is a no-op, so the `hClosed` side-condition
of `PaperInfer.insert` reduces to `rfl`. -/
private theorem exampleRecord_subst_row (row : Row) :
    Expr.eval
        (Expr.subst "_row" (.lit (.record row.visible))
          (.record [("id", Expr.int 1), ("bal", Expr.int 0)])) =
      Expr.eval (.record [("id", Expr.int 1), ("bal", Expr.int 0)]) := by
  rfl

/-- **End-to-end single-transaction INSERT example.**

Assembles a Fig. 13 derivation for the concrete `.insert` body, runs it through
`PaperInfer.globalValid_txn`, and produces a paper-aligned `GlobalValid` triple. All
side-conditions (isolation stability, precondition stability, freshness, post-stability on the
commit rely, guarantee match, invariant preservation) are taken as hypotheses so the example is
self-contained without depending on any legacy VCG infrastructure. -/
theorem paperInfer_globalValid_zeroBalanceInsert_example
    (R : Rely) (I : Assertion) (txnId : TxnId)
    (isolation : IsolationSpec Database) (G : Guarantee)
    (hStableI : Logic.stableAssertion R I)
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
    (hStablePre :
      Logic.stableBiAssertion (Logic.relyMod R isolation.exec)
        (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb exampleRecord)
    (hQstable :
      Logic.stableBiAssertion (Logic.relyMod R isolation.commit)
        (transformerPost SetLanguage.empty (exampleInsertedRowSet txnId)))
    (hGuarantee :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty (exampleInsertedRowSet txnId) localDb visibleDb →
          G visibleDb (Database.flush localDb visibleDb))
    (hPreserve : ∀ db db', I db → G db db' → I db') :
    Logic.GlobalValid I R (.txn txnId isolation exampleInsertBody) G I := by
  -- Build the Fig. 13 derivation for the INSERT body.
  have hInfer :
      PaperInfer (Logic.relyMod R isolation.exec) txnId I SetLanguage.empty
        exampleInsertBody (exampleInsertedRowSet txnId) := by
    refine PaperInfer.insert (env := { scalarVars := [], setVars := [] })
      (expr := .record [("id", Expr.int 1), ("bal", Expr.int 0)])
      hStablePre ?hClosed ?hFresh
    · intro visibleDb row
      rfl
    · intro localDb visibleDb record hPre hEval
      have hEq : record = exampleRecord := by
        have hEvalLit :
            Expr.eval
                (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) []
                  (.record [("id", Expr.int 1), ("bal", Expr.int 0)])) =
              some (.record exampleRecord) := by
          simpa [instantiateSymExpr_noScalars] using exampleRecord_eval
        have := hEval.symm.trans hEvalLit
        simpa using this
      subst hEq
      exact hFresh localDb visibleDb hPre
  -- Chain through the single-transaction capstone lemma.
  exact PaperInfer.globalValid_txn hStableI hExecStable hCommitIsoStable
    hInfer hQstable hGuarantee hPreserve

/-! ## Parallel INSERT example -/

/-- The second concrete record literal for the parallel example (distinct id). -/
private def exampleRecordTwo : RecordLit :=
  ⟨[("id", .int 2), ("bal", .int 0)]⟩

/-- The second concrete insert body. -/
private def exampleInsertBodyTwo : Semantics.Program :=
  .insert (.record [("id", Expr.int 2), ("bal", Expr.int 0)])

/-- Symbolic `insertedRowSet` for the second body. -/
private def exampleInsertedRowSetTwo (txnId : TxnId) : SetLanguage.SetExpr :=
  insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv)
    (.record [("id", Expr.int 2), ("bal", Expr.int 0)])

/-- The second record literal evaluates to the intended record. -/
private theorem exampleRecordTwo_eval :
    Expr.eval (Expr.record [("id", Expr.int 2), ("bal", Expr.int 0)]) =
      some (.record exampleRecordTwo) := by
  rfl

/-- `PaperInfer.insert` derivation for the left-hand body under an arbitrary local rely. -/
private theorem paperInfer_exampleInsert
    (R : LocalRely) (txnId : TxnId) (I : Assertion)
    (hStablePre : Logic.stableBiAssertion R (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb exampleRecord) :
    PaperInfer R txnId I SetLanguage.empty exampleInsertBody
      (exampleInsertedRowSet txnId) := by
  refine PaperInfer.insert (env := { scalarVars := [], setVars := [] })
    (expr := .record [("id", Expr.int 1), ("bal", Expr.int 0)])
    hStablePre ?hClosed ?hFresh
  · intro visibleDb row
    rfl
  · intro localDb visibleDb record hPre hEval
    have hEq : record = exampleRecord := by
      have hEvalLit :
          Expr.eval
              (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) []
                (.record [("id", Expr.int 1), ("bal", Expr.int 0)])) =
            some (.record exampleRecord) := by
        simpa [instantiateSymExpr_noScalars] using exampleRecord_eval
      have := hEval.symm.trans hEvalLit
      simpa using this
    subst hEq
    exact hFresh localDb visibleDb hPre

/-- `PaperInfer.insert` derivation for the right-hand body under an arbitrary local rely. -/
private theorem paperInfer_exampleInsertTwo
    (R : LocalRely) (txnId : TxnId) (I : Assertion)
    (hStablePre : Logic.stableBiAssertion R (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb exampleRecordTwo) :
    PaperInfer R txnId I SetLanguage.empty exampleInsertBodyTwo
      (exampleInsertedRowSetTwo txnId) := by
  refine PaperInfer.insert (env := { scalarVars := [], setVars := [] })
    (expr := .record [("id", Expr.int 2), ("bal", Expr.int 0)])
    hStablePre ?hClosed ?hFresh
  · intro visibleDb row
    rfl
  · intro localDb visibleDb record hPre hEval
    have hEq : record = exampleRecordTwo := by
      have hEvalLit :
          Expr.eval
              (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) []
                (.record [("id", Expr.int 2), ("bal", Expr.int 0)])) =
            some (.record exampleRecordTwo) := by
        simpa [instantiateSymExpr_noScalars] using exampleRecordTwo_eval
      have := hEval.symm.trans hEvalLit
      simpa using this
    subst hEq
    exact hFresh localDb visibleDb hPre

/-- **End-to-end parallel INSERT example.**

Two independent INSERT transactions composed in parallel yield a paper-aligned `GlobalValid`
triple whose combined guarantee is the disjunction of the per-transaction guarantees. Each
transaction's Fig. 13 derivation is built locally by `paperInfer_exampleInsert`/
`paperInfer_exampleInsertTwo`; everything is then plumbed through
`PaperInfer.globalValid_txnPar`. -/
theorem paperInfer_globalValid_zeroBalancePar_example
    (R : Rely) (I : Assertion)
    (txnIdLeft txnIdRight : TxnId)
    (isoLeft isoRight : IsolationSpec Database)
    (Gleft Gright : Guarantee)
    -- Left transaction side-conditions
    (hExecStableLeft :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gright db db') isoLeft.exec)
    (hCommitIsoStableLeft :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gright db db') isoLeft.commit)
    (hStablePreLeft :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gright db db') isoLeft.exec)
        (transformerPre I SetLanguage.empty))
    (hFreshLeft :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb exampleRecord)
    (hQstableLeft :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gright db db') isoLeft.commit)
        (transformerPost SetLanguage.empty (exampleInsertedRowSet txnIdLeft)))
    (hGuaranteeLeft :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty (exampleInsertedRowSet txnIdLeft) localDb visibleDb →
          Gleft visibleDb (Database.flush localDb visibleDb))
    -- Right transaction side-conditions
    (hExecStableRight :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gleft db db') isoRight.exec)
    (hCommitIsoStableRight :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gleft db db') isoRight.commit)
    (hStablePreRight :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gleft db db') isoRight.exec)
        (transformerPre I SetLanguage.empty))
    (hFreshRight :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb exampleRecordTwo)
    (hQstableRight :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gleft db db') isoRight.commit)
        (transformerPost SetLanguage.empty (exampleInsertedRowSetTwo txnIdRight)))
    (hGuaranteeRight :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty (exampleInsertedRowSetTwo txnIdRight) localDb visibleDb →
          Gright visibleDb (Database.flush localDb visibleDb))
    -- Invariant preservation under each guarantee
    (hPreserveLeft : ∀ db db', I db → Gleft db db' → I db')
    (hPreserveRight : ∀ db db', I db → Gright db db' → I db')
    -- Both halves tolerate R even under the other guarantee
    (hStableILeft : Logic.stableAssertion (fun db db' => R db db' ∨ Gright db db') I)
    (hStableIRight : Logic.stableAssertion (fun db db' => R db db' ∨ Gleft db db') I) :
    Logic.GlobalValid I R
      (.par
        (.txn txnIdLeft isoLeft exampleInsertBody)
        (.txn txnIdRight isoRight exampleInsertBodyTwo))
      (fun db db' => Gleft db db' ∨ Gright db db') I := by
  have hInferLeft :=
    paperInfer_exampleInsert
      (Logic.relyMod (fun db db' => R db db' ∨ Gright db db') isoLeft.exec)
      txnIdLeft I hStablePreLeft hFreshLeft
  have hInferRight :=
    paperInfer_exampleInsertTwo
      (Logic.relyMod (fun db db' => R db db' ∨ Gleft db db') isoRight.exec)
      txnIdRight I hStablePreRight hFreshRight
  exact PaperInfer.globalValid_txnPar
    hExecStableLeft hCommitIsoStableLeft hInferLeft hQstableLeft hGuaranteeLeft
    hExecStableRight hCommitIsoStableRight hInferRight hQstableRight hGuaranteeRight
    hPreserveLeft hPreserveRight hStableILeft hStableIRight

end Transformer

end DbAppProgramLogic
