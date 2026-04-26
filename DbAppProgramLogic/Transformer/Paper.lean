import DbAppProgramLogic.Transformer.Basic

namespace DbAppProgramLogic

namespace Transformer

theorem paperInferenceSound_skip (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (hPostStable : Logic.stableBiAssertion R (transformerPost Fctxt SetLanguage.empty)) :
    paperInferenceSound R txnId I Fctxt .skip SetLanguage.empty := by
  let _ := hPostStable
  refine Logic.localValid_conseq
    (fun localDb visibleDb hPre row => ?_)
    (Logic.localValid_skip R txnId (transformerPost Fctxt SetLanguage.empty))
    (fun _ _ hPost => hPost)
  · simpa [transformerPost, SetLanguage.denote_union] using hPre.1 row

theorem paperInferenceSound_insert (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv) (expr : Expr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hClosed :
      ∀ visibleDb row,
        evalExprInSetEnv env ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem "_row" row) expr =
          Expr.eval (instantiateSymExpr env [] expr))
    (hFresh :
      ∀ localDb visibleDb record,
        transformerPre I Fctxt localDb visibleDb →
        Expr.eval (instantiateSymExpr env [] expr) = some (.record record) →
        Semantics.insertFresh visibleDb localDb record) :
    paperInferenceSound R txnId I Fctxt
      (.insert (instantiateSymExpr env [] expr))
      (insertedRowSet txnId env expr) := by
  refine Logic.localValid_insert R txnId _ _ _ hStable ?_
  intro localDb visibleDb record hPre hEval hFresh'
  intro row
  have hCtx := hPre.1 row
  have hInserted :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
        (insertedRowSet txnId env expr) row ↔
        row = Row.fromInsert txnId record := by
    exact denote_insertedRowSet txnId env expr visibleDb row record (hClosed visibleDb row) hEval
  have _ : Semantics.insertFresh visibleDb localDb record := hFresh localDb visibleDb record hPre hEval
  simp [transformerPost, SetLanguage.denote_union, hCtx, hInserted]

theorem paperInferenceSound_let (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (x : VarName) (expr : Expr) (body : Semantics.Program) (value : Value) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hEval : Expr.eval (instantiateSymExpr env [] expr) = some value)
    (hBody :
      Logic.LocalValid R txnId (transformerPre I Fctxt)
        (Command.subst x value.toExpr body) (transformerPost Fctxt F)) :
    paperInferenceSound R txnId I Fctxt
      (.letE x (instantiateSymExpr env [] expr) body) F := by
  exact Logic.localValid_let R txnId _ _ x (instantiateSymExpr env [] expr) body value
    hStable hEval hBody

theorem paperInferenceSound_delete (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : Env)
    (source : VarName) (predicate : Expr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
    paperInferenceSound R txnId I Fctxt
      (.delete source (instantiateExpr env [source] predicate))
      (deleteSetExpr txnId env source predicate) := by
  refine Logic.localValid_delete R txnId _ _ _ _ hStable ?_
  intro localDb visibleDb removed hPre hDelete hDisjoint
  intro row
  have hCtx := hPre.1 row
  have hDeleted :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
        (deleteSetExpr txnId env source predicate) row ↔
        row ∈ removed := by
    exact deleteSetExpr_sound txnId env source predicate visibleDb removed row hDelete
  simp [transformerPost, SetLanguage.denote_union, hCtx, hDeleted]

theorem paperInferenceSound_update (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : Env)
    (source : VarName) (updateExpr predicate : Expr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
    paperInferenceSound R txnId I Fctxt
      (.update source (instantiateExpr env [source] updateExpr) (instantiateExpr env [source] predicate))
      (updateSetExpr txnId env source updateExpr predicate) := by
  refine Logic.localValid_update R txnId _ _ _ _ _ hStable ?_
  intro localDb visibleDb updated hPre hUpdate hDisjoint
  intro row
  have hCtx := hPre.1 row
  have hUpdated :
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
        (updateSetExpr txnId env source updateExpr predicate) row ↔
        row ∈ updated := by
    exact updateSetExpr_sound txnId env source updateExpr predicate visibleDb updated row hUpdate
  simp [transformerPost, SetLanguage.denote_union, hCtx, hUpdated]

theorem paperInferenceSound_seq (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt F₁ F₂ : SetLanguage.SetExpr)
    (left right : Semantics.Program)
    (hLeft : paperInferenceSound R txnId I Fctxt left F₁)
    (hStableMid : Logic.stableBiAssertion R (transformerPost Fctxt F₁))
    (hRight :
      Logic.LocalValid R txnId (transformerPost Fctxt F₁) right
        (transformerPost (.union Fctxt F₁) F₂)) :
    Logic.LocalValid R txnId (transformerPre I Fctxt) (.seq left right)
      (transformerPost (.union Fctxt F₁) F₂) := by
  exact Logic.localValid_seq R txnId _ _ _ left right hLeft hStableMid hRight

theorem paperInferenceSound_ite (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program) (FThen FElse : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hThen : paperInferenceSound R txnId I Fctxt thenBranch FThen)
    (hElse : paperInferenceSound R txnId I Fctxt elseBranch FElse) :
    paperInferenceSound R txnId I Fctxt
      (.ite (instantiateSymExpr env [] cond) thenBranch elseBranch)
      (.ite (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)) FThen FElse) := by
  refine Logic.localValid_ite R txnId _ _
    (instantiateSymExpr env [] cond) thenBranch elseBranch hStable ?_ ?_
  · intro hEvalTrue
    refine Logic.localValid_conseq
      (fun _ _ hPre => hPre)
      hThen
      (fun localDb visibleDb hPost row => ?_)
    have hCond :
        formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
          (SetLanguage.Env.ofDatabases [] visibleDb).localDb
          (SetLanguage.Env.ofDatabases [] visibleDb).globalDb := by
      exact formulaOfExpr_closed_true_of_eval env visibleDb (instantiateSymExpr env [] cond) hEvalTrue
    have hIte :
        SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
          (.ite (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)) FThen FElse) row ↔
        SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) FThen row := by
      exact Iff.of_eq <| congrArg (fun f => f row)
        (SetLanguage.denote_ite_true
          (SetLanguage.Env.ofDatabases [] visibleDb)
          (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
          FThen FElse hCond)
    simpa [transformerPost, SetLanguage.denote_union, hIte] using hPost row
  · intro hEvalFalse
    refine Logic.localValid_conseq
      (fun _ _ hPre => hPre)
      hElse
      (fun localDb visibleDb hPost row => ?_)
    have hCond :
        ¬ formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            (SetLanguage.Env.ofDatabases [] visibleDb).localDb
            (SetLanguage.Env.ofDatabases [] visibleDb).globalDb := by
      exact formulaOfExpr_closed_false_of_eval env visibleDb (instantiateSymExpr env [] cond) hEvalFalse
    have hIte :
        SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
          (.ite (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)) FThen FElse) row ↔
        SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) FElse row := by
      exact Iff.of_eq <| congrArg (fun f => f row)
        (SetLanguage.denote_ite_false
          (SetLanguage.Env.ofDatabases [] visibleDb)
          (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
          FThen FElse hCond)
    simpa [transformerPost, SetLanguage.denote_union, hIte] using hPost row


end Transformer

end DbAppProgramLogic
