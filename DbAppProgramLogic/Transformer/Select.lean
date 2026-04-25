import DbAppProgramLogic.Transformer.Paper
import DbAppProgramLogic.Legacy.Transformer.Concrete

namespace DbAppProgramLogic

namespace Transformer

theorem paperInferenceSound_select (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      ∀ localDb visibleDb selected,
        transformerPre I Fctxt localDb visibleDb →
        Semantics.collectSelected visibleDb source (instantiateSymExpr env [source] predicate) = some selected →
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (Command.subst binder (.lit (.set selected)) body)
          (transformerPost Fctxt F)) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body) F := by
  refine Logic.localValid_select R txnId _ _ binder source (instantiateSymExpr env [source] predicate) body
    hStable ?_
  intro localDb visibleDb selected hPre hSelect
  exact hBody localDb visibleDb selected hPre hSelect

theorem paperInferenceSound_select_of_materializedSet (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (selectedSet : SetLanguage.SetExpr)
    (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hMaterialized :
      ∀ visibleDb selected,
        Semantics.collectSelected visibleDb source (instantiateSymExpr env [source] predicate) =
          some selected →
        materializeSet visibleDb selectedSet = selected)
    (hBodyCmd :
      ∀ visibleDb selected,
        instantiateSetCommand (env.eraseSet binder) visibleDb
            (Command.subst binder (.lit (.set selected)) (instantiateScalarCommand env body)) =
          Command.subst binder (.lit (.set selected)) body)
    (hBody :
      paperInferenceSoundEnv R txnId I Fctxt (env.insertSet binder selectedSet) body F) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body) F := by
  refine paperInferenceSound_select R txnId I Fctxt env
    binder source predicate body F hStable ?_
  intro localDb visibleDb selected hPre hSelect
  have hMaterializedEq : materializeSet visibleDb selectedSet = selected := by
    exact hMaterialized visibleDb selected hSelect
  have hLocal :=
    paperInferenceSoundEnv_materializeSetBody R txnId I Fctxt
      env binder selectedSet body F hBody visibleDb selected hMaterializedEq
  simpa [hBodyCmd visibleDb selected] using hLocal

theorem paperInferenceSound_select_of_evalEq (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hSource : source ≠ "_row")
    (hEval :
      ∀ visibleDb row, row ∈ visibleDb →
        evalExprInSetEnv env ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem source row)
            (instantiateSymExpr env [source] predicate) =
          Expr.eval
            (Semantics.instantiateRecord source row.visible (instantiateSymExpr env [source] predicate)))
    (hBodyCmd :
      ∀ visibleDb selected,
        instantiateSetCommand (env.eraseSet binder) visibleDb
            (Command.subst binder (.lit (.set selected))
              (instantiateScalarCommand env body)) =
          Command.subst binder (.lit (.set selected)) body)
    (hBody :
      paperInferenceSoundEnv R txnId I Fctxt
        (env.insertSet binder
          (globalSelectionSet env source (instantiateSymExpr env [source] predicate))) body F) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body) F := by
  refine paperInferenceSound_select_of_materializedSet R txnId I Fctxt env
    binder source predicate
    (globalSelectionSet env source (instantiateSymExpr env [source] predicate))
    body F hStable ?_ hBodyCmd hBody
  intro visibleDb selected hSelect
  exact materializeSet_globalSelectionSet_eq_collectSelected_of_eval env source
    (instantiateSymExpr env [source] predicate) visibleDb selected
    hSource (hEval visibleDb) hSelect

theorem paperInferenceSound_select_emptyEnv (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hSource : source ≠ "_row")
    (hBody :
      paperInferenceSoundEnv R txnId I Fctxt
        (({ scalarVars := [], setVars := [] } : SymEnv).insertSet binder
          (globalSelectionSet { scalarVars := [], setVars := [] } source predicate))
        body F) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source predicate body) F := by
  refine paperInferenceSound_select_of_evalEq R txnId I Fctxt
    { scalarVars := [], setVars := [] } binder source predicate body F hStable hSource ?_ ?_ hBody
  · intro visibleDb row hMem
    exact evalExprInSetEnv_closed_bindElem_eq_instantiateRecord [] source visibleDb row predicate
  · intro visibleDb selected
    simp [instantiateScalarCommand, instantiateSetCommand, SymEnv.eraseSet]


theorem infer_select_sound (txnId : TxnId) (env : Env) (binder source : VarName)
    (predicate : Expr) (body : Semantics.Program) (db delta : Database)
    (h : inferEffect txnId env (.select binder source predicate body) db = some delta) :
    ∃ selected,
      Semantics.collectSelected db source (instantiateExpr env [source] predicate) = some selected ∧
      inferEffect txnId (env.insert binder (.set selected)) body db = some delta := by
  cases hSelect : Semantics.collectSelected db source (instantiateExpr env [source] predicate) with
  | none =>
      have : False := by
        simp [inferEffect, hSelect] at h
      exact False.elim this
  | some selected =>
      refine ⟨selected, rfl, ?_⟩
      simpa [inferEffect, hSelect] using h

theorem inferenceSoundEnv_select (txnId : TxnId) (env : Env) (binder source : VarName)
    (predicate : Expr) (body : Semantics.Program)
    (hBody :
      ∀ selected,
        inferenceSoundEnv txnId (env.insert binder (.set selected)) body
          (inferEffect txnId (env.insert binder (.set selected)) body)) :
    inferenceSoundEnv txnId env (.select binder source predicate body)
      (inferEffect txnId env (.select binder source predicate body)) := by
  intro visibleDb localDb' hInfer
  rcases infer_select_sound txnId env binder source predicate body visibleDb localDb' hInfer with
    ⟨selected, hSelect, hBodyInfer⟩
  have hBodyValid' := hBody selected visibleDb localDb' hBodyInfer
  have hBodyValid :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ visible = visibleDb)
        (Command.subst binder (.lit (.set selected))
          (instantiateCommand (ι := IsolationSpec Database) (env.erase binder) body) :
            Command (IsolationSpec Database) Database)
        (fun localDb visible => localDb = localDb' ∧ visible = visibleDb) := by
    have hInst :
        instantiateCommand (ι := IsolationSpec Database) (env.insert binder (.set selected)) body =
          Command.subst binder (.lit (.set selected))
            (instantiateCommand (ι := IsolationSpec Database) (env.erase binder) body) := by
      simpa [Env.insert, Env.erase_idem] using
        (instantiateCommand_insert (env.erase binder) binder (.set selected) body)
    simpa [hInst] using hBodyValid'
  refine Logic.localValid_select_false
    (ι := IsolationSpec Database)
    (txnId := txnId)
    (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
    (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
    (binder := binder)
    (source := source)
    (predicate := instantiateExpr env [source] predicate)
    (body := instantiateCommand (ι := IsolationSpec Database) (env.erase binder) body)
    ?_
  intro localDb visibleDb' selected' hPre hSelect'
  rcases hPre with ⟨rfl, rfl⟩
  have hEq : selected' = selected := by
    rw [hSelect] at hSelect'
    injection hSelect' with hEq
    exact hEq.symm
  subst hEq
  exact hBodyValid

theorem inferenceSound_select (txnId : TxnId) (binder source : VarName)
    (predicate : Expr) (body : Semantics.Program)
    (hBody :
      ∀ selected,
        inferenceSoundEnv txnId [(binder, .set selected)] body
          (inferEffect txnId [(binder, .set selected)] body)) :
    inferenceSound txnId (.select binder source predicate body)
      (inferEffect txnId [] (.select binder source predicate body)) := by
  refine inferenceSound_of_env_empty txnId (.select binder source predicate body)
    (inferEffect txnId [] (.select binder source predicate body)) ?_
  refine inferenceSoundEnv_select txnId [] binder source predicate body ?_
  intro selected
  simpa [Env.insert, Env.erase] using hBody selected


theorem localStep_select_of_infer (txnId : TxnId) (env : Env) (binder source : VarName)
    (predicate : Expr) (body : Semantics.Program) (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.select binder source predicate body : Semantics.Program)) visibleDb = some delta) :
    ∃ selected,
      Semantics.collectSelected visibleDb source (instantiateExpr env [source] predicate) = some selected ∧
      inferEffect txnId (env.insert binder (.set selected)) body visibleDb = some delta ∧
      Semantics.LocalStep
        visibleDb
        txnId
        (instantiateCommand (ι := IsolationSpec Database) env (.select binder source predicate body : Semantics.Program))
        localDb
        (Command.subst binder (.lit (.set selected))
          (instantiateCommand (ι := IsolationSpec Database) (env.erase binder) body) :
            Command (IsolationSpec Database) Database)
        localDb := by
  rcases infer_select_sound txnId env binder source predicate body visibleDb delta hInfer with
    ⟨selected, hSelect, hBody⟩
  refine ⟨selected, hSelect, hBody, ?_⟩
  simpa [instantiateCommand] using
    (Semantics.LocalStep.select
      (snapshot := visibleDb)
      (txnId := txnId)
      (binder := binder)
      (source := source)
      (predicate := instantiateExpr env [source] predicate)
      (body := instantiateCommand (env.erase binder) body)
      (selected := selected)
      (localDb := localDb)
      hSelect)


end Transformer

end DbAppProgramLogic
