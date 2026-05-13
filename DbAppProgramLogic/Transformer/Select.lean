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

/-- Soundness of the lazy SELECT rule following Fig. 8 ST-SELECT (`λ(∆). [F'(∆)/y] F(∆)`).

The body's effect `Fbody : SetLit → SetExpr` is parameterized over the captured `selected`
binding, so the substituted body and the body's effect share `selected`. The output `F`
existentially quantifies `selected` against the runtime visible database, which avoids the
universal-quantification mismatch caused by baking `selected` into the body via `Command.subst`
while the surrounding `F` recomputes the aggregate from globalDb.

The proof reduces to `Logic.localValid_select` once the caller supplies a body LocalValid
whose post directly establishes the lazy F's existential post-shape. This is the natural
shape that arises by combining the body's `transformerPost Fctxt (Fbody selected)` LocalValid
with rely-stability information (e.g. SI's silent rely keeps `vd' = visibleDb`, allowing the
`(selected, visibleDb)` witness to satisfy the lazy F's existential conditions). -/
theorem paperInferenceSound_selectLazy (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program)
    (Fbody : SetLit → SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      ∀ localDb visibleDb selected,
        transformerPre I Fctxt localDb visibleDb →
        Semantics.collectSelected visibleDb source (instantiateSymExpr env [source] predicate) = some selected →
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (Command.subst binder (.lit (.set selected)) body)
          (transformerPost Fctxt
            (fun localDb' globalDb' out =>
              ∃ selected',
                Semantics.collectSelected globalDb' source
                    (instantiateSymExpr env [source] predicate) = some selected' ∧
                Fbody selected' localDb' globalDb' out))) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body)
      (fun localDb globalDb out =>
        ∃ selected,
          Semantics.collectSelected globalDb source
              (instantiateSymExpr env [source] predicate) = some selected ∧
          Fbody selected localDb globalDb out) := by
  refine Logic.localValid_select R txnId _ _ binder source
    (instantiateSymExpr env [source] predicate) body hStable ?_
  intro localDb visibleDb selected hPre hSelect
  exact hBody localDb visibleDb selected hPre hSelect

/-! ## Wrap-aware SELECT soundness -/

/-- Wrapped SELECT rule. `Logic.localValid_select` takes a generic post `Q`, so the
wrapped post `transformerPostWrapped R I Fctxt F` flows through unchanged. The body
hypothesis is the wrapped form of the universal-`selected` body LocalValid. -/
theorem paperInferenceSound_select_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program)
    (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      ∀ localDb visibleDb selected,
        transformerPre I Fctxt localDb visibleDb →
        Semantics.collectSelected visibleDb source
            (instantiateSymExpr env [source] predicate) = some selected →
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (Command.subst binder (.lit (.set selected)) body)
          (transformerPostWrapped R I Fctxt F)) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body) F := by
  refine Logic.localValid_select R txnId _ _ binder source
    (instantiateSymExpr env [source] predicate) body hStable ?_
  intro localDb visibleDb selected hPre hSelect
  exact hBody localDb visibleDb selected hPre hSelect

/-- Wrapped SELECT-lazy rule (paper Fig.8 `[F'(Δ)/y] F(Δ)`). The body is provided
as a per-`selected` family of iff-form LocalValids (its iff post is `Fbody selected`).
The proof routes through `Logic.localValid_select_collectInvariant`, which pins
`vd_init = visibleDbMid` (the moment `collectSelected` was observed). Together with
`hCollectStable` propagating through the rely multistep, this lets us bridge the
body's iff `Fbody selected` to `LazyF` at `finalCfg.visibleDb`, then lift to the
wrapped outer post with `vd' := finalCfg.visibleDb` witness. -/
theorem paperInferenceSound_selectLazy_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program)
    (Fbody : SetLit → SetLanguage.SetExpr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hCollectStable :
      ∀ localDb visibleDb visibleDb',
        R localDb visibleDb visibleDb' →
        Semantics.collectSelected visibleDb' source
            (instantiateSymExpr env [source] predicate) =
          Semantics.collectSelected visibleDb source
            (instantiateSymExpr env [source] predicate))
    (hBody :
      ∀ selected,
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (Command.subst binder (.lit (.set selected)) body)
          (transformerPost Fctxt (Fbody selected))) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body)
      (fun localDb globalDb out =>
        ∃ selected,
          Semantics.collectSelected globalDb source
              (instantiateSymExpr env [source] predicate) = some selected ∧
          Fbody selected localDb globalDb out) := by
  refine Logic.localValid_select_collectInvariant R txnId _ _ binder source
    (instantiateSymExpr env [source] predicate) body hStable ?_
  intro selected
  intro ld_init vd_init finalCfg hPreStrong hMulti hSkip
  rcases hPreStrong with ⟨hPreBody, hSelectInit⟩
  -- Body's iff post (Fbody selected) at finalCfg.
  have hPost :=
    hBody selected ld_init vd_init finalCfg hPreBody hMulti hSkip
  -- Propagate `collectSelected` from `vd_init` to `finalCfg.visibleDb`.
  have hCollect_preserved :
      ∀ {cfg cfg' : LocalConfig (IsolationSpec Database)},
        Logic.LocalMultiStep R txnId (IsolationSpec Database) cfg cfg' →
        Semantics.collectSelected cfg.visibleDb source
            (instantiateSymExpr env [source] predicate) =
          Semantics.collectSelected cfg'.visibleDb source
            (instantiateSymExpr env [source] predicate) := by
    intro cfg cfg' hM
    induction hM with
    | refl => rfl
    | tail _hPrev hLast ih =>
        rcases hLast with hLocal | hRely
        · rcases hLocal with ⟨_hStep, hVisEq⟩
          exact ih.trans (by rw [hVisEq])
        · rcases hRely with ⟨_hCmd, _hLocal, _hNotSkip, hR⟩
          exact ih.trans (hCollectStable _ _ _ hR).symm
  have hSelectFinal :
      Semantics.collectSelected finalCfg.visibleDb source
          (instantiateSymExpr env [source] predicate) = some selected := by
    have hEq := hCollect_preserved
      (cfg := ⟨Command.subst binder (.lit (.set selected)) body, ld_init, vd_init⟩)
      (cfg' := finalCfg) hMulti
    exact hEq ▸ hSelectInit
  -- I is preserved through multistep, giving I at finalCfg.visibleDb.
  have hI_final : I finalCfg.visibleDb :=
    localMultiStep_preserves_invariant
      (cfg := ⟨Command.subst binder (.lit (.set selected)) body, ld_init, vd_init⟩)
      (cfg' := finalCfg) hStableI hMulti hPreBody.2
  -- Bridge iff `Fbody selected` ↔ iff `LazyF` at finalCfg.visibleDb.
  have hPostLazy :
      transformerPost Fctxt
        (fun localDb globalDb out =>
          ∃ selected',
            Semantics.collectSelected globalDb source
                (instantiateSymExpr env [source] predicate) = some selected' ∧
            Fbody selected' localDb globalDb out)
        finalCfg.localDb finalCfg.visibleDb := by
    intro row
    have hPostRow := hPost row
    simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote,
      SetLanguage.Env.ofDatabases] at hPostRow ⊢
    constructor
    · rintro (hFctxt | hLazy)
      · exact hPostRow.mp (Or.inl hFctxt)
      · obtain ⟨selected', hSel', hFbody'⟩ := hLazy
        have hEq : selected' = selected := by
          rw [hSelectFinal] at hSel'
          exact (Option.some.inj hSel').symm
        subst hEq
        exact hPostRow.mp (Or.inr hFbody')
    · intro hRow
      rcases hPostRow.mpr hRow with hFctxt | hFbody
      · exact Or.inl hFctxt
      · exact Or.inr ⟨selected, hSelectFinal, hFbody⟩
  -- Lift iff `LazyF` at finalCfg.visibleDb to wrapped form, witness `vd' := finalCfg.visibleDb`.
  exact transformerPostWrapped_of_transformerPost hI_final hPostLazy

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
    (hEval :
      ∀ (visibleDb : Database) row, row ∈ visibleDb →
        evalSymExprAtRow env source row (instantiateSymExpr env [source] predicate) =
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
    (hEval visibleDb) hSelect

theorem paperInferenceSound_select_emptyEnv (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (binder source : VarName) (predicate : Expr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      paperInferenceSoundEnv R txnId I Fctxt
        (({ scalarVars := [], setVars := [] } : SymEnv).insertSet binder
          (globalSelectionSet { scalarVars := [], setVars := [] } source predicate))
        body F) :
    paperInferenceSound R txnId I Fctxt
      (.select binder source predicate body) F := by
  refine paperInferenceSound_select_of_evalEq R txnId I Fctxt
    { scalarVars := [], setVars := [] } binder source predicate body F hStable ?_ ?_ hBody
  · intro visibleDb row _hMem
    simp [evalSymExprAtRow, instantiateSymExpr_noScalars]
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
