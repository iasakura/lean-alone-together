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

/-! ## Wrap-aware per-rule soundness

Each rule below restates the soundness of a single inference rule using
`paperInferenceSoundWrapped`. The trivial lifts (skip / insert / delete / update / let /
viaLocalValid) reduce to `lift_iff_to_wrapped` of the iff-form lemma. The composite
rules (ite, seq) accept wrapped IHs and bridge them internally via stability premises.
-/

theorem paperInferenceSound_skip_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hPostStable : Logic.stableBiAssertion R (transformerPost Fctxt SetLanguage.empty)) :
    paperInferenceSoundWrapped R txnId I Fctxt .skip SetLanguage.empty :=
  lift_iff_to_wrapped hStableI (paperInferenceSound_skip R txnId I Fctxt hPostStable)

theorem paperInferenceSound_insert_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv) (expr : Expr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
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
    paperInferenceSoundWrapped R txnId I Fctxt
      (.insert (instantiateSymExpr env [] expr))
      (insertedRowSet txnId env expr) :=
  lift_iff_to_wrapped hStableI
    (paperInferenceSound_insert R txnId I Fctxt env expr hStable hClosed hFresh)

theorem paperInferenceSound_delete_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : Env)
    (source : VarName) (predicate : Expr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.delete source (instantiateExpr env [source] predicate))
      (deleteSetExpr txnId env source predicate) :=
  lift_iff_to_wrapped hStableI
    (paperInferenceSound_delete R txnId I Fctxt env source predicate hStable)

theorem paperInferenceSound_update_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : Env)
    (source : VarName) (updateExpr predicate : Expr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.update source (instantiateExpr env [source] updateExpr)
        (instantiateExpr env [source] predicate))
      (updateSetExpr txnId env source updateExpr predicate) :=
  lift_iff_to_wrapped hStableI
    (paperInferenceSound_update R txnId I Fctxt env source updateExpr predicate hStable)

theorem paperInferenceSound_let_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (x : VarName) (expr : Expr) (body : Semantics.Program) (value : Value) (F : SetLanguage.SetExpr)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hEval : Expr.eval (instantiateSymExpr env [] expr) = some value)
    (hBody :
      Logic.LocalValid R txnId (transformerPre I Fctxt)
        (Command.subst x value.toExpr body) (transformerPost Fctxt F)) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.letE x (instantiateSymExpr env [] expr) body) F :=
  lift_iff_to_wrapped hStableI
    (paperInferenceSound_let R txnId I Fctxt env x expr body value F hStable hEval hBody)

/-- Wrapped IF rule. Each branch's wrapped LocalValid produces the wrapped post for the
overall `ite` after weakening the inner `FThen`/`FElse` post to the `.ite cond FThen FElse`
post via the (vd-independent) `formulaOfExpr` evaluation. -/
theorem paperInferenceSound_ite_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program) (FThen FElse : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hThen : paperInferenceSoundWrapped R txnId I Fctxt thenBranch FThen)
    (hElse : paperInferenceSoundWrapped R txnId I Fctxt elseBranch FElse) :
    paperInferenceSoundWrapped R txnId I Fctxt
      (.ite (instantiateSymExpr env [] cond) thenBranch elseBranch)
      (.ite (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
        FThen FElse) := by
  refine Logic.localValid_ite R txnId _ _
    (instantiateSymExpr env [] cond) thenBranch elseBranch hStable ?_ ?_
  · intro hEvalTrue
    refine Logic.localValid_conseq (fun _ _ hPre => hPre) hThen ?_
    intro ld vd hWrap
    rcases hWrap with ⟨vd', hPin, hI', hPost⟩
    refine ⟨vd', ?_, hI', ?_⟩
    · intro hStableIte
      apply hPin
      intro ld' vdA vdB hThenPost hR
      have hCondClosed :
          formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld' vdA :=
        formulaOfExpr_closed_true_of_eval env vdA (instantiateSymExpr env [] cond) hEvalTrue
      have hIteAt :
          transformerPost Fctxt
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) ld' vdA := by
        intro row
        have hIte_denote :
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdA)
              (.ite (formulaOfExpr { env with scalarVars := [] }
                (instantiateSymExpr env [] cond)) FThen FElse) row ↔
              SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdA) FThen row := by
          exact Iff.of_eq <| congrArg (fun f => f row)
            (SetLanguage.denote_ite_true (SetLanguage.Env.ofDatabases [] vdA)
              (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
              FThen FElse hCondClosed)
        simpa [transformerPost, SetLanguage.denote_union, hIte_denote] using hThenPost row
      have hStableAtB := hStableIte _ _ _ hIteAt hR
      intro row
      have hCondClosedB :
          formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld' vdB :=
        formulaOfExpr_closed_true_of_eval env vdB (instantiateSymExpr env [] cond) hEvalTrue
      have hIteB :
          SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdB)
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) row ↔
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdB) FThen row := by
        exact Iff.of_eq <| congrArg (fun f => f row)
          (SetLanguage.denote_ite_true (SetLanguage.Env.ofDatabases [] vdB)
            (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
            FThen FElse hCondClosedB)
      simpa [transformerPost, SetLanguage.denote_union, hIteB] using hStableAtB row
    · intro row
      have hCondClosed :
          formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld vd' :=
        formulaOfExpr_closed_true_of_eval env vd' (instantiateSymExpr env [] cond) hEvalTrue
      have hIte :
          SetLanguage.denote (SetLanguage.Env.ofDatabases [] vd')
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) row ↔
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vd') FThen row := by
        exact Iff.of_eq <| congrArg (fun f => f row)
          (SetLanguage.denote_ite_true (SetLanguage.Env.ofDatabases [] vd')
            (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
            FThen FElse hCondClosed)
      simpa [transformerPost, SetLanguage.denote_union, hIte] using hPost row
  · intro hEvalFalse
    refine Logic.localValid_conseq (fun _ _ hPre => hPre) hElse ?_
    intro ld vd hWrap
    rcases hWrap with ⟨vd', hPin, hI', hPost⟩
    refine ⟨vd', ?_, hI', ?_⟩
    · intro hStableIte
      apply hPin
      intro ld' vdA vdB hElsePost hR
      have hCondClosed :
          ¬ formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld' vdA :=
        formulaOfExpr_closed_false_of_eval env vdA (instantiateSymExpr env [] cond) hEvalFalse
      have hIteAt :
          transformerPost Fctxt
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) ld' vdA := by
        intro row
        have hIte_denote :
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdA)
              (.ite (formulaOfExpr { env with scalarVars := [] }
                (instantiateSymExpr env [] cond)) FThen FElse) row ↔
              SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdA) FElse row := by
          exact Iff.of_eq <| congrArg (fun f => f row)
            (SetLanguage.denote_ite_false (SetLanguage.Env.ofDatabases [] vdA)
              (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
              FThen FElse hCondClosed)
        simpa [transformerPost, SetLanguage.denote_union, hIte_denote] using hElsePost row
      have hStableAtB := hStableIte _ _ _ hIteAt hR
      intro row
      have hCondClosedB :
          ¬ formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld' vdB :=
        formulaOfExpr_closed_false_of_eval env vdB (instantiateSymExpr env [] cond) hEvalFalse
      have hIteB :
          SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdB)
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) row ↔
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vdB) FElse row := by
        exact Iff.of_eq <| congrArg (fun f => f row)
          (SetLanguage.denote_ite_false (SetLanguage.Env.ofDatabases [] vdB)
            (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
            FThen FElse hCondClosedB)
      simpa [transformerPost, SetLanguage.denote_union, hIteB] using hStableAtB row
    · intro row
      have hCondClosed :
          ¬ formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond)
            ld vd' :=
        formulaOfExpr_closed_false_of_eval env vd' (instantiateSymExpr env [] cond) hEvalFalse
      have hIte :
          SetLanguage.denote (SetLanguage.Env.ofDatabases [] vd')
            (.ite (formulaOfExpr { env with scalarVars := [] }
              (instantiateSymExpr env [] cond)) FThen FElse) row ↔
            SetLanguage.denote (SetLanguage.Env.ofDatabases [] vd') FElse row := by
        exact Iff.of_eq <| congrArg (fun f => f row)
          (SetLanguage.denote_ite_false (SetLanguage.Env.ofDatabases [] vd')
            (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
            FThen FElse hCondClosed)
      simpa [transformerPost, SetLanguage.denote_union, hIte] using hPost row

/-- Wrapped SEQ rule. `hLeft` (wrapped F₁) is converted to iff form via the `hStableMid`
pin, then `Logic.localValid_seq` is invoked with the iff mid post. The output's
`Fctxt ∪ (F₁ ∪ F₂)` is obtained from `(Fctxt ∪ F₁) ∪ F₂` via union associativity on
both the iff post and the stability of the wrap. -/
theorem paperInferenceSound_seq_wrapped (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt F₁ F₂ : SetLanguage.SetExpr)
    (left right : Semantics.Program)
    (hStableI : Logic.stableBiAssertion R (fun _ vd => I vd))
    (hLeft : paperInferenceSoundWrapped R txnId I Fctxt left F₁)
    (hStableMid : Logic.stableBiAssertion R (transformerPost Fctxt F₁))
    (hRight : Logic.LocalValid R txnId (transformerPre I (.union Fctxt F₁)) right
                (transformerPostWrapped R I (.union Fctxt F₁) F₂)) :
    paperInferenceSoundWrapped R txnId I Fctxt (.seq left right) (.union F₁ F₂) := by
  -- Convert hLeft from wrapped to `transformerPre I (Fctxt ∪ F₁)` (iff + I) via pin.
  have hLeft_iff_pre :
      Logic.LocalValid R txnId (transformerPre I Fctxt) left
        (transformerPre I (.union Fctxt F₁)) := by
    refine Logic.localValid_conseq (fun _ _ h => h) hLeft ?_
    intro ld vd hWrap
    rcases hWrap with ⟨vd', hPin, hI', hPost⟩
    have hVd : vd' = vd := hPin hStableMid
    refine ⟨?_, hVd ▸ hI'⟩
    intro row
    have := hPost row
    have hRew : vd' = vd := hVd
    rw [hRew] at this
    exact this
  -- Stability of `transformerPre I (Fctxt ∪ F₁)` from `hStableMid` + `hStableI`.
  have hStableMidPre :
      Logic.stableBiAssertion R (transformerPre I (.union Fctxt F₁)) := by
    intro ld vd vd' hPre hR
    refine ⟨?_, hStableI _ _ _ hPre.2 hR⟩
    have hPostVd : transformerPost Fctxt F₁ ld vd := hPre.1
    have hPostVd' : transformerPost Fctxt F₁ ld vd' := hStableMid _ _ _ hPostVd hR
    exact hPostVd'
  -- Compose via Logic.localValid_seq with iff mid.
  have hSeq :
      Logic.LocalValid R txnId (transformerPre I Fctxt) (.seq left right)
        (transformerPostWrapped R I (.union Fctxt F₁) F₂) :=
    Logic.localValid_seq R txnId _ _ _ left right hLeft_iff_pre hStableMidPre hRight
  -- Post massage: wrapped (Fctxt ∪ F₁) F₂ → wrapped Fctxt (F₁ ∪ F₂) via union associativity.
  refine Logic.localValid_conseq (fun _ _ h => h) hSeq ?_
  intro ld vd hWrap
  rcases hWrap with ⟨vd', hPin, hI', hPost⟩
  refine ⟨vd', ?_, hI', ?_⟩
  · intro hStableAssoc
    apply hPin
    intro ld' vdA vdB hPostL hR
    have hPostAssoc : transformerPost Fctxt (.union F₁ F₂) ld' vdA := by
      intro row
      have := hPostL row
      simpa [transformerPost, SetLanguage.denote_union, or_assoc] using this
    have hStableAtB := hStableAssoc _ _ _ hPostAssoc hR
    intro row
    have := hStableAtB row
    simpa [transformerPost, SetLanguage.denote_union, or_assoc] using this
  · intro row
    have := hPost row
    simpa [transformerPost, SetLanguage.denote_union, or_assoc] using this

end Transformer

end DbAppProgramLogic
