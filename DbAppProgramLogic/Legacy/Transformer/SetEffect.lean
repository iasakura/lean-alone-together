import DbAppProgramLogic.Transformer.Select
import DbAppProgramLogic.Transformer.Foreach

namespace DbAppProgramLogic

namespace Transformer

def inferWriteSetExpr (txnId : TxnId) (env : Env) : Semantics.Program → Option SetLanguage.SetExpr
  | .skip => some SetLanguage.empty
  | .letE x expr body => do
      let value ← evalInEnv env expr
      inferWriteSetExpr txnId (env.insert x value) body
  | .ite cond thenBranch elseBranch => do
      let .scalar (.bool b) ← evalInEnv env cond | none
      if b then inferWriteSetExpr txnId env thenBranch else inferWriteSetExpr txnId env elseBranch
  | .seq left right => do
      let sLeft ← inferWriteSetExpr txnId env left
      let sRight ← inferWriteSetExpr txnId env right
      pure (.union sLeft sRight)
  | .insert expr => insertSetExpr txnId env expr
  | .delete source predicate => some (deleteSetExpr txnId env source predicate)
  | .update source updateExpr predicate => some (updateSetExpr txnId env source updateExpr predicate)
  | _ => none

theorem inferWriteSetExpr_sound (txnId : TxnId) (env : Env)
    (body : Semantics.Program) (s : SetLanguage.SetExpr)
    (db rows : Database) (row : Row)
    (hSet : inferWriteSetExpr txnId env body = some s)
    (hEffect : inferEffect txnId env body db = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows := by
  induction body generalizing env s db rows row with
  | skip =>
      simp [inferWriteSetExpr, inferEffect, emptyEffect] at hSet hEffect
      subst s
      subst rows
      simp [SetLanguage.empty, SetLanguage.denote]
  | letE x expr body ih =>
      rcases infer_let_sound txnId env x expr body db rows hEffect with
        ⟨value, hEval, hBodyEff⟩
      simp [inferWriteSetExpr, hEval] at hSet
      exact ih (env.insert x value) s db rows row hSet hBodyEff
  | ite cond thenBranch elseBranch ihThen ihElse =>
      rcases infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
        ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
      · simp [inferWriteSetExpr, hCond] at hSet
        exact ihThen env s db rows row hSet hThenEff
      · simp [inferWriteSetExpr, hCond] at hSet
        exact ihElse env s db rows row hSet hElseEff
  | seq left right ihLeft ihRight =>
      cases hLeftSet : inferWriteSetExpr txnId env left with
      | none =>
          simp [inferWriteSetExpr, hLeftSet] at hSet
      | some sLeft =>
          cases hRightSet : inferWriteSetExpr txnId env right with
          | none =>
              simp [inferWriteSetExpr, hLeftSet, hRightSet] at hSet
          | some sRight =>
              simp [inferWriteSetExpr, hLeftSet, hRightSet] at hSet
              subst s
              rcases infer_seq_sound txnId env left right db rows hEffect with
                ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
              have hDenLeft := ihLeft env sLeft db rowsLeft row hLeftSet hLeftEff
              have hDenRight := ihRight env sRight db rowsRight row hRightSet hRightEff
              simp [SetLanguage.denote_union, hDenLeft, hDenRight, hRows]
  | insert expr =>
      rcases insertSetExpr_sound txnId env expr s hSet with ⟨record, rfl, hEval⟩
      rcases infer_insert_sound txnId env expr db rows hEffect with ⟨record', hEval', hRows⟩
      have hEvalExpr : Expr.eval (instantiateExpr env [] expr) = some (.record record) := by
        simpa [evalInEnv] using hEval
      rw [hEvalExpr] at hEval'
      injection hEval' with hRecord
      cases hRecord
      simp [SetLanguage.denote_singleton, hRows]
  | delete source predicate =>
      simp [inferWriteSetExpr] at hSet
      subst s
      exact deleteSetExpr_sound txnId env source predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | select binder source predicate body ih =>
      simp [inferWriteSetExpr] at hSet
  | update source updateExpr predicate =>
      simp [inferWriteSetExpr] at hSet
      subst s
      exact updateSetExpr_sound txnId env source updateExpr predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | foreach source doneVar elemVar body ih =>
      simp [inferWriteSetExpr] at hSet
  | foreachRuntime done remaining doneVar elemVar body ih =>
      simp [inferWriteSetExpr] at hSet
  | txn txnId' isolation body ih =>
      simp [inferWriteSetExpr] at hSet
  | txnRuntime txnId' isolation localDb snapshot body ih =>
      simp [inferWriteSetExpr] at hSet
  | par left right ihLeft ihRight =>
      simp [inferWriteSetExpr] at hSet

mutual

  private def inferSetForeach (txnId : TxnId) (env : Env)
      (doneVar elemVar : VarName) (body : Semantics.Program)
      (done remaining : SetLit) : SetEffect
    | db => do
        match remaining with
        | [] => some SetLanguage.empty
        | current :: rest =>
            let sCurrent ← inferSetEffect txnId (foreachEnv env doneVar elemVar done current) body db
            let sRest ← inferSetForeach txnId env doneVar elemVar body (done ++ [current]) rest db
            pure (.union sCurrent sRest)

  /-- Symbolic effect inference returning a `SetExpr`. This is the explicit-set-language companion
  of `inferEffect` and is the closest Lean analogue of the paper's Fig. 8 transformer. -/
  def inferSetEffect (txnId : TxnId) (env : Env) : Semantics.Program → SetEffect
    | .skip => emptySetEffect
    | .letE x expr body =>
        fun db => do
          let value ← evalInEnv env expr
          inferSetEffect txnId (env.insert x value) body db
    | .ite cond thenBranch elseBranch =>
        fun db => do
          let .scalar (.bool b) ← evalInEnv env cond | none
          if b then inferSetEffect txnId env thenBranch db else inferSetEffect txnId env elseBranch db
    | .seq left right =>
        unionSetEffect (inferSetEffect txnId env left) (inferSetEffect txnId env right)
    | .insert expr =>
        fun _ => insertSetExpr txnId env expr
    | .delete source predicate =>
        fun _ => some (deleteSetExpr txnId env source predicate)
    | .select binder source predicate body =>
        fun db => do
          let selected ← Semantics.collectSelected db source (instantiateExpr env [source] predicate)
          inferSetEffect txnId (env.insert binder (.set selected)) body db
    | .update source updateExpr predicate =>
        fun _ => some (updateSetExpr txnId env source updateExpr predicate)
    | .foreach source doneVar elemVar body =>
        fun db => do
          let .set records ← evalInEnv env source | none
          inferSetForeach txnId env doneVar elemVar body [] records db
    | .foreachRuntime done remaining doneVar elemVar body =>
        fun db => do
          let .set doneRecords ← evalInEnv env done | none
          let .set remainingRecords ← evalInEnv env remaining | none
          inferSetForeach txnId env doneVar elemVar body doneRecords remainingRecords db
    | _ => fun _ => none

end

def SetInferable : Semantics.Program → Prop
  | .skip => True
  | .letE _ _ body => SetInferable body
  | .ite _ thenBranch elseBranch => SetInferable thenBranch ∧ SetInferable elseBranch
  | .seq left right => SetInferable left ∧ SetInferable right
  | .insert _ => True
  | .delete _ _ => True
  | .select _ _ _ body => SetInferable body
  | .update _ _ _ => True
  | .foreach _ _ _ body => SetInferable body
  | .foreachRuntime _ _ _ _ body => SetInferable body
  | .txn _ _ _ => False
  | .txnRuntime _ _ _ _ _ => False
  | .par _ _ => False


mutual

  theorem inferSetForeach_some_of_inferForeach_some (txnId : TxnId) (env : Env)
      (doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
      (hBody :
        ∀ (env' : Env) (rows : Database),
          inferEffect txnId env' body db = some rows →
          ∃ s, inferSetEffect txnId env' body db = some s)
      (done remaining : SetLit) (rows : Database)
      (hEffect : inferForeach txnId env doneVar elemVar body done remaining db = some rows) :
      ∃ s, inferSetForeach txnId env doneVar elemVar body done remaining db = some s := by
    induction remaining generalizing done rows with
    | nil =>
        refine ⟨SetLanguage.empty, ?_⟩
        simp [inferSetForeach]
    | cons current rest ih =>
        rcases infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body db rows
            (by simpa [inferEffect_foreachRuntime_setLit] using hEffect) with
          ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
        rcases hBody (foreachEnv env doneVar elemVar done current) rowsCurrent hCurrentEff with
          ⟨sCurrent, hCurrentSet⟩
        have hRestForeach :
            inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
              some rowsRest := by
          simpa [inferEffect_foreachRuntime_setLit] using hRestEff
        rcases ih (done ++ [current]) rowsRest hRestForeach with ⟨sRest, hRestSet⟩
        refine ⟨.union sCurrent sRest, ?_⟩
        simp [inferSetForeach, hCurrentSet, hRestSet]

theorem inferSetEffect_some_of_inferEffect_some (txnId : TxnId) (env : Env)
      (body : Semantics.Program) (db rows : Database)
      (hInferable : SetInferable body)
      (hEffect : inferEffect txnId env body db = some rows) :
      ∃ s, inferSetEffect txnId env body db = some s := by
    induction body generalizing env rows with
    | skip =>
        refine ⟨SetLanguage.empty, ?_⟩
        simp [inferSetEffect, emptySetEffect]
    | letE x expr body ih =>
        simp [SetInferable] at hInferable
        rcases infer_let_sound txnId env x expr body db rows hEffect with
          ⟨value, hEval, hBodyEff⟩
        rcases ih (env.insert x value) rows hInferable hBodyEff with ⟨s, hSet⟩
        exact ⟨s, by simp [inferSetEffect, hEval, hSet]⟩
    | ite cond thenBranch elseBranch ihThen ihElse =>
        simp [SetInferable] at hInferable
        rcases hInferable with ⟨hThenInferable, hElseInferable⟩
        rcases infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
          ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
        · rcases ihThen env rows hThenInferable hThenEff with ⟨s, hSet⟩
          exact ⟨s, by simp [inferSetEffect, hCond, hSet]⟩
        · rcases ihElse env rows hElseInferable hElseEff with ⟨s, hSet⟩
          exact ⟨s, by simp [inferSetEffect, hCond, hSet]⟩
    | seq left right ihLeft ihRight =>
        simp [SetInferable] at hInferable
        rcases hInferable with ⟨hLeftInferable, hRightInferable⟩
        rcases infer_seq_sound txnId env left right db rows hEffect with
          ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
        rcases ihLeft env rowsLeft hLeftInferable hLeftEff with ⟨sLeft, hLeftSet⟩
        rcases ihRight env rowsRight hRightInferable hRightEff with ⟨sRight, hRightSet⟩
        exact ⟨.union sLeft sRight, by simp [inferSetEffect, unionSetEffect, hLeftSet, hRightSet]⟩
    | insert expr =>
        rcases infer_insert_sound txnId env expr db rows hEffect with ⟨record, hEval, hRows⟩
        refine ⟨SetLanguage.singleton (Row.fromInsert txnId record), ?_⟩
        simp [inferSetEffect, insertSetExpr, evalInEnv, hEval]
    | delete source predicate =>
        exact ⟨deleteSetExpr txnId env source predicate, by simp [inferSetEffect]⟩
    | select binder source predicate body ih =>
        simp [SetInferable] at hInferable
        rcases infer_select_sound txnId env binder source predicate body db rows hEffect with
          ⟨selected, hSelect, hBodyEff⟩
        rcases ih (env.insert binder (.set selected)) rows hInferable hBodyEff with ⟨s, hSet⟩
        exact ⟨s, by simp [inferSetEffect, hSelect, hSet]⟩
    | update source updateExpr predicate =>
        exact ⟨updateSetExpr txnId env source updateExpr predicate, by simp [inferSetEffect]⟩
    | foreach source doneVar elemVar body ih =>
        simp [SetInferable] at hInferable
        rcases infer_foreach_sound txnId env source doneVar elemVar body db rows hEffect with
          ⟨records, hEval, hRuntimeEff⟩
        have hBody :
            ∀ (env' : Env) (rows' : Database),
              inferEffect txnId env' body db = some rows' →
              ∃ s, inferSetEffect txnId env' body db = some s := by
          intro env' rows' hBodyEff
          exact ih env' rows' hInferable hBodyEff
        have hForeach :
            inferForeach txnId env doneVar elemVar body [] records db = some rows := by
          simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
        rcases inferSetForeach_some_of_inferForeach_some txnId env doneVar elemVar body db
            hBody [] records rows hForeach with ⟨s, hSet⟩
        exact ⟨s, by simp [inferSetEffect, hEval, hSet]⟩
    | foreachRuntime done remaining doneVar elemVar body ih =>
        simp [SetInferable] at hInferable
        rcases infer_foreachRuntime_sound txnId env done remaining doneVar elemVar body db rows hEffect with
          ⟨doneRecords, remainingRecords, hDoneEval, hRemainingEval, hRuntimeEff⟩
        have hBody :
            ∀ (env' : Env) (rows' : Database),
              inferEffect txnId env' body db = some rows' →
              ∃ s, inferSetEffect txnId env' body db = some s := by
          intro env' rows' hBodyEff
          exact ih env' rows' hInferable hBodyEff
        have hForeach :
            inferForeach txnId env doneVar elemVar body doneRecords remainingRecords db =
              some rows := by
          simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
        rcases inferSetForeach_some_of_inferForeach_some txnId env doneVar elemVar body db
            hBody doneRecords remainingRecords rows hForeach with ⟨s, hSet⟩
        exact ⟨s, by simp [inferSetEffect, hDoneEval, hRemainingEval, hSet]⟩
    | txn txnId' isolation body =>
        simp [SetInferable] at hInferable
    | txnRuntime txnId' isolation localDb snapshot body =>
        simp [SetInferable] at hInferable
    | par left right =>
        simp [SetInferable] at hInferable

end

theorem option_eq_some_get! {α : Type} [Inhabited α] {o : Option α}
    (hSome : o ≠ none) :
    o = some (Option.get! o) := by
  cases h : o with
  | none =>
      contradiction
  | some value =>
      simp [Option.get!, h]

theorem inferSetForeach_sound (txnId : TxnId) (env : Env)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
    (hBody :
      ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
        inferSetEffect txnId env' body db = some s →
        inferEffect txnId env' body db = some rows →
        (SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows))
    (done remaining : SetLit) (s : SetLanguage.SetExpr) (rows : Database) (row : Row)
    (hSet : inferSetForeach txnId env doneVar elemVar body done remaining db = some s)
    (hEffect : inferForeach txnId env doneVar elemVar body done remaining db = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows := by
  induction remaining generalizing done s rows row with
  | nil =>
      simp [inferSetForeach] at hSet
      simp [inferForeach] at hEffect
      subst s
      subst rows
      simp [SetLanguage.empty, SetLanguage.denote]
  | cons current rest ih =>
      cases hCurrentSet :
          inferSetEffect txnId (foreachEnv env doneVar elemVar done current) body db with
      | none =>
          simp [inferSetForeach, hCurrentSet] at hSet
      | some sCurrent =>
          cases hRestSet :
              inferSetForeach txnId env doneVar elemVar body (done ++ [current]) rest db with
          | none =>
              simp [inferSetForeach, hCurrentSet, hRestSet] at hSet
          | some sRest =>
              simp [inferSetForeach, hCurrentSet, hRestSet] at hSet
              cases hSet
              rcases infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body
                  db rows (by simpa [inferEffect_foreachRuntime_setLit] using hEffect) with
                ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
              have hRestForeach :
                  inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                    some rowsRest := by
                simpa [inferEffect_foreachRuntime_setLit] using hRestEff
              have hDenCurrent :
                  SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) sCurrent row ↔
                    row ∈ rowsCurrent := by
                exact hBody (foreachEnv env doneVar elemVar done current)
                  sCurrent rowsCurrent row hCurrentSet hCurrentEff
              have hDenRest := ih (done ++ [current]) sRest rowsRest row hRestSet hRestForeach
              simp [SetLanguage.denote_union, hDenCurrent, hDenRest, hRows]

theorem inferSetEffect_sound (txnId : TxnId) (env : Env)
    (body : Semantics.Program) (db : Database) (s : SetLanguage.SetExpr)
    (rows : Database) (row : Row)
    (hSet : inferSetEffect txnId env body db = some s)
    (hEffect : inferEffect txnId env body db = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows := by
  induction body generalizing env s rows row with
  | skip =>
      simp [inferSetEffect, emptySetEffect, inferEffect, emptyEffect] at hSet hEffect
      subst s
      subst rows
      simp [SetLanguage.empty, SetLanguage.denote]
  | letE x expr body ih =>
      rcases infer_let_sound txnId env x expr body db rows hEffect with
        ⟨value, hEval, hBodyEff⟩
      simp [inferSetEffect, hEval] at hSet
      exact ih (env.insert x value) s rows row hSet hBodyEff
  | ite cond thenBranch elseBranch ihThen ihElse =>
      rcases infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
        ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
      · simp [inferSetEffect, hCond] at hSet
        exact ihThen env s rows row hSet hThenEff
      · simp [inferSetEffect, hCond] at hSet
        exact ihElse env s rows row hSet hElseEff
  | seq left right ihLeft ihRight =>
      cases hLeftSet : inferSetEffect txnId env left db with
      | none =>
          simp [inferSetEffect, unionSetEffect, hLeftSet] at hSet
      | some sLeft =>
          cases hRightSet : inferSetEffect txnId env right db with
          | none =>
              simp [inferSetEffect, unionSetEffect, hLeftSet, hRightSet] at hSet
          | some sRight =>
              simp [inferSetEffect, unionSetEffect, hLeftSet, hRightSet] at hSet
              cases hSet
              rcases infer_seq_sound txnId env left right db rows hEffect with
                ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
              have hDenLeft := ihLeft env sLeft rowsLeft row hLeftSet hLeftEff
              have hDenRight := ihRight env sRight rowsRight row hRightSet hRightEff
              simp [SetLanguage.denote_union, hDenLeft, hDenRight, hRows]
  | insert expr =>
      rcases insertSetExpr_sound txnId env expr s (by simpa [inferSetEffect] using hSet) with
        ⟨record, rfl, hEval⟩
      rcases infer_insert_sound txnId env expr db rows hEffect with ⟨record', hEval', hRows⟩
      have hEvalExpr : Expr.eval (instantiateExpr env [] expr) = some (.record record) := by
        simpa [evalInEnv] using hEval
      rw [hEvalExpr] at hEval'
      injection hEval' with hRecord
      cases hRecord
      simp [SetLanguage.denote_singleton, hRows]
  | delete source predicate =>
      simp [inferSetEffect] at hSet
      subst s
      exact deleteSetExpr_sound txnId env source predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | select binder source predicate body ih =>
      rcases infer_select_sound txnId env binder source predicate body db rows hEffect with
        ⟨selected, hSelect, hBodyEff⟩
      simp [inferSetEffect, hSelect] at hSet
      exact ih (env.insert binder (.set selected)) s rows row hSet hBodyEff
  | update source updateExpr predicate =>
      simp [inferSetEffect] at hSet
      subst s
      exact updateSetExpr_sound txnId env source updateExpr predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | foreach source doneVar elemVar body ih =>
      rcases infer_foreach_sound txnId env source doneVar elemVar body db rows hEffect with
        ⟨records, hSourceEval, hRuntimeEff⟩
      simp [inferSetEffect, hSourceEval] at hSet
      have hForeachEff :
          inferForeach txnId env doneVar elemVar body [] records db = some rows := by
        simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
      have hBodySound :
          ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
            inferSetEffect txnId env' body db = some s →
            inferEffect txnId env' body db = some rows →
            (SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows) := by
        intro env' s rows row hSetBody hEffectBody
        exact ih env' s rows row hSetBody hEffectBody
      exact inferSetForeach_sound txnId env doneVar elemVar body db
        hBodySound
        [] records s rows row hSet hForeachEff
  | foreachRuntime done remaining doneVar elemVar body ih =>
      rcases infer_foreachRuntime_sound txnId env done remaining doneVar elemVar body db rows hEffect with
        ⟨doneRecords, remainingRecords, hDoneEval, hRemainingEval, hRuntimeEff⟩
      simp [inferSetEffect, hDoneEval, hRemainingEval] at hSet
      have hForeachEff :
          inferForeach txnId env doneVar elemVar body doneRecords remainingRecords db = some rows := by
        simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
      have hBodySound :
          ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
            inferSetEffect txnId env' body db = some s →
            inferEffect txnId env' body db = some rows →
            (SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row ↔ row ∈ rows) := by
        intro env' s rows row hSetBody hEffectBody
        exact ih env' s rows row hSetBody hEffectBody
      exact inferSetForeach_sound txnId env doneVar elemVar body db
        hBodySound
        doneRecords remainingRecords s rows row hSet hForeachEff
  | txn txnId' isolation body ih =>
      simp [inferSetEffect] at hSet
  | txnRuntime txnId' isolation localDb snapshot body ih =>
      simp [inferSetEffect] at hSet
  | par left right ihLeft ihRight =>
      simp [inferSetEffect] at hSet

theorem inferSetForeach_abstractGlobal_sound (absVar : VarName) (txnId : TxnId) (env : Env)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
    (hBody :
      ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
        inferSetEffect txnId env' body db = some s →
        inferEffect txnId env' body db = some rows →
        (SetLanguage.denote (setEnvOfDatabase absVar db) (SetLanguage.abstractGlobal absVar s) row ↔
          row ∈ rows))
    (done remaining : SetLit) (s : SetLanguage.SetExpr) (rows : Database) (row : Row)
    (hSet : inferSetForeach txnId env doneVar elemVar body done remaining db = some s)
    (hEffect : inferForeach txnId env doneVar elemVar body done remaining db = some rows) :
    SetLanguage.denote (setEnvOfDatabase absVar db) (SetLanguage.abstractGlobal absVar s) row ↔
      row ∈ rows := by
  induction remaining generalizing done s rows row with
  | nil =>
      simp [inferSetForeach] at hSet
      simp [inferForeach] at hEffect
      subst s
      subst rows
      simp [SetLanguage.empty, SetLanguage.denote, SetLanguage.abstractGlobal]
  | cons current rest ih =>
      cases hCurrentSet :
          inferSetEffect txnId (foreachEnv env doneVar elemVar done current) body db with
      | none =>
          simp [inferSetForeach, hCurrentSet] at hSet
      | some sCurrent =>
          cases hRestSet :
              inferSetForeach txnId env doneVar elemVar body (done ++ [current]) rest db with
          | none =>
              simp [inferSetForeach, hCurrentSet, hRestSet] at hSet
          | some sRest =>
              simp [inferSetForeach, hCurrentSet, hRestSet] at hSet
              cases hSet
              rcases infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body
                  db rows (by simpa [inferEffect_foreachRuntime_setLit] using hEffect) with
                ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
              have hRestForeach :
                  inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                    some rowsRest := by
                simpa [inferEffect_foreachRuntime_setLit] using hRestEff
              have hDenCurrent := hBody (foreachEnv env doneVar elemVar done current)
                sCurrent rowsCurrent row hCurrentSet hCurrentEff
              have hDenRest := ih (done ++ [current]) sRest rowsRest row hRestSet hRestForeach
              simp [SetLanguage.abstractGlobal_union, SetLanguage.denote_union, hDenCurrent, hDenRest, hRows]

theorem inferSetEffect_abstractGlobal_sound (absVar : VarName) (txnId : TxnId) (env : Env)
    (body : Semantics.Program) (db : Database) (s : SetLanguage.SetExpr)
    (rows : Database) (row : Row)
    (hSet : inferSetEffect txnId env body db = some s)
    (hEffect : inferEffect txnId env body db = some rows) :
    SetLanguage.denote (setEnvOfDatabase absVar db) (SetLanguage.abstractGlobal absVar s) row ↔
      row ∈ rows := by
  induction body generalizing env s rows row with
  | skip =>
      simp [inferSetEffect, emptySetEffect, inferEffect, emptyEffect] at hSet hEffect
      subst s
      subst rows
      simp [SetLanguage.empty, SetLanguage.denote, SetLanguage.abstractGlobal]
  | letE x expr body ih =>
      rcases infer_let_sound txnId env x expr body db rows hEffect with
        ⟨value, hEval, hBodyEff⟩
      simp [inferSetEffect, hEval] at hSet
      exact ih (env.insert x value) s rows row hSet hBodyEff
  | ite cond thenBranch elseBranch ihThen ihElse =>
      rcases infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
        ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
      · simp [inferSetEffect, hCond] at hSet
        simpa [SetLanguage.abstractGlobal_ite] using ihThen env s rows row hSet hThenEff
      · simp [inferSetEffect, hCond] at hSet
        simpa [SetLanguage.abstractGlobal_ite] using ihElse env s rows row hSet hElseEff
  | seq left right ihLeft ihRight =>
      cases hLeftSet : inferSetEffect txnId env left db with
      | none =>
          simp [inferSetEffect, unionSetEffect, hLeftSet] at hSet
      | some sLeft =>
          cases hRightSet : inferSetEffect txnId env right db with
          | none =>
              simp [inferSetEffect, unionSetEffect, hLeftSet, hRightSet] at hSet
          | some sRight =>
              simp [inferSetEffect, unionSetEffect, hLeftSet, hRightSet] at hSet
              cases hSet
              rcases infer_seq_sound txnId env left right db rows hEffect with
                ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
              have hDenLeft := ihLeft env sLeft rowsLeft row hLeftSet hLeftEff
              have hDenRight := ihRight env sRight rowsRight row hRightSet hRightEff
              simp [SetLanguage.abstractGlobal_union, SetLanguage.denote_union, hDenLeft, hDenRight, hRows]
  | insert expr =>
      rcases insertSetExpr_sound txnId env expr s (by simpa [inferSetEffect] using hSet) with
        ⟨record, rfl, hEval⟩
      rcases infer_insert_sound txnId env expr db rows hEffect with ⟨record', hEval', hRows⟩
      have hEvalExpr : Expr.eval (instantiateExpr env [] expr) = some (.record record) := by
        simpa [evalInEnv] using hEval
      rw [hEvalExpr] at hEval'
      injection hEval' with hRecord
      cases hRecord
      simp [SetLanguage.singleton, SetLanguage.denote, SetLanguage.abstractGlobal, hRows]
  | delete source predicate =>
      simp [inferSetEffect] at hSet
      subst s
      exact deleteSetExpr_abstractGlobal_sound absVar txnId env source predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | select binder source predicate body ih =>
      rcases infer_select_sound txnId env binder source predicate body db rows hEffect with
        ⟨selected, hSelect, hBodyEff⟩
      simp [inferSetEffect, hSelect] at hSet
      exact ih (env.insert binder (.set selected)) s rows row hSet hBodyEff
  | update source updateExpr predicate =>
      simp [inferSetEffect] at hSet
      subst s
      exact updateSetExpr_abstractGlobal_sound absVar txnId env source updateExpr predicate db rows row
        (by simpa [inferEffect] using hEffect)
  | foreach source doneVar elemVar body ih =>
      rcases infer_foreach_sound txnId env source doneVar elemVar body db rows hEffect with
        ⟨records, hSourceEval, hRuntimeEff⟩
      simp [inferSetEffect, hSourceEval] at hSet
      have hForeachEff :
          inferForeach txnId env doneVar elemVar body [] records db = some rows := by
        simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
      have hBodySound :
          ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
            inferSetEffect txnId env' body db = some s →
            inferEffect txnId env' body db = some rows →
            (SetLanguage.denote (setEnvOfDatabase absVar db) (SetLanguage.abstractGlobal absVar s) row ↔
              row ∈ rows) := by
        intro env' s rows row hSetBody hEffectBody
        exact ih env' s rows row hSetBody hEffectBody
      exact inferSetForeach_abstractGlobal_sound absVar txnId env doneVar elemVar body db
        hBodySound [] records s rows row hSet hForeachEff
  | foreachRuntime done remaining doneVar elemVar body ih =>
      rcases infer_foreachRuntime_sound txnId env done remaining doneVar elemVar body db rows hEffect with
        ⟨doneRecords, remainingRecords, hDoneEval, hRemainingEval, hRuntimeEff⟩
      simp [inferSetEffect, hDoneEval, hRemainingEval] at hSet
      have hForeachEff :
          inferForeach txnId env doneVar elemVar body doneRecords remainingRecords db = some rows := by
        simpa [inferEffect_foreachRuntime_setLit] using hRuntimeEff
      have hBodySound :
          ∀ (env' : Env) (s : SetLanguage.SetExpr) (rows : Database) (row : Row),
            inferSetEffect txnId env' body db = some s →
            inferEffect txnId env' body db = some rows →
            (SetLanguage.denote (setEnvOfDatabase absVar db) (SetLanguage.abstractGlobal absVar s) row ↔
              row ∈ rows) := by
        intro env' s rows row hSetBody hEffectBody
        exact ih env' s rows row hSetBody hEffectBody
      exact inferSetForeach_abstractGlobal_sound absVar txnId env doneVar elemVar body db
        hBodySound doneRecords remainingRecords s rows row hSet hForeachEff
  | txn txnId' isolation body ih =>
      simp [inferSetEffect] at hSet
  | txnRuntime txnId' isolation localDb snapshot body ih =>
      simp [inferSetEffect] at hSet
  | par left right ihLeft ihRight =>
      simp [inferSetEffect] at hSet

theorem weakenToInvariant_of_abstractGlobal (I : Assertion) (absVar : VarName)
    (db : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInv : I db)
    (hAbs :
      SetLanguage.denote (setEnvOfDatabase absVar db)
        (SetLanguage.abstractGlobal absVar s) row) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  refine ⟨currentGlobalBinding db, ?_, ?_⟩
  · exact assertionFormula_current I absVar db hInv
  · simpa [setEnvOfDatabase, currentGlobalBinding]

theorem inferSetEffect_weaken_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (env : Env) (body : Semantics.Program) (db : Database)
    (s : SetLanguage.SetExpr) (rows : Database) (row : Row)
    (hInv : I db)
    (hSet : inferSetEffect txnId env body db = some s)
    (hEffect : inferEffect txnId env body db = some rows)
    (hRow : row ∈ rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  have hAbs :
      SetLanguage.denote (setEnvOfDatabase absVar db)
        (SetLanguage.abstractGlobal absVar s) row := by
    exact (inferSetEffect_abstractGlobal_sound absVar txnId env body db s rows row hSet hEffect).2 hRow
  exact weakenToInvariant_of_abstractGlobal I absVar db s row hInv hAbs

theorem inferSetEffect_weaken_overapprox (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (env : Env) (body : Semantics.Program) (db : Database)
    (s : SetLanguage.SetExpr) (rows : Database)
    (hInv : I db)
    (hSet : inferSetEffect txnId env body db = some s)
    (hEffect : inferEffect txnId env body db = some rows) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] db)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) rows := by
  intro row hRow
  exact inferSetEffect_weaken_sound I absVar txnId env body db s rows row hInv hSet hEffect hRow

end Transformer

end DbAppProgramLogic
