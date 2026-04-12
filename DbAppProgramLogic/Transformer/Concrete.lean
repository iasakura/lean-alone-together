import DbAppProgramLogic.Transformer.Basic

namespace DbAppProgramLogic

namespace Transformer

theorem inferenceSound_of_env_empty (txnId : TxnId) (body : Semantics.Program) (F : TxnEffect)
    (h : inferenceSoundEnv txnId [] body F) :
    inferenceSound txnId body F := by
  intro visibleDb localDb' hInfer
  simpa [inferenceSoundEnv, inferenceSound, instantiateCommand_nil] using h visibleDb localDb' hInfer

theorem inferenceSoundEnv_skip (txnId : TxnId) (env : Env) :
    inferenceSoundEnv txnId env (.skip : Semantics.Program)
      (inferEffect txnId env (.skip : Semantics.Program)) := by
  intro visibleDb localDb' hInfer
  simp [inferenceSoundEnv, inferEffect, emptyEffect] at hInfer ⊢
  subst localDb'
  simpa using
    (Logic.localValid_skip_false
      (ι := IsolationSpec Database)
      txnId
      (P := fun localDb visible => localDb = [] ∧ visible = visibleDb))

theorem inferenceSound_skip (txnId : TxnId) :
    inferenceSound txnId (.skip : Semantics.Program)
      (inferEffect txnId [] (.skip : Semantics.Program)) := by
  exact inferenceSound_of_env_empty txnId (.skip : Semantics.Program)
    (inferEffect txnId [] (.skip : Semantics.Program))
    (inferenceSoundEnv_skip txnId [])

theorem infer_skip_sound (txnId : TxnId) (env : Env) (db : Database) :
    inferEffect txnId env (.skip : Semantics.Program) db = some [] := by
  simp [inferEffect, emptyEffect]

theorem infer_insert_sound (txnId : TxnId) (env : Env) (expr : Expr) (db : Database) (delta : Database)
    (h : inferEffect txnId env (.insert expr) db = some delta) :
    ∃ record,
      Expr.eval (instantiateExpr env [] expr) = some (.record record) ∧
      delta = [Row.fromInsert txnId record] := by
  cases hEval : evalInEnv env expr with
  | none =>
      have hEval' : Expr.eval (instantiateExpr env [] expr) = none := by
        simpa [evalInEnv] using hEval
      have : False := by
        simp [inferEffect, evalInEnv, hEval'] at h
      exact False.elim this
  | some value =>
      cases value with
      | scalar s =>
          have hEval' : Expr.eval (instantiateExpr env [] expr) = some (.scalar s) := by
            simpa [evalInEnv] using hEval
          have : False := by
            simp [inferEffect, evalInEnv, hEval'] at h
          exact False.elim this
      | set s =>
          have hEval' : Expr.eval (instantiateExpr env [] expr) = some (.set s) := by
            simpa [evalInEnv] using hEval
          have : False := by
            simp [inferEffect, evalInEnv, hEval'] at h
          exact False.elim this
      | record record =>
          have hEval' : Expr.eval (instantiateExpr env [] expr) = some (.record record) := by
            simpa [evalInEnv] using hEval
          simp [inferEffect, evalInEnv, hEval'] at h
          refine ⟨record, ?_, ?_⟩
          · exact hEval'
          · exact h.symm

theorem infer_let_sound (txnId : TxnId) (env : Env) (x : VarName) (expr : Expr)
    (body : Semantics.Program) (db delta : Database)
    (h : inferEffect txnId env (.letE x expr body) db = some delta) :
    ∃ value,
      evalInEnv env expr = some value ∧
      inferEffect txnId (env.insert x value) body db = some delta := by
  cases hEval : evalInEnv env expr with
  | none =>
      have : False := by
        simp [inferEffect, hEval] at h
      exact False.elim this
  | some value =>
      refine ⟨value, rfl, ?_⟩
      simpa [inferEffect, hEval] using h

theorem inferenceSoundEnv_let (txnId : TxnId) (env : Env) (x : VarName) (expr : Expr)
    (body : Semantics.Program)
    (hBody :
      ∀ value,
        evalInEnv env expr = some value →
        inferenceSoundEnv txnId (env.insert x value) body
          (inferEffect txnId (env.insert x value) body)) :
    inferenceSoundEnv txnId env (.letE x expr body)
      (inferEffect txnId env (.letE x expr body)) := by
  intro visibleDb localDb' hInfer
  rcases infer_let_sound txnId env x expr body visibleDb localDb' hInfer with
    ⟨value, hEval, hBodyInfer⟩
  have hEval' : Expr.eval (instantiateExpr env [] expr) = some value := by
    simpa [evalInEnv] using hEval
  have hBodyValid :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ visible = visibleDb)
        (Command.subst x value.toExpr
          (instantiateCommand (ι := IsolationSpec Database) (env.erase x) body) :
            Command (IsolationSpec Database) Database)
        (fun localDb visible => localDb = localDb' ∧ visible = visibleDb) := by
    have hBodyValid' := hBody value hEval visibleDb localDb' hBodyInfer
    simpa [instantiateCommand_insert] using hBodyValid'
  simpa [inferenceSoundEnv, instantiateCommand] using
    (Logic.localValid_let_false
      (ι := IsolationSpec Database)
      (txnId := txnId)
      (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
      (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
      (x := x)
      (expr := instantiateExpr env [] expr)
      (body := instantiateCommand (ι := IsolationSpec Database) (env.erase x) body)
      (value := value)
      hEval'
      hBodyValid)

theorem inferenceSound_let (txnId : TxnId) (x : VarName) (expr : Expr)
    (body : Semantics.Program)
    (hBody :
      ∀ value,
        Expr.eval expr = some value →
        inferenceSoundEnv txnId [(x, value)] body
          (inferEffect txnId [(x, value)] body)) :
    inferenceSound txnId (.letE x expr body)
      (inferEffect txnId [] (.letE x expr body)) := by
  refine inferenceSound_of_env_empty txnId (.letE x expr body)
    (inferEffect txnId [] (.letE x expr body)) ?_
  refine inferenceSoundEnv_let txnId [] x expr body ?_
  intro value hEval
  have hEval' : Expr.eval expr = some value := by
    simpa [evalInEnv_nil] using hEval
  have hBody' := hBody value hEval'
  simpa [Env.insert, instantiateCommand_nil, Env.erase] using hBody'

theorem infer_ite_sound (txnId : TxnId) (env : Env) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program)
    (db delta : Database) (h : inferEffect txnId env (.ite cond thenBranch elseBranch) db = some delta) :
    (evalInEnv env cond = some (.scalar (.bool true)) ∧
        inferEffect txnId env thenBranch db = some delta) ∨
      (evalInEnv env cond = some (.scalar (.bool false)) ∧
        inferEffect txnId env elseBranch db = some delta) := by
  cases hEval : evalInEnv env cond with
  | none =>
      have : False := by
        simp [inferEffect, hEval] at h
      exact False.elim this
  | some value =>
      cases value with
      | record record =>
          have : False := by
            simp [inferEffect, hEval] at h
          exact False.elim this
      | set records =>
          have : False := by
            simp [inferEffect, hEval] at h
          exact False.elim this
      | scalar lit =>
          cases lit with
          | int n =>
              have : False := by
                simp [inferEffect, hEval] at h
              exact False.elim this
          | bool b =>
              cases b with
              | false =>
                  right
                  constructor
                  · exact rfl
                  · simpa [inferEffect, hEval] using h
              | true =>
                  left
                  constructor
                  · exact rfl
                  · simpa [inferEffect, hEval] using h

theorem infer_seq_sound (txnId : TxnId) (env : Env) (left right : Semantics.Program)
    (db delta : Database) (h : inferEffect txnId env (.seq left right) db = some delta) :
    ∃ deltaLeft deltaRight,
      inferEffect txnId env left db = some deltaLeft ∧
      inferEffect txnId env right db = some deltaRight ∧
      delta = deltaLeft ++ deltaRight := by
  cases hLeft : inferEffect txnId env left db with
  | none =>
      have : False := by
        simp [inferEffect, unionEffect, hLeft] at h
      exact False.elim this
  | some deltaLeft =>
      cases hRight : inferEffect txnId env right db with
      | none =>
          have : False := by
            simp [inferEffect, unionEffect, hLeft, hRight] at h
          exact False.elim this
      | some deltaRight =>
          have hEq : deltaLeft ++ deltaRight = delta := by
              simp [inferEffect, unionEffect, hLeft, hRight] at h
              exact h
          exact ⟨deltaLeft, deltaRight, rfl, rfl, hEq.symm⟩


theorem inferenceSoundEnv_seq (txnId : TxnId) (env : Env)
    (left right : Semantics.Program)
    (hLeft : inferenceSoundEnv txnId env left (inferEffect txnId env left))
    (hRight : inferenceSoundEnv txnId env right (inferEffect txnId env right)) :
    inferenceSoundEnv txnId env (.seq left right)
      (inferEffect txnId env (.seq left right)) := by
  intro visibleDb localDb' hInfer
  rcases infer_seq_sound txnId env left right visibleDb localDb' hInfer with
    ⟨deltaLeft, deltaRight, hLeftInfer, hRightInfer, hDelta⟩
  have hLeftValid := hLeft visibleDb deltaLeft hLeftInfer
  have hRightValidBase := hRight visibleDb deltaRight hRightInfer
  have hRightValid :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = deltaLeft ∧ visible = visibleDb)
        (instantiateCommand (ι := IsolationSpec Database) env right)
        (fun localDb visible => localDb = deltaLeft ++ deltaRight ∧ visible = visibleDb) := by
    exact _root_.DbAppProgramLogic.Logic.localValid_prepend_false
      (ι := IsolationSpec Database)
      txnId
      deltaLeft
      visibleDb
      deltaRight
      (instantiateCommand (ι := IsolationSpec Database) env right)
      hRightValidBase
  simpa [inferenceSoundEnv, instantiateCommand, hDelta] using
    (_root_.DbAppProgramLogic.Logic.localValid_seq_false
      (ι := IsolationSpec Database)
      (txnId := txnId)
      (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
      (P' := fun localDb visible => localDb = deltaLeft ∧ visible = visibleDb)
      (Q := fun localDb visible => localDb = deltaLeft ++ deltaRight ∧ visible = visibleDb)
      (left := instantiateCommand (ι := IsolationSpec Database) env left)
      (right := instantiateCommand (ι := IsolationSpec Database) env right)
      hLeftValid
      hRightValid)

theorem inferenceSound_seq (txnId : TxnId) (left right : Semantics.Program)
    (hLeft : inferenceSound txnId left (inferEffect txnId [] left))
    (hRight : inferenceSound txnId right (inferEffect txnId [] right)) :
    inferenceSound txnId (.seq left right)
      (inferEffect txnId [] (.seq left right)) := by
  have hLeftEnv : inferenceSoundEnv txnId [] left (inferEffect txnId [] left) := by
    intro visibleDb localDb' hInfer
    simpa [inferenceSoundEnv, inferenceSound, instantiateCommand_nil] using
      hLeft visibleDb localDb' hInfer
  have hRightEnv : inferenceSoundEnv txnId [] right (inferEffect txnId [] right) := by
    intro visibleDb localDb' hInfer
    simpa [inferenceSoundEnv, inferenceSound, instantiateCommand_nil] using
      hRight visibleDb localDb' hInfer
  exact inferenceSound_of_env_empty txnId (.seq left right)
    (inferEffect txnId [] (.seq left right))
    (inferenceSoundEnv_seq txnId [] left right hLeftEnv hRightEnv)

theorem inferenceSoundEnv_ite (txnId : TxnId) (env : Env) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program)
    (hThen : inferenceSoundEnv txnId env thenBranch (inferEffect txnId env thenBranch))
    (hElse : inferenceSoundEnv txnId env elseBranch (inferEffect txnId env elseBranch)) :
    inferenceSoundEnv txnId env (.ite cond thenBranch elseBranch)
      (inferEffect txnId env (.ite cond thenBranch elseBranch)) := by
  intro visibleDb localDb' hInfer
  refine Logic.localValid_ite_false
    (ι := IsolationSpec Database)
    (txnId := txnId)
    (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
    (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
    (cond := instantiateExpr env [] cond)
    (thenBranch := instantiateCommand env thenBranch)
    (elseBranch := instantiateCommand env elseBranch)
    ?_ ?_
  · intro hEvalTrue
    have hEvalTrue' : evalInEnv env cond = some (.scalar (.bool true)) := by
      simpa [evalInEnv] using hEvalTrue
    have hThenInfer : inferEffect txnId env thenBranch visibleDb = some localDb' := by
      rcases infer_ite_sound txnId env cond thenBranch elseBranch visibleDb localDb' hInfer with
        hThenCase | hElseCase
      · exact hThenCase.2
      · have hImpossible : some (.scalar (.bool true) : Value) = some (.scalar (.bool false)) := by
          rw [← hEvalTrue', hElseCase.1]
        cases hImpossible
    exact hThen visibleDb localDb' hThenInfer
  · intro hEvalFalse
    have hEvalFalse' : evalInEnv env cond = some (.scalar (.bool false)) := by
      simpa [evalInEnv] using hEvalFalse
    have hElseInfer : inferEffect txnId env elseBranch visibleDb = some localDb' := by
      rcases infer_ite_sound txnId env cond thenBranch elseBranch visibleDb localDb' hInfer with
        hThenCase | hElseCase
      · have hImpossible : some (.scalar (.bool false) : Value) = some (.scalar (.bool true)) := by
          rw [← hEvalFalse', hThenCase.1]
        cases hImpossible
      · exact hElseCase.2
    exact hElse visibleDb localDb' hElseInfer

theorem inferenceSound_ite (txnId : TxnId) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program)
    (hThen : inferenceSound txnId thenBranch (inferEffect txnId [] thenBranch))
    (hElse : inferenceSound txnId elseBranch (inferEffect txnId [] elseBranch)) :
    inferenceSound txnId (.ite cond thenBranch elseBranch)
      (inferEffect txnId [] (.ite cond thenBranch elseBranch)) := by
  have hThenEnv : inferenceSoundEnv txnId [] thenBranch (inferEffect txnId [] thenBranch) := by
    intro visibleDb localDb' hInfer
    simpa [inferenceSoundEnv, inferenceSound, instantiateCommand_nil] using
      hThen visibleDb localDb' hInfer
  have hElseEnv : inferenceSoundEnv txnId [] elseBranch (inferEffect txnId [] elseBranch) := by
    intro visibleDb localDb' hInfer
    simpa [inferenceSoundEnv, inferenceSound, instantiateCommand_nil] using
      hElse visibleDb localDb' hInfer
  exact inferenceSound_of_env_empty txnId (.ite cond thenBranch elseBranch)
    (inferEffect txnId [] (.ite cond thenBranch elseBranch))
    (inferenceSoundEnv_ite txnId [] cond thenBranch elseBranch hThenEnv hElseEnv)

theorem infer_delete_sound (txnId : TxnId) (env : Env) (source : VarName) (predicate : Expr)
    (db delta : Database) (h : inferEffect txnId env (.delete source predicate) db = some delta) :
    Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate) = some delta := by
  simpa [inferEffect] using h

theorem infer_update_sound (txnId : TxnId) (env : Env) (source : VarName)
    (updateExpr predicate : Expr) (db delta : Database)
    (h : inferEffect txnId env (.update source updateExpr predicate) db = some delta) :
    Semantics.collectUpdated
      db
      txnId
      source
      (instantiateExpr env [source] updateExpr)
      (instantiateExpr env [source] predicate) = some delta := by
  simpa [inferEffect] using h


theorem inferenceSoundEnv_insert (txnId : TxnId) (env : Env) (expr : Expr) :
    inferenceSoundEnv txnId env (.insert expr)
      (inferEffect txnId env (.insert expr)) := by
  intro visibleDb localDb' hInfer
  refine _root_.DbAppProgramLogic.Logic.localValid_insert_false
    (ι := IsolationSpec Database)
    (txnId := txnId)
    (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
    (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
    (expr := instantiateExpr env [] expr)
    ?_
  intro localDb visibleDb' record hPre hEval hFresh
  rcases hPre with ⟨rfl, rfl⟩
  rcases infer_insert_sound txnId env expr visibleDb' localDb' hInfer with
    ⟨record', hEval', hDelta⟩
  have hRecord : record = record' := by
    rw [hEval'] at hEval
    injection hEval with hValue
    injection hValue with hRecord
    exact hRecord.symm
  subst hRecord
  constructor
  · simp [hDelta]
  · rfl

theorem inferenceSound_insert (txnId : TxnId) (expr : Expr) :
    inferenceSound txnId (.insert expr)
      (inferEffect txnId [] (.insert expr)) := by
  exact inferenceSound_of_env_empty txnId (.insert expr)
    (inferEffect txnId [] (.insert expr))
    (inferenceSoundEnv_insert txnId [] expr)

theorem inferenceSoundEnv_delete (txnId : TxnId) (env : Env) (source : VarName)
    (predicate : Expr) :
    inferenceSoundEnv txnId env (.delete source predicate)
      (inferEffect txnId env (.delete source predicate)) := by
  intro visibleDb localDb' hInfer
  refine _root_.DbAppProgramLogic.Logic.localValid_delete_false
    (ι := IsolationSpec Database)
    (txnId := txnId)
    (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
    (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
    (source := source)
    (predicate := instantiateExpr env [source] predicate)
    ?_
  intro localDb visibleDb' removed hPre hDelete _hDisjoint
  rcases hPre with ⟨rfl, rfl⟩
  have hDelete' := infer_delete_sound txnId env source predicate visibleDb' localDb' hInfer
  have hEq : removed = localDb' := by
    have : some removed = some localDb' := by
      rw [← hDelete', hDelete]
    exact Option.some.inj this
  subst hEq
  constructor
  · simp
  · rfl

theorem inferenceSound_delete (txnId : TxnId) (source : VarName) (predicate : Expr) :
    inferenceSound txnId (.delete source predicate)
      (inferEffect txnId [] (.delete source predicate)) := by
  exact inferenceSound_of_env_empty txnId (.delete source predicate)
    (inferEffect txnId [] (.delete source predicate))
    (inferenceSoundEnv_delete txnId [] source predicate)

theorem inferenceSoundEnv_update (txnId : TxnId) (env : Env) (source : VarName)
    (updateExpr predicate : Expr) :
    inferenceSoundEnv txnId env (.update source updateExpr predicate)
      (inferEffect txnId env (.update source updateExpr predicate)) := by
  intro visibleDb localDb' hInfer
  refine _root_.DbAppProgramLogic.Logic.localValid_update_false
    (ι := IsolationSpec Database)
    (txnId := txnId)
    (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
    (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
    (source := source)
    (updateExpr := instantiateExpr env [source] updateExpr)
    (predicate := instantiateExpr env [source] predicate)
    ?_
  intro localDb visibleDb' updated hPre hUpdate _hDisjoint
  rcases hPre with ⟨rfl, rfl⟩
  have hUpdate' := infer_update_sound txnId env source updateExpr predicate visibleDb' localDb' hInfer
  have hEq : updated = localDb' := by
    have : some updated = some localDb' := by
      rw [← hUpdate', hUpdate]
    exact Option.some.inj this
  subst hEq
  constructor
  · simp
  · rfl

theorem inferenceSound_update (txnId : TxnId) (source : VarName)
    (updateExpr predicate : Expr) :
    inferenceSound txnId (.update source updateExpr predicate)
      (inferEffect txnId [] (.update source updateExpr predicate)) := by
  exact inferenceSound_of_env_empty txnId (.update source updateExpr predicate)
    (inferEffect txnId [] (.update source updateExpr predicate))
    (inferenceSoundEnv_update txnId [] source updateExpr predicate)

theorem localStep_insert_of_infer (txnId : TxnId) (env : Env) (expr : Expr)
    (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.insert expr : Semantics.Program)) visibleDb = some delta)
    (hFresh :
      ∀ record,
        Expr.eval (instantiateExpr env [] expr) = some (.record record) →
        Semantics.insertFresh visibleDb localDb record) :
    Semantics.LocalStep
      visibleDb
      txnId
      (instantiateCommand (ι := IsolationSpec Database) env (.insert expr : Semantics.Program))
      localDb
      (.skip : Command (IsolationSpec Database) Database)
      (localDb ++ delta) := by
  rcases infer_insert_sound txnId env expr visibleDb delta hInfer with ⟨record, hEval, hDelta⟩
  subst hDelta
  simpa [instantiateCommand] using
    (Semantics.LocalStep.insert
      (snapshot := visibleDb)
      (txnId := txnId)
      (expr := instantiateExpr env [] expr)
      (record := record)
      (localDb := localDb)
      hEval
      (hFresh record hEval))

theorem localStep_let_of_infer (txnId : TxnId) (env : Env) (x : VarName) (expr : Expr)
    (body : Semantics.Program) (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.letE x expr body : Semantics.Program)) visibleDb = some delta) :
    ∃ value,
      evalInEnv env expr = some value ∧
      inferEffect txnId (env.insert x value) body visibleDb = some delta ∧
      Semantics.LocalStep
        visibleDb
        txnId
        (instantiateCommand (ι := IsolationSpec Database) env (.letE x expr body : Semantics.Program))
        localDb
        (Command.subst x value.toExpr
          (instantiateCommand (ι := IsolationSpec Database) (env.erase x) body) :
            Command (IsolationSpec Database) Database)
        localDb := by
  rcases infer_let_sound txnId env x expr body visibleDb delta hInfer with ⟨value, hEval, hBody⟩
  refine ⟨value, hEval, hBody, ?_⟩
  have hEval' : Expr.eval (instantiateExpr env [] expr) = some value := by
    simpa [evalInEnv] using hEval
  simpa [instantiateCommand] using
    (Semantics.LocalStep.letE
      (snapshot := visibleDb)
      (txnId := txnId)
      (x := x)
      (expr := instantiateExpr env [] expr)
      (body := instantiateCommand (env.erase x) body)
      (value := value)
      (localDb := localDb)
      hEval')

theorem localStep_ite_of_infer (txnId : TxnId) (env : Env) (cond : Expr)
    (thenBranch elseBranch : Semantics.Program)
    (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.ite cond thenBranch elseBranch : Semantics.Program)) visibleDb = some delta) :
    (evalInEnv env cond = some (.scalar (.bool true)) ∧
        inferEffect txnId env thenBranch visibleDb = some delta ∧
        Semantics.LocalStep
          visibleDb
          txnId
          (instantiateCommand (ι := IsolationSpec Database) env
            (.ite cond thenBranch elseBranch : Semantics.Program))
          localDb
          (instantiateCommand (ι := IsolationSpec Database) env thenBranch :
            Command (IsolationSpec Database) Database)
          localDb) ∨
      (evalInEnv env cond = some (.scalar (.bool false)) ∧
        inferEffect txnId env elseBranch visibleDb = some delta ∧
        Semantics.LocalStep
          visibleDb
          txnId
          (instantiateCommand (ι := IsolationSpec Database) env
            (.ite cond thenBranch elseBranch : Semantics.Program))
          localDb
          (instantiateCommand (ι := IsolationSpec Database) env elseBranch :
            Command (IsolationSpec Database) Database)
          localDb) := by
  rcases infer_ite_sound txnId env cond thenBranch elseBranch visibleDb delta hInfer with
    hThen | hElse
  · rcases hThen with ⟨hCond, hBranch⟩
    left
    refine ⟨hCond, hBranch, ?_⟩
    have hCond' : Expr.eval (instantiateExpr env [] cond) = some (.scalar (.bool true)) := by
      simpa [evalInEnv] using hCond
    simpa [instantiateCommand] using
      (Semantics.LocalStep.iteTrue
        (snapshot := visibleDb)
        (txnId := txnId)
        (condition := instantiateExpr env [] cond)
        (thenBranch := instantiateCommand env thenBranch)
        (elseBranch := instantiateCommand env elseBranch)
        (localDb := localDb)
        hCond')
  · rcases hElse with ⟨hCond, hBranch⟩
    right
    refine ⟨hCond, hBranch, ?_⟩
    have hCond' : Expr.eval (instantiateExpr env [] cond) = some (.scalar (.bool false)) := by
      simpa [evalInEnv] using hCond
    simpa [instantiateCommand] using
      (Semantics.LocalStep.iteFalse
        (snapshot := visibleDb)
        (txnId := txnId)
        (condition := instantiateExpr env [] cond)
        (thenBranch := instantiateCommand env thenBranch)
        (elseBranch := instantiateCommand env elseBranch)
        (localDb := localDb)
        hCond')

theorem localStep_delete_of_infer (txnId : TxnId) (env : Env) (source : VarName) (predicate : Expr)
    (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.delete source predicate : Semantics.Program)) visibleDb = some delta)
    (hDisjoint : Database.disjointIds localDb delta) :
    Semantics.LocalStep
      visibleDb
      txnId
      (instantiateCommand (ι := IsolationSpec Database) env (.delete source predicate : Semantics.Program))
      localDb
      (.skip : Command (IsolationSpec Database) Database)
      (localDb ++ delta) := by
  have hDelete := infer_delete_sound txnId env source predicate visibleDb delta hInfer
  simpa [instantiateCommand] using
    (Semantics.LocalStep.delete
      (snapshot := visibleDb)
      (txnId := txnId)
      (source := source)
      (predicate := instantiateExpr env [source] predicate)
      (localDb := localDb)
      (removed := delta)
      hDelete
      hDisjoint)

theorem localStep_update_of_infer (txnId : TxnId) (env : Env) (source : VarName)
    (updateExpr predicate : Expr) (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.update source updateExpr predicate : Semantics.Program)) visibleDb = some delta)
    (hDisjoint : Database.disjointIds localDb delta) :
    Semantics.LocalStep
      visibleDb
      txnId
      (instantiateCommand (ι := IsolationSpec Database) env (.update source updateExpr predicate : Semantics.Program))
      localDb
      (.skip : Command (IsolationSpec Database) Database)
      (localDb ++ delta) := by
  have hUpdate := infer_update_sound txnId env source updateExpr predicate visibleDb delta hInfer
  simpa [instantiateCommand] using
    (Semantics.LocalStep.update
      (snapshot := visibleDb)
      (txnId := txnId)
      (source := source)
      (updateExpr := instantiateExpr env [source] updateExpr)
      (predicate := instantiateExpr env [source] predicate)
      (localDb := localDb)
      (updated := delta)
      hUpdate
      hDisjoint)


end Transformer

end DbAppProgramLogic
