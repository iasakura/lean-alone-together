import DbAppProgramLogic.Transformer.Paper
import DbAppProgramLogic.Legacy.Transformer.Concrete

namespace DbAppProgramLogic

namespace Transformer

theorem paperInferenceSound_foreach (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (source : Expr) (doneVar elemVar : VarName) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      ∀ records,
        Expr.eval (instantiateSymExpr env [] source) = some (.set records) →
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body)
          (transformerPost Fctxt F)) :
    paperInferenceSound R txnId I Fctxt
      (.foreach (instantiateSymExpr env [] source) doneVar elemVar body) F := by
  refine Logic.localValid_foreach R txnId _ _ (instantiateSymExpr env [] source) doneVar elemVar body
    hStable ?_
  intro records hEval
  exact hBody records hEval

theorem inferEffect_foreachRuntime_eq (txnId : TxnId) (env : Env)
    (done remaining : Expr) (doneVar elemVar : VarName)
    (body : Semantics.Program) (db : Database) :
    inferEffect txnId env (.foreachRuntime done remaining doneVar elemVar body) db =
      (match done, remaining with
      | Expr.lit (.set doneRecords), Expr.lit (.set remainingRecords) =>
          inferForeach txnId env doneVar elemVar body doneRecords remainingRecords db
      | _, _ => none) := by
  rw [inferEffect.eq_def]
  cases done <;> cases remaining <;> simp
  case lit.lit doneLit remainingLit =>
    cases doneLit <;> cases remainingLit <;> simp

theorem inferEffect_foreachRuntime_setLit (txnId : TxnId) (env : Env)
    (done remaining : SetLit) (doneVar elemVar : VarName)
    (body : Semantics.Program) (db : Database) :
    inferEffect txnId env
      (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
      db =
      inferForeach txnId env doneVar elemVar body done remaining db := by
  rw [inferEffect_foreachRuntime_eq]
  simp [Expr.setLit]

theorem infer_foreachRuntime_nil_sound (txnId : TxnId) (env : Env) (done : SetLit)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db delta : Database)
    (h :
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body)
        db = some delta) :
    delta = [] := by
  have hEq : [] = delta := by
    simpa [inferEffect_foreachRuntime_setLit, inferForeach.eq_def] using h
  simpa using hEq.symm

theorem infer_foreachRuntime_cons_sound (txnId : TxnId) (env : Env) (done : SetLit)
    (current : RecordLit) (rest : SetLit) (doneVar elemVar : VarName)
    (body : Semantics.Program) (db delta : Database)
    (h :
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit (current :: rest)) doneVar elemVar body)
        db = some delta) :
    ∃ deltaCurrent deltaRest,
      inferEffect txnId (foreachEnv env doneVar elemVar done current) body db = some deltaCurrent ∧
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit (done ++ [current])) (Expr.setLit rest) doneVar elemVar body)
        db = some deltaRest ∧
      delta = deltaCurrent ++ deltaRest := by
  have hDoneEval : evalInEnv env (Expr.setLit done) = some (.set done) := by
    simp
  have hRemainingEval :
      evalInEnv env (Expr.setLit (current :: rest)) = some (.set (current :: rest)) := by
    simp
  cases hCurrent : inferEffect txnId (foreachEnv env doneVar elemVar done current) body db with
  | none =>
      rw [inferEffect_foreachRuntime_setLit] at h
      rw [inferForeach.eq_def] at h
      simp [hCurrent] at h
  | some deltaCurrent =>
      cases hRest :
          inferEffect txnId env
            (.foreachRuntime (Expr.setLit (done ++ [current])) (Expr.setLit rest) doneVar elemVar body)
            db with
      | none =>
          have hRest' :
              inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db = none := by
            simpa [inferEffect_foreachRuntime_setLit] using hRest
          rw [inferEffect_foreachRuntime_setLit] at h
          rw [inferForeach.eq_def] at h
          simp [hCurrent, hRest'] at h
      | some deltaRest =>
          have hRest' :
              inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                some deltaRest := by
            simpa [inferEffect_foreachRuntime_setLit] using hRest
          have hEqSome : some (deltaCurrent ++ deltaRest) = some delta := by
            rw [inferEffect_foreachRuntime_setLit] at h
            rw [inferForeach.eq_def] at h
            simpa [hCurrent, hRest'] using h
          have hEq : delta = deltaCurrent ++ deltaRest := by
            exact (Option.some.inj hEqSome).symm
          refine ⟨deltaCurrent, deltaRest, ?_, ?_, hEq⟩
          · rfl
          · rfl

theorem infer_foreach_sound (txnId : TxnId) (env : Env) (source : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db delta : Database)
    (h : inferEffect txnId env (.foreach source doneVar elemVar body) db = some delta) :
    ∃ records,
      evalInEnv env source = some (.set records) ∧
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body)
        db = some delta := by
  cases hEval : evalInEnv env source with
  | none =>
      have : False := by
        simp [inferEffect, hEval] at h
      exact False.elim this
  | some value =>
      cases value with
      | scalar s =>
          have : False := by
            simp [inferEffect, hEval] at h
          exact False.elim this
      | record record =>
          have : False := by
            simp [inferEffect, hEval] at h
          exact False.elim this
      | set records =>
          have hRuntime : inferForeach txnId env doneVar elemVar body [] records db = some delta := by
            simpa [inferEffect, hEval] using h
          refine ⟨records, ?_⟩
          constructor
          · rfl
          · simpa [inferEffect_foreachRuntime_setLit] using hRuntime

theorem infer_foreachRuntime_sound (txnId : TxnId) (env : Env) (done remaining : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db delta : Database)
    (h : inferEffect txnId env (.foreachRuntime done remaining doneVar elemVar body) db = some delta) :
    ∃ doneRecords remainingRecords,
      evalInEnv env done = some (.set doneRecords) ∧
      evalInEnv env remaining = some (.set remainingRecords) ∧
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit doneRecords) (Expr.setLit remainingRecords) doneVar elemVar body)
        db = some delta := by
  cases done <;> cases remaining <;> simp [inferEffect_foreachRuntime_eq, Expr.setLit] at h
  case lit.lit doneLit remainingLit =>
    cases doneLit <;> cases remainingLit <;> simp [inferEffect_foreachRuntime_eq, Expr.setLit] at h
    case set.set doneRecords remainingRecords =>
      refine ⟨doneRecords, remainingRecords, ?_, ?_, ?_⟩
      · simp [evalInEnv, Expr.eval, Literal.toValue, Expr.setLit]
      · simp [evalInEnv, Expr.eval, Literal.toValue, Expr.setLit]
      · simpa [inferEffect_foreachRuntime_setLit] using h


theorem inferenceSoundEnv_foreachRuntime_lit (txnId : TxnId) (env : Env)
    (done : SetLit) (remaining : SetLit) (doneVar elemVar : VarName)
    (body : Semantics.Program)
    (hBody :
      ∀ done current,
        inferenceSoundEnv txnId (foreachEnv env doneVar elemVar done current) body
          (inferEffect txnId (foreachEnv env doneVar elemVar done current) body)) :
    inferenceSoundEnv txnId env
      (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
      (inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)) := by
  induction remaining generalizing done with
  | nil =>
      intro visibleDb localDb' hInfer
      have hNil : localDb' = [] := by
        exact infer_foreachRuntime_nil_sound txnId env done doneVar elemVar body visibleDb localDb' hInfer
      subst hNil
      simpa [inferenceSoundEnv, instantiateCommand] using
        (_root_.DbAppProgramLogic.Logic.localValid_foreachDone_false
        (ι := IsolationSpec Database)
        (txnId := txnId)
        (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
        (Q := fun localDb visible => localDb = [] ∧ visible = visibleDb)
        (done := done)
        (doneVar := doneVar)
        (elemVar := elemVar)
        (body := instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)
        (by
          intro localDb visibleDb' hPre
          exact hPre))
  | cons current rest ih =>
      intro visibleDb localDb' hInfer
      rcases infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body visibleDb localDb' hInfer with
        ⟨deltaCurrent, deltaRest, hCurrentInfer, hRestInfer, hDelta⟩
      have hBodyValid' := hBody done current visibleDb deltaCurrent hCurrentInfer
      have hBodyValid :
          Logic.LocalValid (fun _ _ _ => False) txnId
            (fun localDb visible => localDb = [] ∧ visible = visibleDb)
            (Command.subst doneVar (Expr.setLit done)
              (Command.subst elemVar (.lit (.record current))
                (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)) :
                  Command (IsolationSpec Database) Database)
            (fun localDb visible => localDb = deltaCurrent ∧ visible = visibleDb) := by
        have hInst := instantiateCommand_foreachEnv env doneVar elemVar done current body
        simpa [hInst] using hBodyValid'
      have hRestValidBase :
          Logic.LocalValid (fun _ _ _ => False) txnId
            (fun localDb visible => localDb = [] ∧ visible = visibleDb)
            (.foreachRuntime
              (Expr.setLit (done ++ [current]))
              (Expr.setLit rest)
              doneVar
              elemVar
              (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
                Command (IsolationSpec Database) Database)
            (fun localDb visible => localDb = deltaRest ∧ visible = visibleDb) := by
        simpa [inferenceSoundEnv, instantiateCommand] using
          (ih (done ++ [current]) visibleDb deltaRest hRestInfer)
      have hRestValid :
          Logic.LocalValid (fun _ _ _ => False) txnId
            (fun localDb visible => localDb = deltaCurrent ∧ visible = visibleDb)
            (.foreachRuntime
              (Expr.setLit (done ++ [current]))
              (Expr.setLit rest)
              doneVar
              elemVar
              (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
                Command (IsolationSpec Database) Database)
            (fun localDb visible => localDb = deltaCurrent ++ deltaRest ∧ visible = visibleDb) := by
        exact _root_.DbAppProgramLogic.Logic.localValid_prepend_false
          (ι := IsolationSpec Database)
          txnId
          deltaCurrent
          visibleDb
          deltaRest
          (.foreachRuntime
            (Expr.setLit (done ++ [current]))
            (Expr.setLit rest)
            doneVar
            elemVar
            (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
              Command (IsolationSpec Database) Database)
          hRestValidBase
      have hSeqValid :
          Logic.LocalValid (fun _ _ _ => False) txnId
            (fun localDb visible => localDb = [] ∧ visible = visibleDb)
            (.seq
              (Command.subst doneVar (Expr.setLit done)
                (Command.subst elemVar (.lit (.record current))
                  (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)))
              (.foreachRuntime
                (Expr.setLit (done ++ [current]))
                (Expr.setLit rest)
                doneVar
                elemVar
                (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)) :
                  Command (IsolationSpec Database) Database)
            (fun localDb visible => localDb = deltaCurrent ++ deltaRest ∧ visible = visibleDb) := by
        exact _root_.DbAppProgramLogic.Logic.localValid_seq_false
          (ι := IsolationSpec Database)
          (txnId := txnId)
          (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
          (P' := fun localDb visible => localDb = deltaCurrent ∧ visible = visibleDb)
          (Q := fun localDb visible => localDb = deltaCurrent ++ deltaRest ∧ visible = visibleDb)
          (left :=
            Command.subst doneVar (Expr.setLit done)
              (Command.subst elemVar (.lit (.record current))
                (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)))
          (right :=
            (.foreachRuntime
              (Expr.setLit (done ++ [current]))
              (Expr.setLit rest)
              doneVar
              elemVar
              (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
                Command (IsolationSpec Database) Database))
          hBodyValid
          hRestValid
      simpa [inferenceSoundEnv, instantiateCommand, hDelta] using
        (_root_.DbAppProgramLogic.Logic.localValid_foreachNext_false
          (ι := IsolationSpec Database)
          (txnId := txnId)
          (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
          (Q := fun localDb visible => localDb = deltaCurrent ++ deltaRest ∧ visible = visibleDb)
          (done := done)
          (current := current)
          (rest := rest)
          (doneVar := doneVar)
          (elemVar := elemVar)
          (body := instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)
          hSeqValid)

theorem inferenceSoundEnv_foreach (txnId : TxnId) (env : Env) (source : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program)
    (hBody :
      ∀ done current,
        inferenceSoundEnv txnId (foreachEnv env doneVar elemVar done current) body
          (inferEffect txnId (foreachEnv env doneVar elemVar done current) body)) :
    inferenceSoundEnv txnId env (.foreach source doneVar elemVar body)
      (inferEffect txnId env (.foreach source doneVar elemVar body)) := by
  intro visibleDb localDb' hInfer
  rcases infer_foreach_sound txnId env source doneVar elemVar body visibleDb localDb' hInfer with
    ⟨records, hEval, hRuntimeInfer⟩
  have hRuntimeValid :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ visible = visibleDb)
        (.foreachRuntime
          (Expr.setLit [])
          (Expr.setLit records)
          doneVar
          elemVar
          (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
            Command (IsolationSpec Database) Database)
        (fun localDb visible => localDb = localDb' ∧ visible = visibleDb) := by
    simpa [inferenceSoundEnv, instantiateCommand] using
      (inferenceSoundEnv_foreachRuntime_lit txnId env [] records doneVar elemVar body hBody
        visibleDb localDb' hRuntimeInfer)
  have hEval' : Expr.eval (instantiateExpr env [] source) = some (.set records) := by
    simpa [evalInEnv] using hEval
  simpa [inferenceSoundEnv, instantiateCommand] using
    (_root_.DbAppProgramLogic.Logic.localValid_foreachStart_false
      (ι := IsolationSpec Database)
      (txnId := txnId)
      (P := fun localDb visible => localDb = [] ∧ visible = visibleDb)
      (Q := fun localDb visible => localDb = localDb' ∧ visible = visibleDb)
      (source := instantiateExpr env [] source)
      (records := records)
      (doneVar := doneVar)
      (elemVar := elemVar)
      (body := instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body)
      hEval'
      hRuntimeValid)

theorem inferenceSound_foreach (txnId : TxnId) (source : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program)
    (hBody :
      ∀ done current,
        inferenceSoundEnv txnId (foreachEnv [] doneVar elemVar done current) body
          (inferEffect txnId (foreachEnv [] doneVar elemVar done current) body)) :
    inferenceSound txnId (.foreach source doneVar elemVar body)
      (inferEffect txnId [] (.foreach source doneVar elemVar body)) := by
  exact inferenceSound_of_env_empty txnId (.foreach source doneVar elemVar body)
    (inferEffect txnId [] (.foreach source doneVar elemVar body))
    (inferenceSoundEnv_foreach txnId [] source doneVar elemVar body hBody)

theorem inferenceSoundEnv_foreachRuntime (txnId : TxnId) (env : Env)
    (done remaining : Expr) (doneVar elemVar : VarName) (body : Semantics.Program)
    (hBody :
      ∀ done current,
        inferenceSoundEnv txnId (foreachEnv env doneVar elemVar done current) body
          (inferEffect txnId (foreachEnv env doneVar elemVar done current) body)) :
  inferenceSoundEnv txnId env (.foreachRuntime done remaining doneVar elemVar body)
      (inferEffect txnId env (.foreachRuntime done remaining doneVar elemVar body)) := by
  intro visibleDb localDb' hInfer
  cases done <;> cases remaining <;> simp [inferEffect_foreachRuntime_eq, Expr.setLit] at hInfer
  case lit.lit doneLit remainingLit =>
    cases doneLit <;> cases remainingLit <;> simp [inferEffect_foreachRuntime_eq, Expr.setLit] at hInfer
    case set.set doneRecords remainingRecords =>
      have hInferLit :
          inferEffect txnId env
            (.foreachRuntime (Expr.setLit doneRecords) (Expr.setLit remainingRecords)
              doneVar elemVar body)
            visibleDb = some localDb' := by
        simpa [inferEffect_foreachRuntime_setLit] using hInfer
      have hValidLit :=
        inferenceSoundEnv_foreachRuntime_lit txnId env doneRecords remainingRecords
          doneVar elemVar body hBody visibleDb localDb' hInferLit
      simpa [inferenceSoundEnv, instantiateCommand] using hValidLit


theorem localStep_foreach_of_infer (txnId : TxnId) (env : Env) (source : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program) (visibleDb localDb delta : Database)
    (hInfer : inferEffect txnId env ((.foreach source doneVar elemVar body : Semantics.Program)) visibleDb = some delta) :
    ∃ records,
      evalInEnv env source = some (.set records) ∧
      Semantics.LocalStep
        visibleDb
        txnId
        (instantiateCommand (ι := IsolationSpec Database) env
          (.foreach source doneVar elemVar body : Semantics.Program))
        localDb
        (.foreachRuntime
          (Expr.setLit [])
          (Expr.setLit records)
          doneVar
          elemVar
          (instantiateCommand (ι := IsolationSpec Database) ((env.erase doneVar).erase elemVar) body) :
            Command (IsolationSpec Database) Database)
        localDb := by
  cases hEval : evalInEnv env source with
  | none =>
      have : False := by
        simp [inferEffect, hEval] at hInfer
      exact False.elim this
  | some value =>
      cases value with
      | scalar s =>
          have : False := by
            simp [inferEffect, hEval] at hInfer
          exact False.elim this
      | record record =>
          have : False := by
            simp [inferEffect, hEval] at hInfer
          exact False.elim this
      | set records =>
          have hEvalSet : evalInEnv env source = some (.set records) := by
            simpa using hEval
          refine ⟨records, rfl, ?_⟩
          have hEval' : Expr.eval (instantiateExpr env [] source) = some (.set records) := by
            simpa [evalInEnv] using hEvalSet
          simpa [instantiateCommand] using
            (Semantics.LocalStep.foreachStart
              (snapshot := visibleDb)
              (txnId := txnId)
              (source := instantiateExpr env [] source)
              (doneVar := doneVar)
              (elemVar := elemVar)
              (body := instantiateCommand ((env.erase doneVar).erase elemVar) body)
              (localDb := localDb)
              (records := records)
              hEval')

end Transformer

end DbAppProgramLogic
