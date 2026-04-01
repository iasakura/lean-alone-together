import DbAppProgramLogic.Logic

namespace DbAppProgramLogic

abbrev Env := List (VarName × Value)
abbrev TxnEffect := Database → Option Database

namespace Env

def lookup? (env : Env) (x : VarName) : Option Value :=
  match env with
  | [] => none
  | (y, v) :: rest => if x = y then some v else lookup? rest x

def erase (env : Env) (x : VarName) : Env :=
  env.filter (fun binding => binding.1 ≠ x)

def insert (env : Env) (x : VarName) (v : Value) : Env :=
  (x, v) :: env.erase x

theorem erase_comm (env : Env) (x y : VarName) :
    (env.erase x).erase y = (env.erase y).erase x := by
  unfold erase
  rw [List.filter_filter, List.filter_filter]
  congr
  funext binding
  simp [Bool.and_comm]

theorem erase_idem (env : Env) (x : VarName) :
    (env.erase x).erase x = env.erase x := by
  unfold erase
  rw [List.filter_filter]
  congr
  funext binding
  simp

theorem erase_insert_same (env : Env) (x : VarName) (v : Value) :
    (env.insert x v).erase x = env.erase x := by
  simp [insert, erase]

theorem erase_insert_ne (env : Env) (x y : VarName) (v : Value) (hxy : x ≠ y) :
    (env.insert x v).erase y = (env.erase y).insert x v := by
  unfold erase
  simp [insert, hxy]
  simpa [erase] using erase_comm env x y

end Env

namespace Transformer

def instantiateExpr (env : Env) (blocked : List VarName) (expr : Expr) : Expr :=
  env.foldr
    (fun (binding : VarName × Value) acc =>
      if binding.1 ∈ blocked then
        acc
      else
        Expr.subst binding.1 binding.2.toExpr acc)
    expr

def instantiateCommand (env : Env) : Command ι Database → Command ι Database
  | .skip => .skip
  | .letE x expr body =>
      .letE x (instantiateExpr env [] expr) (instantiateCommand (env.erase x) body)
  | .ite cond thenBranch elseBranch =>
      .ite
        (instantiateExpr env [] cond)
        (instantiateCommand env thenBranch)
        (instantiateCommand env elseBranch)
  | .seq left right =>
      .seq (instantiateCommand env left) (instantiateCommand env right)
  | .insert expr =>
      .insert (instantiateExpr env [] expr)
  | .delete source predicate =>
      .delete source (instantiateExpr env [source] predicate)
  | .select binder source predicate body =>
      .select
        binder
        source
        (instantiateExpr env [source] predicate)
        (instantiateCommand (env.erase binder) body)
  | .update source updateExpr predicate =>
      .update
        source
        (instantiateExpr env [source] updateExpr)
        (instantiateExpr env [source] predicate)
  | .foreach source doneVar elemVar body =>
      .foreach
        (instantiateExpr env [] source)
        doneVar
        elemVar
        (instantiateCommand ((env.erase doneVar).erase elemVar) body)
  | .foreachRuntime done remaining doneVar elemVar body =>
      .foreachRuntime
        (instantiateExpr env [] done)
        (instantiateExpr env [] remaining)
        doneVar
        elemVar
        (instantiateCommand ((env.erase doneVar).erase elemVar) body)
  | .txn txnId isolation body =>
      .txn txnId isolation (instantiateCommand env body)
  | .txnRuntime txnId isolation localDb snapshot body =>
      .txnRuntime txnId isolation localDb snapshot (instantiateCommand env body)
  | .par left right =>
      .par (instantiateCommand env left) (instantiateCommand env right)

def evalInEnv (env : Env) (expr : Expr) : Option Value :=
  Expr.eval (instantiateExpr env [] expr)

def foreachEnv (env : Env) (doneVar elemVar : VarName) (done : SetLit) (current : RecordLit) : Env :=
  if _ : doneVar = elemVar then
    env.insert elemVar (.record current)
  else
    (env.insert elemVar (.record current)).insert doneVar (.set done)

def emptyEffect : TxnEffect :=
  fun _ => some []

def unionEffect (left right : TxnEffect) : TxnEffect :=
  fun db => do
    let delta₁ ← left db
    let delta₂ ← right db
    pure (delta₁ ++ delta₂)

mutual

  private def inferForeach (txnId : TxnId) (env : Env)
      (doneVar elemVar : VarName) (body : Semantics.Program)
      (done remaining : SetLit) : TxnEffect
    | db => do
        match remaining with
        | [] => some []
        | current :: rest =>
            let env' := foreachEnv env doneVar elemVar done current
            let deltaCurrent ← inferEffect txnId env' body db
            let deltaRest ← inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db
            pure (deltaCurrent ++ deltaRest)

  def inferEffect (txnId : TxnId) (env : Env) : Semantics.Program → TxnEffect
    | .skip => emptyEffect
    | .letE x expr body =>
        fun db => do
          let value ← evalInEnv env expr
          inferEffect txnId (env.insert x value) body db
    | .ite cond thenBranch elseBranch =>
        fun db => do
          let .scalar (.bool b) ← evalInEnv env cond | none
          if b then inferEffect txnId env thenBranch db else inferEffect txnId env elseBranch db
    | .seq left right =>
        unionEffect (inferEffect txnId env left) (inferEffect txnId env right)
    | .insert expr =>
        fun _ => do
          let .record record ← evalInEnv env expr | none
          pure [Row.fromInsert txnId record]
    | .delete source predicate =>
        fun db =>
          Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate)
    | .select binder source predicate body =>
        fun db => do
          let selected ← Semantics.collectSelected db source (instantiateExpr env [source] predicate)
          inferEffect txnId (env.insert binder (.set selected)) body db
    | .update source updateExpr predicate =>
        fun db =>
          Semantics.collectUpdated
            db
            txnId
            source
            (instantiateExpr env [source] updateExpr)
            (instantiateExpr env [source] predicate)
    | .foreach source doneVar elemVar body =>
        fun db => do
          let .set records ← evalInEnv env source | none
          inferForeach txnId env doneVar elemVar body [] records db
    | .foreachRuntime done remaining doneVar elemVar body =>
        fun db => do
          let .set doneRecords ← evalInEnv env done | none
          let .set remainingRecords ← evalInEnv env remaining | none
          inferForeach txnId env doneVar elemVar body doneRecords remainingRecords db
    | .txn .. => fun _ => none
    | .txnRuntime .. => fun _ => none
    | .par .. => fun _ => none

end

def effectStable (R : LocalRely) (F : TxnEffect) : Prop :=
  ∀ localDb visibleDb visibleDb', R localDb visibleDb visibleDb' → F visibleDb = F visibleDb'

def guaranteeValid (G : Guarantee) (F : TxnEffect) : Prop :=
  ∀ visibleDb localDb, F visibleDb = some localDb → G visibleDb (Database.flush localDb visibleDb)

def inferenceSoundEnv (txnId : TxnId) (env : Env) (body : Semantics.Program) (F : TxnEffect) : Prop :=
  ∀ visibleDb localDb',
    F visibleDb = some localDb' →
    Logic.LocalValid (fun _ _ _ => False) txnId
      (fun localDb visible => localDb = [] ∧ visible = visibleDb)
      (instantiateCommand (ι := IsolationSpec Database) env body)
      (fun localDb visible => localDb = localDb' ∧ visible = visibleDb)

def inferenceSound (txnId : TxnId) (body : Semantics.Program) (F : TxnEffect) : Prop :=
  ∀ visibleDb localDb',
    F visibleDb = some localDb' →
    Logic.LocalValid (fun _ _ _ => False) txnId (fun localDb visible => localDb = [] ∧ visible = visibleDb) body
      (fun localDb visible => localDb = localDb' ∧ visible = visibleDb)

structure TransactionVCG where
  effect : TxnEffect
  execStable : Prop
  commitStable : Prop
  guaranteeOk : Prop
  preservesInvariant : Prop

def vcg (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program) : TransactionVCG :=
  let effect := inferEffect txnId [] body
  { effect := effect
    execStable := effectStable (Logic.relyMod R isolation.exec) effect
    commitStable := effectStable (Logic.relyMod R isolation.commit) effect
    guaranteeOk := guaranteeValid G effect
    preservesInvariant := ∀ db db', I db → G db db' → I db' }

def vcgForTxn (R : Rely) (I : Assertion) (G : Guarantee) : Semantics.Program → Option TransactionVCG
  | .txn txnId isolation body => some (vcg R I G txnId isolation body)
  | _ => none

def effectPost (I : Assertion) (F : TxnEffect) : BiAssertion :=
  fun localDb visibleDb => F visibleDb = some localDb ∧ I visibleDb

def effectDefinedOn (I : Assertion) (F : TxnEffect) : Prop :=
  ∀ visibleDb, I visibleDb → ∃ localDb, F visibleDb = some localDb

theorem instantiateExpr_nil (blocked : List VarName) (expr : Expr) :
    instantiateExpr [] blocked expr = expr := by
  simp [instantiateExpr]

theorem instantiateCommand_nil (cmd : Command ι Database) :
    instantiateCommand [] cmd = cmd := by
  induction cmd <;> simp [instantiateCommand, instantiateExpr_nil, Env.erase, *]

@[simp] theorem instantiateExpr_lit (env : Env) (blocked : List VarName) (lit : Literal) :
    instantiateExpr env blocked (.lit lit) = .lit lit := by
  induction env with
  | nil =>
      simp [instantiateExpr]
  | cons binding rest ih =>
      by_cases hmem : binding.fst ∈ blocked
      · simp [instantiateExpr, hmem, Expr.subst] at ih ⊢
        exact ih
      · simp [instantiateExpr, hmem, Expr.subst] at ih ⊢
        simp [ih, Expr.subst]

@[simp] theorem instantiateExpr_setLit (env : Env) (blocked : List VarName) (records : SetLit) :
    instantiateExpr env blocked (Expr.setLit records) = Expr.setLit records :=
  instantiateExpr_lit env blocked (.set records)

@[simp] theorem evalInEnv_lit (env : Env) (lit : Literal) :
    evalInEnv env (.lit lit) = some lit.toValue := by
  cases lit <;> simp [evalInEnv, Expr.eval, Literal.toValue]

@[simp] theorem evalInEnv_setLit (env : Env) (records : SetLit) :
    evalInEnv env (Expr.setLit records) = some (.set records) :=
  evalInEnv_lit env (.set records)

theorem instantiateExpr_insert (env : Env) (x : VarName) (value : Value)
    (blocked : List VarName) (expr : Expr) :
    instantiateExpr (env.insert x value) blocked expr =
      if x ∈ blocked then
        instantiateExpr (env.erase x) blocked expr
      else
        Expr.subst x value.toExpr (instantiateExpr (env.erase x) blocked expr) := by
  simp [instantiateExpr, Env.insert]

theorem evalInEnv_nil (expr : Expr) :
    evalInEnv [] expr = Expr.eval expr := by
  simp [evalInEnv, instantiateExpr_nil]

theorem instantiateCommand_insert (env : Env) (x : VarName) (value : Value)
    (cmd : Command (IsolationSpec Database) Database) :
    instantiateCommand (env.insert x value) cmd =
      Command.subst x value.toExpr (instantiateCommand (env.erase x) cmd) := by
  induction cmd generalizing env with
  | skip =>
      simp [instantiateCommand, Command.subst]
  | letE y expr body ih =>
      by_cases hxy : x = y
      · subst hxy
        simp [instantiateCommand, Command.subst, instantiateExpr_insert,
          Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
      · have hErase : (env.insert x value).erase y = (env.erase y).insert x value := by
          simpa using Env.erase_insert_ne env x y value hxy
        simp [instantiateCommand, Command.subst, instantiateExpr_insert,
          hxy, hErase, ih, Env.erase_comm]
  | ite cond thenBranch elseBranch ihThen ihElse =>
      simp [instantiateCommand, Command.subst, instantiateExpr_insert, ihThen, ihElse]
  | seq left right ihLeft ihRight =>
      simp [instantiateCommand, Command.subst, ihLeft, ihRight]
  | insert expr =>
      simp [instantiateCommand, Command.subst, instantiateExpr_insert]
  | delete source predicate =>
      by_cases hxs : x = source
      · subst hxs
        simp [instantiateCommand, Command.subst, instantiateExpr_insert]
      · simp [instantiateCommand, Command.subst, instantiateExpr_insert, hxs]
  | select binder source predicate body ih =>
      by_cases hxb : x = binder
      · subst hxb
        simp [instantiateCommand, Command.subst, instantiateExpr_insert,
          Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
      · have hErase : (env.insert x value).erase binder = (env.erase binder).insert x value := by
          simpa using Env.erase_insert_ne env x binder value hxb
        by_cases hxs : x = source
        · subst hxs
          have ih' := ih (env.erase binder)
          simpa [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxb, hErase, Env.erase_comm, Env.erase_idem] using ih'
        · simp [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxb, hxs, hErase, ih, Env.erase_comm]
  | update source updateExpr predicate =>
      by_cases hxs : x = source
      · subst hxs
        simp [instantiateCommand, Command.subst, instantiateExpr_insert]
      · simp [instantiateCommand, Command.subst, instantiateExpr_insert, hxs]
  | foreach source doneVar elemVar body ih =>
      by_cases hxd : x = doneVar
      · subst hxd
        simp [instantiateCommand, Command.subst, instantiateExpr_insert,
          Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
      · by_cases hxe : x = elemVar
        · subst hxe
          simp [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxd, Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
        · have hEraseDone :
            (env.insert x value).erase doneVar = (env.erase doneVar).insert x value := by
            simpa using Env.erase_insert_ne env x doneVar value hxd
          have hEraseElem :
            ((env.erase doneVar).insert x value).erase elemVar =
              (((env.erase doneVar).erase elemVar).insert x value) := by
            simpa [Env.erase_comm] using Env.erase_insert_ne (env.erase doneVar) x elemVar value hxe
          simp [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxd, hxe, hEraseDone, hEraseElem, ih, Env.erase_comm]
  | foreachRuntime done remaining doneVar elemVar body ih =>
      by_cases hxd : x = doneVar
      · subst hxd
        simp [instantiateCommand, Command.subst, instantiateExpr_insert,
          Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
      · by_cases hxe : x = elemVar
        · subst hxe
          simp [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxd, Env.erase_insert_same, Env.erase_comm, Env.erase_idem]
        · have hEraseDone :
            (env.insert x value).erase doneVar = (env.erase doneVar).insert x value := by
            simpa using Env.erase_insert_ne env x doneVar value hxd
          have hEraseElem :
            ((env.erase doneVar).insert x value).erase elemVar =
              (((env.erase doneVar).erase elemVar).insert x value) := by
            simpa [Env.erase_comm] using Env.erase_insert_ne (env.erase doneVar) x elemVar value hxe
          simp [instantiateCommand, Command.subst, instantiateExpr_insert,
            hxd, hxe, hEraseDone, hEraseElem, ih, Env.erase_comm]
  | txn txnId isolation body ih =>
      simp [instantiateCommand, Command.subst, ih]
  | txnRuntime txnId isolation localDb snapshot body ih =>
      simp [instantiateCommand, Command.subst, ih]
  | par left right ihLeft ihRight =>
      simp [instantiateCommand, Command.subst, ihLeft, ihRight]

theorem instantiateCommand_foreachEnv (env : Env) (doneVar elemVar : VarName)
    (done : SetLit) (current : RecordLit) (cmd : Command (IsolationSpec Database) Database) :
    instantiateCommand (foreachEnv env doneVar elemVar done current) cmd =
      Command.subst doneVar (Expr.setLit done)
        (Command.subst elemVar (.lit (.record current))
          (instantiateCommand (((env.erase doneVar).erase elemVar)) cmd)) := by
  by_cases hEq : doneVar = elemVar
  · subst hEq
    simp [foreachEnv, instantiateCommand_insert, Env.erase_idem, Command.subst,
      Command.subst_shadow_lit, Value.toExpr, Expr.setLit]
  · have hErase :
        ((env.insert elemVar (.record current)).erase doneVar) =
          ((env.erase doneVar).insert elemVar (.record current)) := by
      have hNe : elemVar ≠ doneVar := by
        intro h'
        exact hEq h'.symm
      simpa using Env.erase_insert_ne env elemVar doneVar (.record current) hNe
    simp [foreachEnv, hEq, instantiateCommand_insert, hErase, Env.erase_comm, Command.subst, Value.toExpr, Expr.setLit]

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

theorem infer_foreachRuntime_nil_sound (txnId : TxnId) (env : Env) (done : SetLit)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db delta : Database)
    (h :
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body)
        db = some delta) :
    delta = [] := by
  have hEq : [] = delta := by
    simpa [inferEffect, inferForeach] using h
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
      simp [inferEffect, inferForeach, hDoneEval, hRemainingEval, hCurrent] at h
  | some deltaCurrent =>
      cases hRest :
          inferEffect txnId env
            (.foreachRuntime (Expr.setLit (done ++ [current])) (Expr.setLit rest) doneVar elemVar body)
            db with
      | none =>
          have hRest' :
              inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db = none := by
            simpa [inferEffect, inferForeach] using hRest
          simp [inferEffect, inferForeach, hDoneEval, hRemainingEval, hCurrent, hRest'] at h
      | some deltaRest =>
          have hRest' :
              inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                some deltaRest := by
            simpa [inferEffect, inferForeach] using hRest
          have hEqSome : some (deltaCurrent ++ deltaRest) = some delta := by
            simpa [inferEffect, inferForeach, hDoneEval, hRemainingEval, hCurrent, hRest'] using h
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
          · simpa [inferEffect, inferForeach] using hRuntime

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

theorem expr_eq_setLit_of_eval {expr : Expr} {records : SetLit}
    (h : Expr.eval expr = some (.set records)) :
    expr = Expr.setLit records := by
  cases expr with
  | lit lit =>
      cases lit with
      | scalar s =>
          simp [Expr.eval, Expr.setLit, Literal.toValue] at h
      | record record =>
          simp [Expr.eval, Expr.setLit, Literal.toValue] at h
      | set records' =>
          have hEq : records' = records := by
            simpa [Expr.eval, Expr.setLit, Literal.toValue] using h
          subst hEq
          rfl
  | var x =>
      simp [Expr.eval] at h
  | proj expr field =>
      simp [Expr.eval, Option.bind_eq_some_iff] at h
      rcases h with ⟨value, hExpr, hProj⟩
      cases value with
      | scalar s =>
          simp at hProj
      | set s =>
          simp at hProj
      | record record =>
          simp [Option.bind_eq_some_iff] at hProj
  | record fields =>
      simp [Expr.eval, Option.bind_eq_some_iff] at h
  | withUpdates base updates =>
      simp [Expr.eval, Option.bind_eq_some_iff] at h
      rcases h with ⟨baseValue, hBase, hUpdates⟩
      cases baseValue with
      | scalar s =>
          simp at hUpdates
      | set s =>
          simp at hUpdates
      | record record =>
          simp [Option.bind_eq_some_iff] at hUpdates
  | binop op lhs rhs =>
      simp [Expr.eval, Option.bind_eq_some_iff] at h
      rcases h with ⟨lhsValue, hLhs, hRhs⟩
      rcases hRhs with ⟨rhsValue, hEvalRhs, hValue⟩
      cases op <;> cases lhsValue <;> cases rhsValue
      all_goals
        first
        | simp at hValue
        | cases ‹ScalarLit› <;> cases ‹ScalarLit› <;> simp at hValue

theorem inferenceSoundEnv_foreachRuntime (txnId : TxnId) (env : Env)
    (done remaining : Expr) (doneVar elemVar : VarName) (body : Semantics.Program)
    (hBody :
      ∀ done current,
        inferenceSoundEnv txnId (foreachEnv env doneVar elemVar done current) body
          (inferEffect txnId (foreachEnv env doneVar elemVar done current) body)) :
    inferenceSoundEnv txnId env (.foreachRuntime done remaining doneVar elemVar body)
      (inferEffect txnId env (.foreachRuntime done remaining doneVar elemVar body)) := by
  intro visibleDb localDb' hInfer
  cases hDone : evalInEnv env done with
  | none =>
      have : False := by
        simp [inferEffect, hDone] at hInfer
      exact False.elim this
  | some doneValue =>
      cases doneValue with
      | scalar s =>
          have : False := by
            simp [inferEffect, hDone] at hInfer
          exact False.elim this
      | record record =>
          have : False := by
            simp [inferEffect, hDone] at hInfer
          exact False.elim this
      | set doneRecords =>
          cases hRemaining : evalInEnv env remaining with
          | none =>
              have : False := by
                simp [inferEffect, hDone, hRemaining] at hInfer
              exact False.elim this
          | some remainingValue =>
              cases remainingValue with
              | scalar s =>
                  have : False := by
                    simp [inferEffect, hDone, hRemaining] at hInfer
                  exact False.elim this
              | record record =>
                  have : False := by
                    simp [inferEffect, hDone, hRemaining] at hInfer
                  exact False.elim this
              | set remainingRecords =>
                  have hDoneExpr :
                      instantiateExpr env [] done = Expr.setLit doneRecords := by
                    apply expr_eq_setLit_of_eval
                    simpa [evalInEnv] using hDone
                  have hRemainingExpr :
                      instantiateExpr env [] remaining = Expr.setLit remainingRecords := by
                    apply expr_eq_setLit_of_eval
                    simpa [evalInEnv] using hRemaining
                  have hInferLit :
                      inferEffect txnId env
                        (.foreachRuntime (Expr.setLit doneRecords) (Expr.setLit remainingRecords)
                          doneVar elemVar body)
                        visibleDb = some localDb' := by
                    simpa [inferEffect, hDone, hRemaining] using hInfer
                  have hValidLit :=
                    inferenceSoundEnv_foreachRuntime_lit txnId env doneRecords remainingRecords
                      doneVar elemVar body hBody visibleDb localDb' hInferLit
                  simpa [inferenceSoundEnv, instantiateCommand, hDoneExpr, hRemainingExpr] using hValidLit

theorem inferenceSoundEnv_all (txnId : TxnId) :
    ∀ env body, inferenceSoundEnv txnId env body (inferEffect txnId env body)
  | env, .skip =>
      inferenceSoundEnv_skip txnId env
  | env, .letE x expr body =>
      inferenceSoundEnv_let txnId env x expr body
        (fun value _ => inferenceSoundEnv_all txnId (env.insert x value) body)
  | env, .ite cond thenBranch elseBranch =>
      inferenceSoundEnv_ite txnId env cond thenBranch elseBranch
        (inferenceSoundEnv_all txnId env thenBranch)
        (inferenceSoundEnv_all txnId env elseBranch)
  | env, .seq left right =>
      inferenceSoundEnv_seq txnId env left right
        (inferenceSoundEnv_all txnId env left)
        (inferenceSoundEnv_all txnId env right)
  | env, .insert expr =>
      inferenceSoundEnv_insert txnId env expr
  | env, .delete source predicate =>
      inferenceSoundEnv_delete txnId env source predicate
  | env, .select binder source predicate body =>
      inferenceSoundEnv_select txnId env binder source predicate body
        (fun selected => inferenceSoundEnv_all txnId (env.insert binder (.set selected)) body)
  | env, .update source updateExpr predicate =>
      inferenceSoundEnv_update txnId env source updateExpr predicate
  | env, .foreach source doneVar elemVar body =>
      inferenceSoundEnv_foreach txnId env source doneVar elemVar body
        (fun done current => inferenceSoundEnv_all txnId (foreachEnv env doneVar elemVar done current) body)
  | env, .foreachRuntime done remaining doneVar elemVar body =>
      inferenceSoundEnv_foreachRuntime txnId env done remaining doneVar elemVar body
        (fun done current => inferenceSoundEnv_all txnId (foreachEnv env doneVar elemVar done current) body)
  | env, .txn innerTxnId isolation body => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer
  | env, .txnRuntime innerTxnId isolation localDb snapshot body => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer
  | env, .par left right => by
      intro visibleDb localDb' hInfer
      simp [inferEffect] at hInfer

theorem inferenceSound_all (txnId : TxnId) (body : Semantics.Program) :
    inferenceSound txnId body (inferEffect txnId [] body) := by
  exact inferenceSound_of_env_empty txnId body (inferEffect txnId [] body)
    (inferenceSoundEnv_all txnId [] body)

theorem vcg_effect_sound (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program) :
    inferenceSound txnId body (vcg R I G txnId isolation body).effect := by
  simpa [vcg] using inferenceSound_all txnId body

theorem vcgForTxn_sound (R : Rely) (I : Assertion) (G : Guarantee)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program) :
    ∃ info,
      vcgForTxn R I G (.txn txnId isolation body) = some info ∧
      inferenceSound txnId body info.effect := by
  refine ⟨vcg R I G txnId isolation body, rfl, ?_⟩
  exact vcg_effect_sound R I G txnId isolation body

theorem effectStable_false (F : TxnEffect) :
    effectStable (fun _ _ _ => False) F := by
  intro localDb visibleDb visibleDb' hFalse
  exact False.elim hFalse

theorem effectPost_stable_of_commitStable {R : Rely} {I : Assertion}
    {isolation : IsolationSpec Database} {F : TxnEffect}
    (hEffect : effectStable (Logic.relyMod R isolation.commit) F)
    (hI : Logic.stableAssertion R I) :
    Logic.stableBiAssertion (Logic.relyMod R isolation.commit) (effectPost I F) := by
  intro localDb visibleDb visibleDb' hPost hRely
  rcases hPost with ⟨hEffectDb, hIvisible⟩
  rcases hRely with ⟨hR, hIso⟩
  constructor
  · have hEq : F visibleDb = F visibleDb' := hEffect localDb visibleDb visibleDb' ⟨hR, hIso⟩
    rw [hEq] at hEffectDb
    exact hEffectDb
  · exact hI _ _ hIvisible hR

theorem effectPost_guarantee {G : Guarantee} {I : Assertion} {F : TxnEffect}
    (hGuarantee : guaranteeValid G F) :
    ∀ localDb visibleDb, effectPost I F localDb visibleDb → G visibleDb (Database.flush localDb visibleDb) := by
  intro localDb visibleDb hPost
  exact hGuarantee visibleDb localDb hPost.1

theorem effectLocalValid_false (txnId : TxnId) (body : Semantics.Program)
    (I : Assertion) (F : TxnEffect)
    (hDefined : effectDefinedOn I F)
    (hSound : inferenceSound txnId body F) :
    Logic.LocalValid (fun _ _ _ => False) txnId
      (fun localDb visible => localDb = [] ∧ I visible)
      body
      (effectPost I F) := by
  intro localDb visibleDb finalCfg hPre hMulti hSkip
  rcases hPre with ⟨hLocalEq, hIvisible⟩
  subst hLocalEq
  rcases hDefined visibleDb hIvisible with ⟨deltaDb, hDelta⟩
  have hPost :=
    hSound visibleDb deltaDb hDelta
      [] visibleDb finalCfg
      (by simp)
      hMulti
      hSkip
  rcases hPost with ⟨hLocalFinal, hVisibleFinal⟩
  constructor
  · simpa [effectPost, hLocalFinal, hVisibleFinal] using hDelta
  · simpa [hVisibleFinal] using hIvisible

theorem vcg_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hStableI : Logic.stableAssertion R I)
    (hLocal :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I (vcg R I G txnId isolation body).effect))
    (hCommit : (vcg R I G txnId isolation body).commitStable)
    (hGuarantee : (vcg R I G txnId isolation body).guaranteeOk)
    (hPreserve : (vcg R I G txnId isolation body).preservesInvariant) :
    Logic.GlobalValid I R (.txn txnId isolation body) G I := by
  have hCommit' :
      effectStable (Logic.relyMod R isolation.commit) (vcg R I G txnId isolation body).effect := by
    simpa [vcg] using hCommit
  have hGuarantee' :
      guaranteeValid G (vcg R I G txnId isolation body).effect := by
    simpa [vcg] using hGuarantee
  have hPreserve' : ∀ db db', I db → G db db' → I db' := by
    simpa [vcg] using hPreserve
  refine Logic.txnGlobalValid_of_localValid hStableI ?_ hLocal ?_ ?_ hPreserve'
  · intro localDb visibleDb
    constructor <;> intro h <;> simpa using h
  · exact effectPost_stable_of_commitStable hCommit' hStableI
  · exact effectPost_guarantee hGuarantee'

theorem vcg_sound_false {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      effectDefinedOn I ((vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee : (vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve : (vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Logic.GlobalValid I (fun _ _ => False) (.txn txnId isolation body) G I := by
  have hLocal :
      Logic.LocalValid (fun _ _ _ => False) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I ((vcg (fun _ _ => False) I G txnId isolation body).effect)) := by
    exact effectLocalValid_false txnId body I _ hDefined
      (vcg_effect_sound (fun _ _ => False) I G txnId isolation body)
  have hLocal' :
      Logic.LocalValid (Logic.relyMod (fun _ _ => False) isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I ((vcg (fun _ _ => False) I G txnId isolation body).effect)) := by
    intro localDb visibleDb finalCfg hPre hMulti hSkip
    have stripFalse :
        ∀ {cfg₁ cfg₂ : LocalConfig (IsolationSpec Database)},
          Logic.LocalMultiStep (Logic.relyMod (fun _ _ => False) isolation.exec)
              txnId (IsolationSpec Database) cfg₁ cfg₂ →
          Logic.LocalMultiStep (fun _ _ _ => False)
              txnId (IsolationSpec Database) cfg₁ cfg₂ := by
      intro cfg₁ cfg₂ hPath
      induction hPath with
      | refl =>
          exact Logic.MultiStep.refl
      | tail hPrev hLast ih =>
          refine Logic.MultiStep.tail ih ?_
          cases hLast with
          | inl hLocalStep =>
              exact Or.inl hLocalStep
          | inr hRely =>
              exact False.elim hRely.2.2.2.1
    have hMulti' :
        Logic.LocalMultiStep (fun _ _ _ => False) txnId (IsolationSpec Database)
          ⟨body, localDb, visibleDb⟩ finalCfg := by
      exact stripFalse hMulti
    exact hLocal localDb visibleDb finalCfg hPre
      hMulti'
      hSkip
  have hCommit : (vcg (fun _ _ => False) I G txnId isolation body).commitStable := by
    simp [vcg, Logic.relyMod, effectStable]
  exact vcg_sound txnId isolation body
    (Logic.stableAssertion_false I)
    hLocal'
    hCommit
    hGuarantee
    hPreserve

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
