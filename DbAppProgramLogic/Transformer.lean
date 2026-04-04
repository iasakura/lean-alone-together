import DbAppProgramLogic.Semantics
import DbAppProgramLogic.Logic
import DbAppProgramLogic.SetLanguage

namespace DbAppProgramLogic

/-!
Effect inference and VCG layer.

The development keeps two parallel views of inferred transaction effects:

* `inferEffect` computes a concrete database delta.
* `inferSetEffect` computes an explicit symbolic set-language expression.

Most soundness proofs in this file first relate syntax-directed inference back to the operational
semantics, and only then package the result into VCG-style obligations.
-/

/-- Concrete environment used by effect inference and by the later first-order encodings. -/
abbrev Env := List (VarName × Value)
/-- A semantic transaction effect maps the visible database to the rows written by the transaction. -/
abbrev TxnEffect := Database → Option Database
/-- Symbolic counterpart of `TxnEffect`, phrased in the explicit set language from `SetLanguage`. -/
abbrev SetEffect := Database → Option SetLanguage.SetExpr

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

/-- Instantiate free variables in an expression from the current environment, except for names that
are intentionally blocked because they are rebound by the surrounding command. -/
def instantiateExpr (env : Env) (blocked : List VarName) (expr : Expr) : Expr :=
  env.foldr
    (fun (binding : VarName × Value) acc =>
      if binding.1 ∈ blocked then
        acc
      else
        Expr.subst binding.1 binding.2.toExpr acc)
    expr

/-- Environment-aware instantiation of commands. Binder forms erase the bound variable before
descending so that later substitutions do not capture it. -/
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

def emptySetEffect : SetEffect :=
  fun _ => some SetLanguage.empty

def unionSetEffect (left right : SetEffect) : SetEffect :=
  fun db => do
    let s₁ ← left db
    let s₂ ← right db
    pure (.union s₁ s₂)

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

  /-- Syntax-directed semantic effect inference for transaction bodies. The result is concrete: a
  successful run returns the rows that should be appended to the local delta. -/
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

/-- The obligations discharged by the concrete VCG for one transaction body. -/
structure TransactionVCG where
  effect : TxnEffect
  execStable : Prop
  commitStable : Prop
  guaranteeOk : Prop
  preservesInvariant : Prop

/-- Build the concrete VCG obligations for a transaction body. -/
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

def reifyEffect (F : TxnEffect) : SetEffect :=
  fun db => SetLanguage.ofRows <$> F db

def denotesRows (ρ : SetLanguage.Env) (s : SetLanguage.SetExpr) (rows : Database) : Prop :=
  ∀ row, SetLanguage.denote ρ s row ↔ row ∈ rows

def overapproximatesRows (ρ : SetLanguage.Env) (s : SetLanguage.SetExpr) (rows : Database) : Prop :=
  ∀ row, row ∈ rows → SetLanguage.denote ρ s row

def assertionFormula (I : Assertion) : SetLanguage.Formula1 :=
  fun _ rows => ∃ db : Database, I db ∧ ∀ row, rows row ↔ row ∈ db

def currentGlobalBinding (db : Database) : SetLanguage.SetDenotation :=
  fun row => row ∈ db

def setEnvOfDatabase (x : VarName) (db : Database) : SetLanguage.Env :=
  (SetLanguage.Env.ofDatabases [] db).bindSet x (currentGlobalBinding db)

def weakenSetEffect (I : Assertion) (absVar : VarName) (F : SetEffect) : SetEffect :=
  fun db => do
    let s ← F db
    pure (SetLanguage.weakenToInvariant absVar (assertionFormula I) s)

theorem assertionFormula_current (I : Assertion) (x : VarName) (db : Database) (hI : I db) :
    assertionFormula I (setEnvOfDatabase x db) (currentGlobalBinding db) := by
  refine ⟨db, hI, ?_⟩
  intro row
  rfl

theorem denotesRows_ofRows (ρ : SetLanguage.Env) (rows : Database) :
    denotesRows ρ (SetLanguage.ofRows rows) rows := by
  intro row
  simp [denotesRows]

theorem overapproximatesRows_of_denotesRows (ρ : SetLanguage.Env) (s : SetLanguage.SetExpr)
    (rows : Database) (hDenote : denotesRows ρ s rows) :
    overapproximatesRows ρ s rows := by
  intro row hRow
  exact (hDenote row).2 hRow

theorem reifyEffect_sound (F : TxnEffect) (visibleDb localDb : Database)
    (hEffect : F visibleDb = some localDb) :
    ∃ s, reifyEffect F visibleDb = some s ∧
      denotesRows (SetLanguage.Env.ofDatabases localDb visibleDb) s localDb := by
  refine ⟨SetLanguage.ofRows localDb, ?_, ?_⟩
  · simp [reifyEffect, hEffect]
  · exact denotesRows_ofRows _ _

theorem vcg_reify_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hEffect : (vcg R I G txnId isolation body).effect visibleDb = some localDb) :
    ∃ s, reifyEffect (vcg R I G txnId isolation body).effect visibleDb = some s ∧
      denotesRows (SetLanguage.Env.ofDatabases localDb visibleDb) s localDb := by
  exact reifyEffect_sound _ _ _ hEffect

def rowPredicateFormula (env : Env) (source : VarName) (predicate : Expr) : SetLanguage.Formula0 :=
  fun ρ =>
    match ρ.lookupElem? source with
    | some row =>
        Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate) row.visible = some true
    | none => False

def insertSetExpr (txnId : TxnId) (env : Env) (expr : Expr) : Option SetLanguage.SetExpr := do
  let .record record ← evalInEnv env expr | none
  pure (SetLanguage.singleton (Row.fromInsert txnId record))

def deleteSetExprWith (outVar : VarName) (txnId : TxnId) (env : Env) (source : VarName) (predicate : Expr) :
    SetLanguage.SetExpr :=
  .bind .globalDb source
    (.ite
      (rowPredicateFormula env source predicate)
      (.comprehension outVar (fun ρ =>
        match ρ.lookupElem? outVar, ρ.lookupElem? source with
        | some out, some src => out = src.markDeleted txnId
        | _, _ => False))
      SetLanguage.empty)

def defaultOutVar (source : VarName) : VarName :=
  if source = "__out" then "__out0" else "__out"

theorem defaultOutVar_ne (source : VarName) :
    defaultOutVar source ≠ source := by
  unfold defaultOutVar
  by_cases h : source = "__out"
  · subst h
    simp
  · simp [h]
    intro hEq
    exact h hEq.symm

def deleteSetExpr (txnId : TxnId) (env : Env) (source : VarName) (predicate : Expr) :
    SetLanguage.SetExpr :=
  deleteSetExprWith (defaultOutVar source) txnId env source predicate

def updateSetExprWith (outVar : VarName) (txnId : TxnId) (env : Env) (source : VarName)
    (updateExpr predicate : Expr) : SetLanguage.SetExpr :=
  .bind .globalDb source
    (.ite
      (rowPredicateFormula env source predicate)
      (.comprehension outVar (fun ρ =>
        match ρ.lookupElem? outVar, ρ.lookupElem? source with
        | some out, some src =>
            ∃ updated,
              Expr.eval (Semantics.instantiateRecord source src.visible
                (instantiateExpr env [source] updateExpr)) = some (.record updated) ∧
              out = src.overwrite txnId updated
        | _, _ => False))
      SetLanguage.empty)

def updateSetExpr (txnId : TxnId) (env : Env) (source : VarName)
    (updateExpr predicate : Expr) : SetLanguage.SetExpr :=
  updateSetExprWith (defaultOutVar source) txnId env source updateExpr predicate

theorem insertSetExpr_sound (txnId : TxnId) (env : Env) (expr : Expr)
    (s : SetLanguage.SetExpr) (hInsert : insertSetExpr txnId env expr = some s) :
    ∃ record, s = SetLanguage.singleton (Row.fromInsert txnId record) ∧
      evalInEnv env expr = some (.record record) := by
  unfold insertSetExpr at hInsert
  cases hEval : evalInEnv env expr with
  | none =>
      simp [hEval] at hInsert
  | some value =>
      cases value with
      | scalar scalar =>
          simp [hEval] at hInsert
      | set records =>
          simp [hEval] at hInsert
      | record record =>
          simp [hEval] at hInsert
          exact ⟨record, hInsert.symm, rfl⟩

theorem deleteSetExprWith_sound (outVar : VarName) (txnId : TxnId) (env : Env)
    (source : VarName) (predicate : Expr)
    (db rows : Database) (row : Row)
    (hNe : outVar ≠ source)
    (hCollect : Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (deleteSetExprWith outVar txnId env source predicate) row ↔
      row ∈ rows := by
  have hNe' : source ≠ outVar := by
    intro hEq
    exact hNe hEq.symm
  rw [Semantics.mem_collectDeleted_iff hCollect]
  constructor
  · intro h
    simp [deleteSetExprWith, rowPredicateFormula, SetLanguage.denote, SetLanguage.empty] at h
    rcases h with ⟨mid, hMid, hPred, hMatch⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMid
    · have hLookup :
          (((SetLanguage.Env.ofDatabases [] db).bindElem source mid).bindElem outVar row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq : outVar = source
          · exact False.elim (hNe hEq)
          · simp [SetLanguage.Env.lookupElemList?, hEq]
      rw [hLookup] at hMatch
      simpa using hMatch
  · intro h
    simp [deleteSetExprWith, rowPredicateFormula, SetLanguage.denote, SetLanguage.empty]
    rcases h with ⟨mid, hMid, hPred, hEq⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMid
    · have hLookup :
          (((SetLanguage.Env.ofDatabases [] db).bindElem source mid).bindElem outVar row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq : outVar = source
          · exact False.elim (hNe hEq)
          · simp [SetLanguage.Env.lookupElemList?, hEq]
      rw [hLookup]
      simpa using hEq

theorem deleteSetExpr_sound (txnId : TxnId) (env : Env)
    (source : VarName) (predicate : Expr)
    (db rows : Database) (row : Row)
    (hCollect : Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (deleteSetExpr txnId env source predicate) row ↔
      row ∈ rows := by
  simpa [deleteSetExpr] using
    deleteSetExprWith_sound (defaultOutVar source) txnId env source predicate db rows row
      (defaultOutVar_ne source) hCollect

theorem updateSetExprWith_sound (outVar : VarName) (txnId : TxnId) (env : Env)
    (source : VarName) (updateExpr predicate : Expr)
    (db rows : Database) (row : Row)
    (hNe : outVar ≠ source)
    (hCollect :
      Semantics.collectUpdated db txnId source
        (instantiateExpr env [source] updateExpr)
        (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (updateSetExprWith outVar txnId env source updateExpr predicate) row ↔
      row ∈ rows := by
  unfold Semantics.collectUpdated at hCollect
  rw [Semantics.mem_collectUpdated_go_iff hCollect]
  constructor
  · intro h
    simp [updateSetExprWith, rowPredicateFormula, SetLanguage.denote, SetLanguage.empty] at h
    rcases h with ⟨mid, hMid, hPred, hMatch⟩
    have hLookup :
        (((SetLanguage.Env.ofDatabases [] db).bindElem source mid).bindElem outVar row).lookupElem? source =
          some mid := by
        unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
        by_cases hEq : outVar = source
        · exact False.elim (hNe hEq)
        · simp [SetLanguage.Env.lookupElemList?, hEq]
    rw [hLookup] at hMatch
    rcases hMatch with ⟨updated, hEval, hEq⟩
    refine ⟨mid, ?_, hPred, updated, hEval, hEq⟩
    simpa [SetLanguage.Env.ofDatabases] using hMid
  · intro h
    simp [updateSetExprWith, rowPredicateFormula, SetLanguage.denote, SetLanguage.empty]
    rcases h with ⟨mid, hMid, hPred, updated, hEval, hEq⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMid
    · have hLookup :
          (((SetLanguage.Env.ofDatabases [] db).bindElem source mid).bindElem outVar row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq' : outVar = source
          · exact False.elim (hNe hEq')
          · simp [SetLanguage.Env.lookupElemList?, hEq']
      rw [hLookup]
      exact ⟨updated, hEval, hEq⟩

theorem updateSetExpr_sound (txnId : TxnId) (env : Env)
    (source : VarName) (updateExpr predicate : Expr)
    (db rows : Database) (row : Row)
    (hCollect :
      Semantics.collectUpdated db txnId source
        (instantiateExpr env [source] updateExpr)
        (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (updateSetExpr txnId env source updateExpr predicate) row ↔
      row ∈ rows := by
  simpa [updateSetExpr] using
    updateSetExprWith_sound (defaultOutVar source) txnId env source updateExpr predicate db rows row
      (defaultOutVar_ne source) hCollect

theorem deleteSetExpr_abstractGlobal_sound (absVar : VarName) (txnId : TxnId) (env : Env)
    (source : VarName) (predicate : Expr)
    (db rows : Database) (row : Row)
    (hCollect : Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (setEnvOfDatabase absVar db)
      (SetLanguage.abstractGlobal absVar (deleteSetExpr txnId env source predicate)) row ↔
      row ∈ rows := by
  have hNe : defaultOutVar source ≠ source := defaultOutVar_ne source
  rw [Semantics.mem_collectDeleted_iff hCollect]
  constructor
  · intro h
    simp [deleteSetExpr, deleteSetExprWith, rowPredicateFormula, setEnvOfDatabase,
      currentGlobalBinding, SetLanguage.abstractGlobal, SetLanguage.denote, SetLanguage.empty] at h
    rcases h with ⟨mid, hMid, hPred, hMatch⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [currentGlobalBinding] using hMid
    · have hLookup :
          ((((SetLanguage.Env.ofDatabases [] db).bindSet absVar (currentGlobalBinding db)).bindElem source mid).bindElem
            (defaultOutVar source) row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq : defaultOutVar source = source
          · exact False.elim (hNe hEq)
          · simp [SetLanguage.Env.lookupElemList?, hEq]
      rw [hLookup] at hMatch
      simpa using hMatch
  · intro h
    simp [deleteSetExpr, deleteSetExprWith, rowPredicateFormula, setEnvOfDatabase,
      currentGlobalBinding, SetLanguage.abstractGlobal, SetLanguage.denote, SetLanguage.empty]
    rcases h with ⟨mid, hMid, hPred, hEq⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [currentGlobalBinding] using hMid
    · have hLookup :
          ((((SetLanguage.Env.ofDatabases [] db).bindSet absVar (currentGlobalBinding db)).bindElem source mid).bindElem
            (defaultOutVar source) row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq' : defaultOutVar source = source
          · exact False.elim (hNe hEq')
          · simp [SetLanguage.Env.lookupElemList?, hEq']
      rw [hLookup]
      simpa using hEq

theorem updateSetExpr_abstractGlobal_sound (absVar : VarName) (txnId : TxnId) (env : Env)
    (source : VarName) (updateExpr predicate : Expr)
    (db rows : Database) (row : Row)
    (hCollect :
      Semantics.collectUpdated db txnId source
        (instantiateExpr env [source] updateExpr)
        (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (setEnvOfDatabase absVar db)
      (SetLanguage.abstractGlobal absVar (updateSetExpr txnId env source updateExpr predicate)) row ↔
      row ∈ rows := by
  have hNe : defaultOutVar source ≠ source := defaultOutVar_ne source
  unfold Semantics.collectUpdated at hCollect
  rw [Semantics.mem_collectUpdated_go_iff hCollect]
  constructor
  · intro h
    simp [updateSetExpr, updateSetExprWith, rowPredicateFormula, setEnvOfDatabase,
      currentGlobalBinding, SetLanguage.abstractGlobal, SetLanguage.denote, SetLanguage.empty] at h
    rcases h with ⟨mid, hMid, hPred, hMatch⟩
    have hLookup :
        ((((SetLanguage.Env.ofDatabases [] db).bindSet absVar (currentGlobalBinding db)).bindElem source mid).bindElem
          (defaultOutVar source) row).lookupElem? source =
          some mid := by
      unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
      by_cases hEq : defaultOutVar source = source
      · exact False.elim (hNe hEq)
      · simp [SetLanguage.Env.lookupElemList?, hEq]
    rw [hLookup] at hMatch
    rcases hMatch with ⟨updated, hEval, hEq⟩
    refine ⟨mid, ?_, hPred, updated, hEval, hEq⟩
    simpa [currentGlobalBinding] using hMid
  · intro h
    simp [updateSetExpr, updateSetExprWith, rowPredicateFormula, setEnvOfDatabase,
      currentGlobalBinding, SetLanguage.abstractGlobal, SetLanguage.denote, SetLanguage.empty]
    rcases h with ⟨mid, hMid, hPred, updated, hEval, hEq⟩
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [currentGlobalBinding] using hMid
    · have hLookup :
          ((((SetLanguage.Env.ofDatabases [] db).bindSet absVar (currentGlobalBinding db)).bindElem source mid).bindElem
            (defaultOutVar source) row).lookupElem? source =
            some mid := by
          unfold SetLanguage.Env.lookupElem? SetLanguage.Env.bindElem
          by_cases hEq' : defaultOutVar source = source
          · exact False.elim (hNe hEq')
          · simp [SetLanguage.Env.lookupElemList?, hEq']
      rw [hLookup]
      exact ⟨updated, hEval, hEq⟩

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

theorem infer_foreachRuntime_sound (txnId : TxnId) (env : Env) (done remaining : Expr)
    (doneVar elemVar : VarName) (body : Semantics.Program) (db delta : Database)
    (h : inferEffect txnId env (.foreachRuntime done remaining doneVar elemVar body) db = some delta) :
    ∃ doneRecords remainingRecords,
      evalInEnv env done = some (.set doneRecords) ∧
      evalInEnv env remaining = some (.set remainingRecords) ∧
      inferEffect txnId env
        (.foreachRuntime (Expr.setLit doneRecords) (Expr.setLit remainingRecords) doneVar elemVar body)
        db = some delta := by
  cases hDone : evalInEnv env done with
  | none =>
      have : False := by
        simp [inferEffect, hDone] at h
      exact False.elim this
  | some doneValue =>
      cases doneValue with
      | scalar s =>
          have : False := by
            simp [inferEffect, hDone] at h
          exact False.elim this
      | record record =>
          have : False := by
            simp [inferEffect, hDone] at h
          exact False.elim this
      | set doneRecords =>
          cases hRemaining : evalInEnv env remaining with
          | none =>
              have : False := by
                simp [inferEffect, hDone, hRemaining] at h
              exact False.elim this
          | some remainingValue =>
              cases remainingValue with
              | scalar s =>
                  have : False := by
                    simp [inferEffect, hDone, hRemaining] at h
                  exact False.elim this
              | record record =>
                  have : False := by
                    simp [inferEffect, hDone, hRemaining] at h
                  exact False.elim this
              | set remainingRecords =>
                  refine ⟨doneRecords, remainingRecords, ?_, ?_, ?_⟩
                  · rfl
                  · rfl
                  · simpa [inferEffect, hDone, hRemaining] using h

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
            (by simpa [inferEffect] using hEffect) with
          ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
        rcases hBody (foreachEnv env doneVar elemVar done current) rowsCurrent hCurrentEff with
          ⟨sCurrent, hCurrentSet⟩
        have hRestForeach :
            inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
              some rowsRest := by
          simpa [inferEffect, inferForeach] using hRestEff
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
          simpa [inferEffect, inferForeach] using hRuntimeEff
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
          simpa [inferEffect, inferForeach] using hRuntimeEff
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
                  db rows (by simpa [inferEffect] using hEffect) with
                ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
              have hRestForeach :
                  inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                    some rowsRest := by
                simpa [inferEffect, inferForeach] using hRestEff
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
        simpa [inferEffect, inferForeach] using hRuntimeEff
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
        simpa [inferEffect, inferForeach] using hRuntimeEff
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
                  db rows (by simpa [inferEffect] using hEffect) with
                ⟨rowsCurrent, rowsRest, hCurrentEff, hRestEff, hRows⟩
              have hRestForeach :
                  inferForeach txnId env doneVar elemVar body (done ++ [current]) rest db =
                    some rowsRest := by
                simpa [inferEffect, inferForeach] using hRestEff
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
        simpa [inferEffect, inferForeach] using hRuntimeEff
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
        simpa [inferEffect, inferForeach] using hRuntimeEff
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

theorem vcg_setSound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : (vcg R I G txnId isolation body).effect visibleDb = some localDb) :
    denotesRows (SetLanguage.Env.ofDatabases [] visibleDb) s localDb := by
  intro row
  exact inferSetEffect_sound txnId [] body visibleDb s localDb row hSet
    (by simpa [vcg] using hEffect)

theorem vcgForTxn_setSound {R : Rely} {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : TransactionVCG) (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInfo : vcgForTxn R I G (.txn txnId isolation body) = some info)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : info.effect visibleDb = some localDb) :
    denotesRows (SetLanguage.Env.ofDatabases [] visibleDb) s localDb := by
  simp [vcgForTxn] at hInfo
  subst info
  exact vcg_setSound txnId isolation body visibleDb localDb s hSet hEffect

theorem vcg_setWeaken_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (absVar : VarName) (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : (vcg R I G txnId isolation body).effect visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  exact inferSetEffect_weaken_sound I absVar txnId [] body visibleDb s localDb row hInv hSet
    (by simpa [vcg] using hEffect) hRow

theorem vcgForTxn_setWeaken_sound {R : Rely} {I : Assertion} {G : Guarantee}
    (absVar : VarName) (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : TransactionVCG) (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInfo : vcgForTxn R I G (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : info.effect visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) row := by
  simp [vcgForTxn] at hInfo
  subst info
  exact vcg_setWeaken_sound absVar txnId isolation body visibleDb localDb s row hInv hSet hEffect hRow

/-- The weakened symbolic postcondition used at the transaction interface. This packages the exact
symbolic effect together with existential abstraction over the current global database. -/
def symbolicVcg (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program) : SetEffect :=
  weakenSetEffect I absVar (inferSetEffect txnId [] body)

def symbolicVcgForTxn (I : Assertion) (absVar : VarName) : Semantics.Program → Option SetEffect
  | .txn txnId _isolation body => some (symbolicVcg I absVar txnId body)
  | _ => none

/-- Convenience wrapper for evaluating `symbolicVcgForTxn` on a concrete visible database. -/
def symbolicPostForTxn (I : Assertion) (absVar : VarName)
    (program : Semantics.Program) (visibleDb : Database) : Option SetLanguage.SetExpr := do
  let info ← symbolicVcgForTxn I absVar program
  info visibleDb

theorem symbolicVcg_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) row := by
  have hSym :
      symbolicVcg I absVar txnId body visibleDb =
        some (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) := by
    simp [symbolicVcg, weakenSetEffect, hSet]
  rw [hSym]
  simp
  exact inferSetEffect_weaken_sound I absVar txnId [] body visibleDb s localDb row hInv hSet hEffect hRow

theorem symbolicVcg_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (row : Row)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) row := by
  rcases inferSetEffect_some_of_inferEffect_some txnId [] body visibleDb localDb hInferable hEffect with
    ⟨s, hSet⟩
  exact symbolicVcg_sound I absVar txnId body visibleDb localDb s row hInv hSet hEffect hRow

theorem symbolicVcg_some_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    ∃ s, symbolicVcg I absVar txnId body visibleDb = some s := by
  rcases inferSetEffect_some_of_inferEffect_some txnId [] body visibleDb localDb hInferable hEffect with
    ⟨s, hSet⟩
  refine ⟨SetLanguage.weakenToInvariant absVar (assertionFormula I) s, ?_⟩
  simp [symbolicVcg, weakenSetEffect, hSet]

theorem symbolicVcg_eq_some_get!_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    symbolicVcg I absVar txnId body visibleDb =
      some (Option.get! (symbolicVcg I absVar txnId body visibleDb)) := by
  rcases symbolicVcg_some_of_inferEffect_some I absVar txnId body visibleDb localDb hInferable hEffect with
    ⟨s, hSome⟩
  apply option_eq_some_get!
  intro hNone
  rw [hNone] at hSome
  cases hSome

theorem symbolicVcg_overapprox_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) localDb := by
  exact inferSetEffect_weaken_overapprox I absVar txnId [] body visibleDb s localDb hInv hSet hEffect

theorem symbolicVcg_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicVcg I absVar txnId body visibleDb)) localDb := by
  intro row hRow
  exact symbolicVcg_sound_of_inferEffect_some I absVar txnId body visibleDb localDb row
    hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (s : SetLanguage.SetExpr) (row : Row)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) row := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_sound I absVar txnId body visibleDb localDb s row hInv hSet hEffect hRow

theorem symbolicVcgForTxn_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (row : Row)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) row := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_sound_of_inferEffect_some I absVar txnId body visibleDb localDb row
    hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_some_at_visibleDb_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    ∃ s, info visibleDb = some s := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_some_of_inferEffect_some I absVar txnId body visibleDb localDb hInferable hEffect

theorem symbolicVcgForTxn_eq_some_get!_at_visibleDb_of_inferEffect_some
    (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    info visibleDb = some (Option.get! (info visibleDb)) := by
  simp [symbolicVcgForTxn] at hInfo
  subst info
  exact symbolicVcg_eq_some_get!_of_inferEffect_some I absVar txnId body visibleDb localDb
    hInferable hEffect

theorem symbolicPostForTxn_sound_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database) (row : Row)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb)
    (hRow : row ∈ localDb) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb)) row := by
  have hInfo :
      symbolicVcgForTxn I absVar (.txn txnId isolation body) =
        some (symbolicVcg I absVar txnId body) := by
    simp [symbolicVcgForTxn]
  have hShape :
      symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb =
        symbolicVcg I absVar txnId body visibleDb := by
    simp [symbolicPostForTxn, symbolicVcgForTxn]
  rw [hShape]
  exact symbolicVcgForTxn_sound_of_inferEffect_some I absVar txnId isolation body
    (symbolicVcg I absVar txnId body) visibleDb localDb row hInfo hInferable hInv hEffect hRow

theorem symbolicPostForTxn_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (visibleDb localDb : Database)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (symbolicPostForTxn I absVar (.txn txnId isolation body) visibleDb))
      localDb := by
  intro row hRow
  exact symbolicPostForTxn_sound_of_inferEffect_some I absVar txnId isolation body
    visibleDb localDb row hInferable hInv hEffect hRow

theorem symbolicVcgForTxn_overapprox_sound (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database) (s : SetLanguage.SetExpr)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInv : I visibleDb)
    (hSet : inferSetEffect txnId [] body visibleDb = some s)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (SetLanguage.weakenToInvariant absVar (assertionFormula I) s) localDb := by
  have hInfo' := hInfo
  simp [symbolicVcgForTxn] at hInfo'
  subst info
  exact symbolicVcg_overapprox_sound I absVar txnId body visibleDb localDb s hInv hSet hEffect

theorem symbolicVcgForTxn_overapprox_of_inferEffect_some (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (info : SetEffect) (visibleDb localDb : Database)
    (hInfo : symbolicVcgForTxn I absVar (.txn txnId isolation body) = some info)
    (hInferable : SetInferable body)
    (hInv : I visibleDb)
    (hEffect : inferEffect txnId [] body visibleDb = some localDb) :
    overapproximatesRows (SetLanguage.Env.ofDatabases [] visibleDb)
      (Option.get! (info visibleDb)) localDb := by
  intro row hRow
  exact symbolicVcgForTxn_sound_of_inferEffect_some I absVar txnId isolation body info
    visibleDb localDb row hInfo hInferable hInv hEffect hRow

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
  rcases hRely with ⟨baseDb, hR, hIsoVisible, hIsoVisible'⟩
  constructor
  · have hEq : F visibleDb = F visibleDb' := by
      exact hEffect localDb visibleDb visibleDb' ⟨baseDb, hR, hIsoVisible, hIsoVisible'⟩
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
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hLocal :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (fun localDb visible => localDb = [] ∧ I visible)
        body
        (effectPost I (vcg R I G txnId isolation body).effect))
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
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
  refine Logic.txnGlobalValid_of_localValid hStableI hExecStable hCommitIsoStable ?_ hLocal ?_ ?_ hPreserve'
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
              rcases hRely with ⟨_, _, _, hRely⟩
              rcases hRely with ⟨_, hFalse, _, _⟩
              exact False.elim hFalse
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
    (Logic.stableIsolation_false isolation.exec)
    hLocal'
    (Logic.stableIsolation_false isolation.commit)
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
