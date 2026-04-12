import DbAppProgramLogic.Transformer

namespace DbAppProgramLogic

namespace FirstOrder

/-!
First-order-style encodings for symbolic postconditions.

This file is the current bridge toward Sec. 5.2 of the paper. It does not yet implement the full
deep embedding and solver pipeline, but it does provide a deep formula language for row-membership
queries and syntax-directed encoders from transaction bodies to those formulas.
-/

abbrev Env := DbAppProgramLogic.Env

/-- A lightweight deep embedding of first-order formulas over the existing expression language. -/
inductive Formula where
  | top
  | bot
  | evalBool : Expr → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | not : Formula → Formula
  | existsScalar : VarName → Formula → Formula
  | existsRecord : VarName → Formula → Formula
  | existsSet : VarName → Formula → Formula
  | forallScalar : VarName → Formula → Formula
  | forallRecord : VarName → Formula → Formula
  | forallSet : VarName → Formula → Formula
  deriving Inhabited

def eq (lhs rhs : Expr) : Formula :=
  .evalBool (.binop .eq lhs rhs)

def le (lhs rhs : Expr) : Formula :=
  .evalBool (.binop .le lhs rhs)

def ge (lhs rhs : Expr) : Formula :=
  .evalBool (.binop .ge lhs rhs)

def denote (env : Env) : Formula → Prop
  | .top => True
  | .bot => False
  | .evalBool expr => Transformer.evalInEnv env expr = some (.scalar (.bool true))
  | .and φ ψ => denote env φ ∧ denote env ψ
  | .or φ ψ => denote env φ ∨ denote env ψ
  | .imp φ ψ => denote env φ → denote env ψ
  | .not φ => ¬ denote env φ
  | .existsScalar x φ => ∃ value : ScalarLit, denote (env.insert x (.scalar value)) φ
  | .existsRecord x φ => ∃ value : RecordLit, denote (env.insert x (.record value)) φ
  | .existsSet x φ => ∃ value : SetLit, denote (env.insert x (.set value)) φ
  | .forallScalar x φ => ∀ value : ScalarLit, denote (env.insert x (.scalar value)) φ
  | .forallRecord x φ => ∀ value : RecordLit, denote (env.insert x (.record value)) φ
  | .forallSet x φ => ∀ value : SetLit, denote (env.insert x (.set value)) φ

def exprCondition (env : DbAppProgramLogic.Env) (expr : Expr) : Formula :=
  .evalBool (Transformer.instantiateExpr env [] expr)

def rowPredicateFormula (env : DbAppProgramLogic.Env) (source : VarName) (predicate : Expr) : Formula :=
  .evalBool (Transformer.instantiateExpr env [source] predicate)

@[simp] theorem denote_top (env : Env) :
    denote env .top := by
  trivial

@[simp] theorem denote_bot (env : Env) :
    ¬ denote env .bot := by
  simp [denote]

@[simp] theorem denote_evalBool (env : Env) (expr : Expr) :
    denote env (.evalBool expr) ↔
      Transformer.evalInEnv env expr = some (.scalar (.bool true)) := Iff.rfl

@[simp] theorem denote_and (env : Env) (φ ψ : Formula) :
    denote env (.and φ ψ) ↔ denote env φ ∧ denote env ψ := Iff.rfl

@[simp] theorem denote_or (env : Env) (φ ψ : Formula) :
    denote env (.or φ ψ) ↔ denote env φ ∨ denote env ψ := Iff.rfl

@[simp] theorem denote_imp (env : Env) (φ ψ : Formula) :
    denote env (.imp φ ψ) ↔ (denote env φ → denote env ψ) := Iff.rfl

@[simp] theorem denote_not (env : Env) (φ : Formula) :
    denote env (.not φ) ↔ ¬ denote env φ := Iff.rfl

@[simp] theorem denote_existsScalar (env : Env) (x : VarName) (φ : Formula) :
    denote env (.existsScalar x φ) ↔
      ∃ value : ScalarLit, denote (env.insert x (.scalar value)) φ := Iff.rfl

@[simp] theorem denote_existsRecord (env : Env) (x : VarName) (φ : Formula) :
    denote env (.existsRecord x φ) ↔
      ∃ value : RecordLit, denote (env.insert x (.record value)) φ := Iff.rfl

@[simp] theorem denote_existsSet (env : Env) (x : VarName) (φ : Formula) :
    denote env (.existsSet x φ) ↔
      ∃ value : SetLit, denote (env.insert x (.set value)) φ := Iff.rfl

@[simp] theorem denote_forallScalar (env : Env) (x : VarName) (φ : Formula) :
    denote env (.forallScalar x φ) ↔
      ∀ value : ScalarLit, denote (env.insert x (.scalar value)) φ := Iff.rfl

@[simp] theorem denote_forallRecord (env : Env) (x : VarName) (φ : Formula) :
    denote env (.forallRecord x φ) ↔
      ∀ value : RecordLit, denote (env.insert x (.record value)) φ := Iff.rfl

@[simp] theorem denote_forallSet (env : Env) (x : VarName) (φ : Formula) :
    denote env (.forallSet x φ) ↔
      ∀ value : SetLit, denote (env.insert x (.set value)) φ := Iff.rfl

@[simp] theorem denote_eq (env : Env) (lhs rhs : Expr) :
    denote env (eq lhs rhs) ↔
      Transformer.evalInEnv env (.binop .eq lhs rhs) = some (.scalar (.bool true)) := Iff.rfl

@[simp] theorem denote_le (env : Env) (lhs rhs : Expr) :
    denote env (le lhs rhs) ↔
      Transformer.evalInEnv env (.binop .le lhs rhs) = some (.scalar (.bool true)) := Iff.rfl

@[simp] theorem denote_ge (env : Env) (lhs rhs : Expr) :
    denote env (ge lhs rhs) ↔
      Transformer.evalInEnv env (.binop .ge lhs rhs) = some (.scalar (.bool true)) := Iff.rfl

@[simp] theorem denote_exprCondition (env : DbAppProgramLogic.Env) (expr : Expr) :
    denote [] (exprCondition env expr) ↔
      Transformer.evalInEnv env expr = some (.scalar (.bool true)) := by
  unfold exprCondition denote Transformer.evalInEnv
  rw [Transformer.instantiateExpr_nil]

@[simp] theorem denote_rowPredicateFormula (env : DbAppProgramLogic.Env) (source : VarName) (predicate : Expr)
    (record : RecordLit) :
    denote (DbAppProgramLogic.Env.insert [] source (.record record)) (rowPredicateFormula env source predicate) ↔
      Semantics.satisfiesPredicate source (Transformer.instantiateExpr env [source] predicate) record = some true := by
  change
    Transformer.evalInEnv (DbAppProgramLogic.Env.insert [] source (.record record))
      (Transformer.instantiateExpr env [source] predicate) = some (.scalar (.bool true)) ↔
      Semantics.satisfiesPredicate source (Transformer.instantiateExpr env [source] predicate) record = some true
  unfold Transformer.evalInEnv
  unfold Semantics.satisfiesPredicate Semantics.instantiateRecord
  have hInst :
      Transformer.instantiateExpr (DbAppProgramLogic.Env.insert [] source (.record record)) []
        (Transformer.instantiateExpr env [source] predicate) =
          Expr.subst source (.lit (.record record))
            (Transformer.instantiateExpr env [source] predicate) := by
    simpa [DbAppProgramLogic.Env.insert, Transformer.instantiateExpr_nil] using
      (Transformer.instantiateExpr_insert ([] : DbAppProgramLogic.Env) source (.record record) []
        (Transformer.instantiateExpr env [source] predicate))
  rw [hInst]
  cases hEval : (Expr.subst source (.lit (.record record))
      (Transformer.instantiateExpr env [source] predicate)).eval <;> simp [hEval]
  case some val =>
    cases val <;> simp
    case scalar lit =>
      cases lit <;> simp

/-- Row-membership formulas are the target used by the current `S -> FOL` bridge. They talk about a
single candidate output row and characterize when that row belongs to a symbolic effect. -/
inductive MembershipFormula where
  | top
  | bot
  | inVar : VarName → VarName → MembershipFormula
  | inLocalDb : VarName → MembershipFormula
  | inGlobalDb : VarName → MembershipFormula
  | eqConst : VarName → Row → MembershipFormula
  | evalClosedBool : Expr → MembershipFormula
  | satisfiesPredicate : VarName → Expr → MembershipFormula
  | eqDeleted : VarName → VarName → TxnId → MembershipFormula
  | eqUpdated : VarName → VarName → TxnId → Expr → MembershipFormula
  | and : MembershipFormula → MembershipFormula → MembershipFormula
  | or : MembershipFormula → MembershipFormula → MembershipFormula
  | imp : MembershipFormula → MembershipFormula → MembershipFormula
  | not : MembershipFormula → MembershipFormula
  | existsElem : VarName → MembershipFormula → MembershipFormula
  | existsSet : VarName → MembershipFormula → MembershipFormula
  deriving Inhabited, Repr

def denoteMembership (ρ : SetLanguage.Env) : MembershipFormula → Prop
  | .top => True
  | .bot => False
  | .inVar elemVar setVar =>
      match ρ.lookupElem? elemVar, ρ.lookupSet? setVar with
      | some row, some rows => rows row
      | _, _ => False
  | .inLocalDb elemVar =>
      match ρ.lookupElem? elemVar with
      | some row => ρ.localDb row
      | none => False
  | .inGlobalDb elemVar =>
      match ρ.lookupElem? elemVar with
      | some row => ρ.globalDb row
      | none => False
  | .eqConst elemVar row₀ =>
      match ρ.lookupElem? elemVar with
      | some row => row = row₀
      | none => False
  | .evalClosedBool expr =>
      Expr.eval expr = some (.scalar (.bool true))
  | .satisfiesPredicate source predicate =>
      match ρ.lookupElem? source with
      | some row => Semantics.satisfiesPredicate source predicate row.visible = some true
      | none => False
  | .eqDeleted outVar source txnId =>
      match ρ.lookupElem? outVar, ρ.lookupElem? source with
      | some out, some src => out = src.markDeleted txnId
      | _, _ => False
  | .eqUpdated outVar source txnId updateExpr =>
      match ρ.lookupElem? outVar, ρ.lookupElem? source with
      | some out, some src =>
          ∃ updated,
            Expr.eval (Semantics.instantiateRecord source src.visible updateExpr) = some (.record updated) ∧
            out = src.overwrite txnId updated
      | _, _ => False
  | .and φ ψ => denoteMembership ρ φ ∧ denoteMembership ρ ψ
  | .or φ ψ => denoteMembership ρ φ ∨ denoteMembership ρ ψ
  | .imp φ ψ => denoteMembership ρ φ → denoteMembership ρ ψ
  | .not φ => ¬ denoteMembership ρ φ
  | .existsElem x φ => ∃ row : Row, denoteMembership (ρ.bindElem x row) φ
  | .existsSet x φ => ∃ rows : SetLanguage.SetDenotation, denoteMembership (ρ.bindSet x rows) φ

def encodeOfRowsMembership (elemVar : VarName) : Database → MembershipFormula
  | [] => .bot
  | row :: rows => .or (.eqConst elemVar row) (encodeOfRowsMembership elemVar rows)

def encodeSingletonMembership (elemVar : VarName) (row : Row) : MembershipFormula :=
  .eqConst elemVar row

def encodeDeleteMembership (elemVar : VarName) (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (source : VarName) (predicate : Expr) : MembershipFormula :=
  .existsElem source
    (.and (.inGlobalDb source)
      (.and
        (.satisfiesPredicate source (Transformer.instantiateExpr env [source] predicate))
        (.eqDeleted elemVar source txnId)))

def encodeUpdateMembership (elemVar : VarName) (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (source : VarName) (updateExpr predicate : Expr) : MembershipFormula :=
  .existsElem source
    (.and (.inGlobalDb source)
      (.and
        (.satisfiesPredicate source (Transformer.instantiateExpr env [source] predicate))
        (.eqUpdated elemVar source txnId (Transformer.instantiateExpr env [source] updateExpr))))

def inferWriteMembership (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (elemVar : VarName) : Semantics.Program → Option MembershipFormula
  | .skip => some .bot
  | .letE x expr body => do
      let value ← Transformer.evalInEnv env expr
      inferWriteMembership txnId (env.insert x value) elemVar body
  | .ite cond thenBranch elseBranch => do
      let .scalar (.bool b) ← Transformer.evalInEnv env cond | none
      if b then inferWriteMembership txnId env elemVar thenBranch
      else inferWriteMembership txnId env elemVar elseBranch
  | .seq left right => do
      let φLeft ← inferWriteMembership txnId env elemVar left
      let φRight ← inferWriteMembership txnId env elemVar right
      pure (.or φLeft φRight)
  | .insert expr => do
      let .record record ← Transformer.evalInEnv env expr | none
      pure (encodeSingletonMembership elemVar (Row.fromInsert txnId record))
  | .delete source predicate =>
      if elemVar = source then
        none
      else
        some (encodeDeleteMembership elemVar txnId env source predicate)
  | .update source updateExpr predicate =>
      if elemVar = source then
        none
      else
        some (encodeUpdateMembership elemVar txnId env source updateExpr predicate)
  | _ => none

def inferMembership (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (elemVar : VarName) (db : Database) : Semantics.Program → Option MembershipFormula
  | .skip => some .bot
  | .letE x expr body => do
      let value ← Transformer.evalInEnv env expr
      inferMembership txnId (env.insert x value) elemVar db body
  | .ite cond thenBranch elseBranch => do
      let .scalar (.bool b) ← Transformer.evalInEnv env cond | none
      if b then inferMembership txnId env elemVar db thenBranch
      else inferMembership txnId env elemVar db elseBranch
  | .seq left right => do
      let φLeft ← inferMembership txnId env elemVar db left
      let φRight ← inferMembership txnId env elemVar db right
      pure (.or φLeft φRight)
  | .insert expr => do
      let .record record ← Transformer.evalInEnv env expr | none
      pure (encodeSingletonMembership elemVar (Row.fromInsert txnId record))
  | .delete source predicate =>
      if elemVar = source then
        none
      else
        some (encodeDeleteMembership elemVar txnId env source predicate)
  | .select binder source predicate body => do
      let selected ← Semantics.collectSelected db source (Transformer.instantiateExpr env [source] predicate)
      inferMembership txnId (env.insert binder (.set selected)) elemVar db body
  | .update source updateExpr predicate =>
      if elemVar = source then
        none
      else
        some (encodeUpdateMembership elemVar txnId env source updateExpr predicate)
  | _ => none

def encodeSetExprMembership (elemVar : VarName) : SetLanguage.SetExpr → Option MembershipFormula
  | _ => none

@[simp] theorem denoteMembership_inVar (ρ : SetLanguage.Env) (elemVar setVar : VarName) :
    denoteMembership ρ (.inVar elemVar setVar) ↔
      ∃ row rows, ρ.lookupElem? elemVar = some row ∧ ρ.lookupSet? setVar = some rows ∧ rows row := by
  cases hElem : ρ.lookupElem? elemVar <;> cases hSet : ρ.lookupSet? setVar <;> simp [denoteMembership, hElem, hSet]

@[simp] theorem denoteMembership_or (ρ : SetLanguage.Env) (φ ψ : MembershipFormula) :
    denoteMembership ρ (.or φ ψ) ↔ denoteMembership ρ φ ∨ denoteMembership ρ ψ := Iff.rfl

@[simp] theorem denoteMembership_eqConst_bindElem (ρ : SetLanguage.Env) (x : VarName) (row row₀ : Row) :
    denoteMembership (ρ.bindElem x row) (.eqConst x row₀) ↔ row = row₀ := by
  simp [denoteMembership]

@[simp] theorem denoteMembership_evalClosedBool (ρ : SetLanguage.Env) (expr : Expr) :
    denoteMembership ρ (.evalClosedBool expr) ↔
      Expr.eval expr = some (.scalar (.bool true)) := Iff.rfl

@[simp] theorem denoteMembership_satisfiesPredicate_bindElem (ρ : SetLanguage.Env)
    (source : VarName) (predicate : Expr) (row : Row) :
    denoteMembership (ρ.bindElem source row) (.satisfiesPredicate source predicate) ↔
      Semantics.satisfiesPredicate source predicate row.visible = some true := by
  simp [denoteMembership]

@[simp] theorem denoteMembership_eqDeleted_bindElem₂ (ρ : SetLanguage.Env)
    (outVar source : VarName) (txnId : TxnId) (out src : Row) (hNe : outVar ≠ source) :
    denoteMembership ((ρ.bindElem outVar out).bindElem source src) (.eqDeleted outVar source txnId) ↔
      out = src.markDeleted txnId := by
  have hLookup :
      (((ρ.bindElem outVar out).bindElem source src).lookupElem? outVar) = some out := by
    rw [SetLanguage.Env.lookupElem_bindElem_ne (ρ := ρ.bindElem outVar out)
      (x := source) (y := outVar) (row := src) hNe.symm]
    simp
  rw [denoteMembership, hLookup]
  simp

@[simp] theorem denoteMembership_eqUpdated_bindElem₂ (ρ : SetLanguage.Env)
    (outVar source : VarName) (txnId : TxnId) (updateExpr : Expr) (out src : Row) (hNe : outVar ≠ source) :
    denoteMembership ((ρ.bindElem outVar out).bindElem source src) (.eqUpdated outVar source txnId updateExpr) ↔
      ∃ updated,
        Expr.eval (Semantics.instantiateRecord source src.visible updateExpr) = some (.record updated) ∧
        out = src.overwrite txnId updated := by
  have hLookup :
      (((ρ.bindElem outVar out).bindElem source src).lookupElem? outVar) = some out := by
    rw [SetLanguage.Env.lookupElem_bindElem_ne (ρ := ρ.bindElem outVar out)
      (x := source) (y := outVar) (row := src) hNe.symm]
    simp
  rw [denoteMembership, hLookup]
  simp

@[simp] theorem lookupSet_bindElem (ρ : SetLanguage.Env) (x y : VarName) (row : Row) :
    (ρ.bindElem x row).lookupSet? y = ρ.lookupSet? y := by
  simp [SetLanguage.Env.lookupSet?, SetLanguage.Env.bindElem]

@[simp] theorem denoteMembership_inLocalDb_bindElem (ρ : SetLanguage.Env) (x : VarName) (row : Row) :
    denoteMembership (ρ.bindElem x row) (.inLocalDb x) ↔ ρ.localDb row := by
  unfold denoteMembership
  simp [SetLanguage.Env.lookupElem?, SetLanguage.Env.lookupElemList?, SetLanguage.Env.bindElem]

@[simp] theorem denoteMembership_inGlobalDb_bindElem (ρ : SetLanguage.Env) (x : VarName) (row : Row) :
    denoteMembership (ρ.bindElem x row) (.inGlobalDb x) ↔ ρ.globalDb row := by
  unfold denoteMembership
  simp [SetLanguage.Env.lookupElem?, SetLanguage.Env.lookupElemList?, SetLanguage.Env.bindElem]

theorem encodeOfRowsMembership_sound (ρ : SetLanguage.Env) (elemVar : VarName)
    (rows : Database) (row : Row) :
    denoteMembership (ρ.bindElem elemVar row) (encodeOfRowsMembership elemVar rows) ↔ row ∈ rows := by
  induction rows with
  | nil =>
      simp [encodeOfRowsMembership, denoteMembership]
  | cons head tail ih =>
      simp [encodeOfRowsMembership, ih]

theorem encodeSingletonMembership_sound (ρ : SetLanguage.Env) (elemVar : VarName)
    (row₀ row : Row) :
    denoteMembership (ρ.bindElem elemVar row) (encodeSingletonMembership elemVar row₀) ↔ row = row₀ := by
  simp [encodeSingletonMembership, denoteMembership]

theorem encodeOfRowsMembership_denote (ρ : SetLanguage.Env) (elemVar : VarName)
    (rows : Database) (row : Row) :
    denoteMembership (ρ.bindElem elemVar row) (encodeOfRowsMembership elemVar rows) ↔
      SetLanguage.denote ρ (SetLanguage.ofRows rows) row := by
  simp [encodeOfRowsMembership_sound, SetLanguage.ofRows, SetLanguage.denote]

theorem encodeSingletonMembership_denote (ρ : SetLanguage.Env) (elemVar : VarName)
    (row₀ row : Row) :
    denoteMembership (ρ.bindElem elemVar row) (encodeSingletonMembership elemVar row₀) ↔
      SetLanguage.denote ρ (SetLanguage.singleton row₀) row := by
  simp [encodeSingletonMembership_sound, SetLanguage.singleton, SetLanguage.denote]

theorem encodeDeleteMembership_sound (elemVar : VarName) (txnId : TxnId)
    (env : DbAppProgramLogic.Env) (source : VarName) (predicate : Expr)
    (db : Database) (row : Row) (hNe : elemVar ≠ source) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
      (encodeDeleteMembership elemVar txnId env source predicate) ↔
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
        (Transformer.deleteSetExpr txnId env source predicate) row := by
  sorry

theorem encodeUpdateMembership_sound (elemVar : VarName) (txnId : TxnId)
    (env : DbAppProgramLogic.Env) (source : VarName) (updateExpr predicate : Expr)
    (db : Database) (row : Row) (hNe : elemVar ≠ source) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
      (encodeUpdateMembership elemVar txnId env source updateExpr predicate) ↔
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
        (Transformer.updateSetExpr txnId env source updateExpr predicate) row := by
  sorry

theorem inferWriteMembership_sound (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (elemVar : VarName) (body : Semantics.Program) (φ : MembershipFormula)
    (db rows : Database) (row : Row)
    (hFormula : inferWriteMembership txnId env elemVar body = some φ)
    (hEffect : Transformer.inferEffect txnId env body db = some rows) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row) φ ↔
      row ∈ rows := by
  induction body generalizing env φ db rows row with
  | skip =>
      simp [inferWriteMembership, Transformer.inferEffect, Transformer.emptyEffect] at hFormula hEffect
      subst φ
      subst rows
      simp [denoteMembership]
  | letE x expr body ih =>
      rcases Transformer.infer_let_sound txnId env x expr body db rows hEffect with
        ⟨value, hEval, hBodyEff⟩
      simp [inferWriteMembership, hEval] at hFormula
      exact ih (env.insert x value) φ db rows row hFormula hBodyEff
  | ite cond thenBranch elseBranch ihThen ihElse =>
      rcases Transformer.infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
        ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
      · simp [inferWriteMembership, hCond] at hFormula
        exact ihThen env φ db rows row hFormula hThenEff
      · simp [inferWriteMembership, hCond] at hFormula
        exact ihElse env φ db rows row hFormula hElseEff
  | seq left right ihLeft ihRight =>
      cases hLeft : inferWriteMembership txnId env elemVar left with
      | none =>
          simp [inferWriteMembership, hLeft] at hFormula
      | some φLeft =>
          cases hRight : inferWriteMembership txnId env elemVar right with
          | none =>
              simp [inferWriteMembership, hLeft, hRight] at hFormula
          | some φRight =>
              simp [inferWriteMembership, hLeft, hRight] at hFormula
              subst φ
              rcases Transformer.infer_seq_sound txnId env left right db rows hEffect with
                ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
              have hDenLeft := ihLeft env φLeft db rowsLeft row hLeft hLeftEff
              have hDenRight := ihRight env φRight db rowsRight row hRight hRightEff
              simp [denoteMembership_or, hDenLeft, hDenRight, hRows]
  | insert expr =>
      cases hEval : Transformer.evalInEnv env expr with
      | none =>
          simp [inferWriteMembership, hEval] at hFormula
      | some value =>
          cases value with
          | scalar scalar =>
              simp [inferWriteMembership, hEval] at hFormula
          | set records =>
              simp [inferWriteMembership, hEval] at hFormula
          | record record =>
              simp [inferWriteMembership, hEval] at hFormula
              subst φ
              rcases Transformer.infer_insert_sound txnId env expr db rows hEffect with
                ⟨record', hEval', hRows⟩
              have hEvalExpr :
                  Expr.eval (Transformer.instantiateExpr env [] expr) = some (.record record) := by
                simpa [Transformer.evalInEnv] using hEval
              rw [hEvalExpr] at hEval'
              injection hEval' with hRecord
              cases hRecord
              simp [encodeSingletonMembership_sound, hRows]
  | delete source predicate =>
      by_cases hNe : elemVar = source
      · simp [inferWriteMembership, hNe] at hFormula
      · simp [inferWriteMembership, hNe] at hFormula
        subst φ
        have hCollect := Transformer.infer_delete_sound txnId env source predicate db rows hEffect
        exact Iff.trans
          (encodeDeleteMembership_sound elemVar txnId env source predicate db row hNe)
          (Transformer.deleteSetExpr_sound txnId env source predicate db rows row hCollect)
  | select binder source predicate body ih =>
      simp [inferWriteMembership] at hFormula
  | update source updateExpr predicate =>
      by_cases hNe : elemVar = source
      · simp [inferWriteMembership, hNe] at hFormula
      · simp [inferWriteMembership, hNe] at hFormula
        subst φ
        have hCollect := Transformer.infer_update_sound txnId env source updateExpr predicate db rows hEffect
        exact Iff.trans
          (encodeUpdateMembership_sound elemVar txnId env source updateExpr predicate db row hNe)
          (Transformer.updateSetExpr_sound txnId env source updateExpr predicate db rows row hCollect)
  | foreach source doneVar elemVar' body ih =>
      simp [inferWriteMembership] at hFormula
  | foreachRuntime done remaining doneVar elemVar' body ih =>
      simp [inferWriteMembership] at hFormula
  | txn txnId' isolation body ih =>
      simp [inferWriteMembership] at hFormula
  | txnRuntime txnId' isolation localDb snapshot body ih =>
      simp [inferWriteMembership] at hFormula
  | par left right ihLeft ihRight =>
      simp [inferWriteMembership] at hFormula

theorem inferMembership_sound (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (elemVar : VarName) (body : Semantics.Program) (db : Database) (φ : MembershipFormula)
    (rows : Database) (row : Row)
    (hFormula : inferMembership txnId env elemVar db body = some φ)
    (hEffect : Transformer.inferEffect txnId env body db = some rows) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row) φ ↔
      row ∈ rows := by
  induction body generalizing env φ rows row with
  | skip =>
      simp [inferMembership, Transformer.inferEffect, Transformer.emptyEffect] at hFormula hEffect
      subst φ
      subst rows
      simp [denoteMembership]
  | letE x expr body ih =>
      rcases Transformer.infer_let_sound txnId env x expr body db rows hEffect with
        ⟨value, hEval, hBodyEff⟩
      simp [inferMembership, hEval] at hFormula
      exact ih (env.insert x value) φ rows row hFormula hBodyEff
  | ite cond thenBranch elseBranch ihThen ihElse =>
      rcases Transformer.infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
        ⟨hCond, hThenEff⟩ | ⟨hCond, hElseEff⟩
      · simp [inferMembership, hCond] at hFormula
        exact ihThen env φ rows row hFormula hThenEff
      · simp [inferMembership, hCond] at hFormula
        exact ihElse env φ rows row hFormula hElseEff
  | seq left right ihLeft ihRight =>
      cases hLeft : inferMembership txnId env elemVar db left with
      | none =>
          simp [inferMembership, hLeft] at hFormula
      | some φLeft =>
          cases hRight : inferMembership txnId env elemVar db right with
          | none =>
              simp [inferMembership, hLeft, hRight] at hFormula
          | some φRight =>
              simp [inferMembership, hLeft, hRight] at hFormula
              subst φ
              rcases Transformer.infer_seq_sound txnId env left right db rows hEffect with
                ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
              have hDenLeft := ihLeft env φLeft rowsLeft row hLeft hLeftEff
              have hDenRight := ihRight env φRight rowsRight row hRight hRightEff
              simp [denoteMembership_or, hDenLeft, hDenRight, hRows]
  | insert expr =>
      cases hEval : Transformer.evalInEnv env expr with
      | none =>
          simp [inferMembership, hEval] at hFormula
      | some value =>
          cases value with
          | scalar scalar =>
              simp [inferMembership, hEval] at hFormula
          | set records =>
              simp [inferMembership, hEval] at hFormula
          | record record =>
              simp [inferMembership, hEval] at hFormula
              subst φ
              rcases Transformer.infer_insert_sound txnId env expr db rows hEffect with
                ⟨record', hEval', hRows⟩
              have hEvalExpr :
                  Expr.eval (Transformer.instantiateExpr env [] expr) = some (.record record) := by
                simpa [Transformer.evalInEnv] using hEval
              rw [hEvalExpr] at hEval'
              injection hEval' with hRecord
              cases hRecord
              simp [encodeSingletonMembership_sound, hRows]
  | delete source predicate =>
      by_cases hNe : elemVar = source
      · simp [inferMembership, hNe] at hFormula
      · simp [inferMembership, hNe] at hFormula
        subst φ
        have hCollect := Transformer.infer_delete_sound txnId env source predicate db rows hEffect
        exact Iff.trans
          (encodeDeleteMembership_sound elemVar txnId env source predicate db row hNe)
          (Transformer.deleteSetExpr_sound txnId env source predicate db rows row hCollect)
  | select binder source predicate body ih =>
      rcases Transformer.infer_select_sound txnId env binder source predicate body db rows hEffect with
        ⟨selected, hSelect, hBodyEff⟩
      simp [inferMembership, hSelect] at hFormula
      exact ih (env.insert binder (.set selected)) φ rows row hFormula hBodyEff
  | update source updateExpr predicate =>
      by_cases hNe : elemVar = source
      · simp [inferMembership, hNe] at hFormula
      · simp [inferMembership, hNe] at hFormula
        subst φ
        have hCollect := Transformer.infer_update_sound txnId env source updateExpr predicate db rows hEffect
        exact Iff.trans
          (encodeUpdateMembership_sound elemVar txnId env source updateExpr predicate db row hNe)
          (Transformer.updateSetExpr_sound txnId env source updateExpr predicate db rows row hCollect)
  | foreach source doneVar elemVar' body ih =>
      simp [inferMembership] at hFormula
  | foreachRuntime done remaining doneVar elemVar' body ih =>
      simp [inferMembership] at hFormula
  | txn txnId' isolation body ih =>
      simp [inferMembership] at hFormula
  | txnRuntime txnId' isolation localDb snapshot body ih =>
      simp [inferMembership] at hFormula
  | par left right ihLeft ihRight =>
      simp [inferMembership] at hFormula

mutual

  def inferForeachMembership (txnId : TxnId) (env : DbAppProgramLogic.Env)
      (outVar doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
      (done remaining : SetLit) : Option MembershipFormula :=
    match remaining with
    | [] => some .bot
    | current :: rest => do
        let φCurrent ← inferMembershipFull txnId (Transformer.foreachEnv env doneVar elemVar done current)
          outVar body db
        let φRest ← inferForeachMembership txnId env outVar doneVar elemVar body db
          (done ++ [current]) rest
        pure (.or φCurrent φRest)

  /-- Compile a full transaction body into a row-membership formula. The encoding is still
  db-dependent because `select` and `foreach` inspect the current visible database. -/
  def inferMembershipFull (txnId : TxnId) (env : DbAppProgramLogic.Env)
      (outVar : VarName) (body : Semantics.Program) (db : Database) : Option MembershipFormula :=
    match body with
    | .skip => some .bot
    | .letE x expr body => do
        let value ← Transformer.evalInEnv env expr
        inferMembershipFull txnId (env.insert x value) outVar body db
    | .ite cond thenBranch elseBranch => do
        let .scalar (.bool b) ← Transformer.evalInEnv env cond | none
        if b then inferMembershipFull txnId env outVar thenBranch db
        else inferMembershipFull txnId env outVar elseBranch db
    | .seq left right => do
        let φLeft ← inferMembershipFull txnId env outVar left db
        let φRight ← inferMembershipFull txnId env outVar right db
        pure (.or φLeft φRight)
    | .insert expr => do
        let .record record ← Transformer.evalInEnv env expr | none
        pure (encodeSingletonMembership outVar (Row.fromInsert txnId record))
    | .delete source predicate =>
        if outVar = source then
          none
        else
          some (encodeDeleteMembership outVar txnId env source predicate)
    | .select binder source predicate body => do
        let selected ← Semantics.collectSelected db source (Transformer.instantiateExpr env [source] predicate)
        inferMembershipFull txnId (env.insert binder (.set selected)) outVar body db
    | .update source updateExpr predicate =>
        if outVar = source then
          none
        else
          some (encodeUpdateMembership outVar txnId env source updateExpr predicate)
    | .foreach source doneVar elemVar body => do
        let .set records ← Transformer.evalInEnv env source | none
        inferForeachMembership txnId env outVar doneVar elemVar body db [] records
    | .foreachRuntime done remaining doneVar elemVar body => do
        let .set doneRecords ← Transformer.evalInEnv env done | none
        let .set remainingRecords ← Transformer.evalInEnv env remaining | none
        inferForeachMembership txnId env outVar doneVar elemVar body db doneRecords remainingRecords
    | _ => none

end

def MembershipEncodable (outVar : VarName) : Semantics.Program → Prop
  | .skip => True
  | .letE _ _ body => MembershipEncodable outVar body
  | .ite _ thenBranch elseBranch =>
      MembershipEncodable outVar thenBranch ∧ MembershipEncodable outVar elseBranch
  | .seq left right =>
      MembershipEncodable outVar left ∧ MembershipEncodable outVar right
  | .insert _ => True
  | .delete source _ => outVar ≠ source
  | .select _ _ _ body => MembershipEncodable outVar body
  | .update source _ _ => outVar ≠ source
  | .foreach _ _ _ body => MembershipEncodable outVar body
  | .foreachRuntime _ _ _ _ body => MembershipEncodable outVar body
  | .txn _ _ _ => False
  | .txnRuntime _ _ _ _ _ => False
  | .par _ _ => False

def MembershipBaseEncodable (outVar : VarName) : Semantics.Program → Prop
  | .skip => True
  | .letE _ _ body => MembershipBaseEncodable outVar body
  | .ite _ thenBranch elseBranch =>
      MembershipBaseEncodable outVar thenBranch ∧ MembershipBaseEncodable outVar elseBranch
  | .seq left right =>
      MembershipBaseEncodable outVar left ∧ MembershipBaseEncodable outVar right
  | .insert _ => True
  | .delete source _ => outVar ≠ source
  | .select _ _ _ body => MembershipBaseEncodable outVar body
  | .update source _ _ => outVar ≠ source
  | .foreach _ _ _ _ => False
  | .foreachRuntime _ _ _ _ _ => False
  | .txn _ _ _ => False
  | .txnRuntime _ _ _ _ _ => False
  | .par _ _ => False

mutual

  theorem inferMembership_some_of_inferEffect_some (txnId : TxnId) (env : DbAppProgramLogic.Env)
      (outVar : VarName) (body : Semantics.Program) (db rows : Database)
      (hEnc : MembershipBaseEncodable outVar body)
      (hEffect : Transformer.inferEffect txnId env body db = some rows) :
      ∃ φ, inferMembership txnId env outVar db body = some φ := by
    induction body generalizing env rows with
    | skip =>
        exact ⟨.bot, by simp [inferMembership]⟩
    | letE x expr body ih =>
        simp [MembershipBaseEncodable] at hEnc
        rcases Transformer.infer_let_sound txnId env x expr body db rows hEffect with
          ⟨value, hEval, hBody⟩
        rcases ih (env.insert x value) rows hEnc hBody with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembership, hEval, hFormula]⟩
    | ite cond thenBranch elseBranch ihThen ihElse =>
        simp [MembershipBaseEncodable] at hEnc
        rcases hEnc with ⟨hThenEnc, hElseEnc⟩
        rcases Transformer.infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
          ⟨hCond, hThen⟩ | ⟨hCond, hElse⟩
        · rcases ihThen env rows hThenEnc hThen with ⟨φ, hFormula⟩
          exact ⟨φ, by simp [inferMembership, hCond, hFormula]⟩
        · rcases ihElse env rows hElseEnc hElse with ⟨φ, hFormula⟩
          exact ⟨φ, by simp [inferMembership, hCond, hFormula]⟩
    | seq left right ihLeft ihRight =>
        simp [MembershipBaseEncodable] at hEnc
        rcases hEnc with ⟨hLeftEnc, hRightEnc⟩
        rcases Transformer.infer_seq_sound txnId env left right db rows hEffect with
          ⟨rowsLeft, rowsRight, hLeft, hRight, hRows⟩
        rcases ihLeft env rowsLeft hLeftEnc hLeft with ⟨φLeft, hLeftFormula⟩
        rcases ihRight env rowsRight hRightEnc hRight with ⟨φRight, hRightFormula⟩
        exact ⟨.or φLeft φRight, by simp [inferMembership, hLeftFormula, hRightFormula]⟩
    | insert expr =>
        rcases Transformer.infer_insert_sound txnId env expr db rows hEffect with
          ⟨record, hEval, hRows⟩
        refine ⟨encodeSingletonMembership outVar (Row.fromInsert txnId record), ?_⟩
        simp [inferMembership, Transformer.evalInEnv, hEval]
    | delete source predicate =>
        simp [MembershipBaseEncodable] at hEnc
        exact ⟨encodeDeleteMembership outVar txnId env source predicate, by simp [inferMembership, hEnc]⟩
    | select binder source predicate body ih =>
        simp [MembershipBaseEncodable] at hEnc
        rcases Transformer.infer_select_sound txnId env binder source predicate body db rows hEffect with
          ⟨selected, hSelect, hBody⟩
        rcases ih (env.insert binder (.set selected)) rows hEnc hBody with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembership, hSelect, hFormula]⟩
    | update source updateExpr predicate =>
        simp [MembershipBaseEncodable] at hEnc
        exact ⟨encodeUpdateMembership outVar txnId env source updateExpr predicate, by
          simp [inferMembership, hEnc]⟩
    | foreach source doneVar elemVar body ih =>
        simp [MembershipBaseEncodable] at hEnc
    | foreachRuntime done remaining doneVar elemVar body ih =>
        simp [MembershipBaseEncodable] at hEnc
    | txn txnId' isolation body ih =>
        simp [MembershipBaseEncodable] at hEnc
    | txnRuntime txnId' isolation localDb snapshot body ih =>
        simp [MembershipBaseEncodable] at hEnc
    | par left right ihLeft ihRight =>
        simp [MembershipBaseEncodable] at hEnc

  theorem inferMembershipFull_some_of_inferEffect_some (txnId : TxnId) (env : DbAppProgramLogic.Env)
      (outVar : VarName) (body : Semantics.Program) (db rows : Database)
      (hEnc : MembershipEncodable outVar body)
      (hEffect : Transformer.inferEffect txnId env body db = some rows) :
      ∃ φ, inferMembershipFull txnId env outVar body db = some φ := by
    induction body generalizing env rows with
    | skip =>
        exact ⟨.bot, by simp [inferMembershipFull, inferMembership]⟩
    | letE x expr body ih =>
        simp [MembershipEncodable] at hEnc
        rcases Transformer.infer_let_sound txnId env x expr body db rows hEffect with
          ⟨value, hEval, hBody⟩
        rcases ih (env.insert x value) rows hEnc hBody with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembershipFull, inferMembership, hEval, hFormula]⟩
    | ite cond thenBranch elseBranch ihThen ihElse =>
        simp [MembershipEncodable] at hEnc
        rcases hEnc with ⟨hThenEnc, hElseEnc⟩
        rcases Transformer.infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
          ⟨hCond, hThen⟩ | ⟨hCond, hElse⟩
        · rcases ihThen env rows hThenEnc hThen with ⟨φ, hFormula⟩
          exact ⟨φ, by simp [inferMembershipFull, inferMembership, hCond, hFormula]⟩
        · rcases ihElse env rows hElseEnc hElse with ⟨φ, hFormula⟩
          exact ⟨φ, by simp [inferMembershipFull, inferMembership, hCond, hFormula]⟩
    | seq left right ihLeft ihRight =>
        simp [MembershipEncodable] at hEnc
        rcases hEnc with ⟨hLeftEnc, hRightEnc⟩
        rcases Transformer.infer_seq_sound txnId env left right db rows hEffect with
          ⟨rowsLeft, rowsRight, hLeft, hRight, hRows⟩
        rcases ihLeft env rowsLeft hLeftEnc hLeft with ⟨φLeft, hLeftFormula⟩
        rcases ihRight env rowsRight hRightEnc hRight with ⟨φRight, hRightFormula⟩
        exact ⟨.or φLeft φRight, by simp [inferMembershipFull, inferMembership, hLeftFormula, hRightFormula]⟩
    | insert expr =>
        rcases Transformer.infer_insert_sound txnId env expr db rows hEffect with
          ⟨record, hEval, hRows⟩
        refine ⟨encodeSingletonMembership outVar (Row.fromInsert txnId record), ?_⟩
        simp [inferMembershipFull, inferMembership, Transformer.evalInEnv, hEval]
    | delete source predicate =>
        simp [MembershipEncodable] at hEnc
        exact ⟨encodeDeleteMembership outVar txnId env source predicate, by
          simp [inferMembershipFull, inferMembership, hEnc]⟩
    | select binder source predicate body ih =>
        simp [MembershipEncodable] at hEnc
        rcases Transformer.infer_select_sound txnId env binder source predicate body db rows hEffect with
          ⟨selected, hSelect, hBody⟩
        rcases ih (env.insert binder (.set selected)) rows hEnc hBody with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembershipFull, inferMembership, hSelect, hFormula]⟩
    | update source updateExpr predicate =>
        simp [MembershipEncodable] at hEnc
        exact ⟨encodeUpdateMembership outVar txnId env source updateExpr predicate, by
          simp [inferMembershipFull, inferMembership, hEnc]⟩
    | foreach source doneVar elemVar body ih =>
        rcases Transformer.infer_foreach_sound txnId env source doneVar elemVar body db rows hEffect with
          ⟨records, hEval, hRuntime⟩
        have hForeachAux :
            ∀ (done remaining : SetLit) (rows' : Database),
              Transformer.inferEffect txnId env
                  (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
                  db = some rows' →
                ∃ φ', inferForeachMembership txnId env outVar doneVar elemVar body db done remaining = some φ' := by
          intro done remaining
          induction remaining generalizing done with
          | nil =>
              intro rows' hEffect'
              exact ⟨.bot, by simp [inferForeachMembership]⟩
          | cons current rest ihRemaining =>
              intro rows' hEffect'
              rcases Transformer.infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body db rows'
                  hEffect' with
                ⟨rowsCurrent, rowsRest, hCurrent, hRest, hRows⟩
              rcases ih (Transformer.foreachEnv env doneVar elemVar done current) rowsCurrent hEnc hCurrent with
                ⟨φCurrent, hCurrentFormula⟩
              rcases ihRemaining (done ++ [current]) rowsRest hRest with ⟨φRest, hRestFormula⟩
              exact ⟨.or φCurrent φRest, by simp [inferForeachMembership, hCurrentFormula, hRestFormula]⟩
        rcases hForeachAux [] records rows hRuntime with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembershipFull, hEval, hFormula]⟩
    | foreachRuntime done remaining doneVar elemVar body ih =>
        rcases Transformer.infer_foreachRuntime_sound txnId env done remaining doneVar elemVar body db rows hEffect with
          ⟨doneRecords, remainingRecords, hDoneEval, hRemainingEval, hRuntime⟩
        have hForeachAux :
            ∀ (done remaining : SetLit) (rows' : Database),
              Transformer.inferEffect txnId env
                  (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
                  db = some rows' →
                ∃ φ', inferForeachMembership txnId env outVar doneVar elemVar body db done remaining = some φ' := by
          intro done remaining
          induction remaining generalizing done with
          | nil =>
              intro rows' hEffect'
              exact ⟨.bot, by simp [inferForeachMembership]⟩
          | cons current rest ihRemaining =>
              intro rows' hEffect'
              rcases Transformer.infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body db rows'
                  hEffect' with
                ⟨rowsCurrent, rowsRest, hCurrent, hRest, hRows⟩
              rcases ih (Transformer.foreachEnv env doneVar elemVar done current) rowsCurrent hEnc hCurrent with
                ⟨φCurrent, hCurrentFormula⟩
              rcases ihRemaining (done ++ [current]) rowsRest hRest with ⟨φRest, hRestFormula⟩
              exact ⟨.or φCurrent φRest, by simp [inferForeachMembership, hCurrentFormula, hRestFormula]⟩
        rcases hForeachAux doneRecords remainingRecords rows hRuntime with ⟨φ, hFormula⟩
        exact ⟨φ, by simp [inferMembershipFull, hDoneEval, hRemainingEval, hFormula]⟩
    | txn txnId' isolation body =>
        simp [MembershipEncodable] at hEnc
    | txnRuntime txnId' isolation localDb snapshot body =>
        simp [MembershipEncodable] at hEnc
    | par left right =>
        simp [MembershipEncodable] at hEnc

end

theorem inferForeachMembership_some_of_inferEffect_some (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (outVar doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
    (done remaining : SetLit) (rows : Database)
    (hEnc : MembershipEncodable outVar body)
    (hEffect :
      Transformer.inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
        db = some rows) :
    ∃ φ, inferForeachMembership txnId env outVar doneVar elemVar body db done remaining = some φ := by
  induction remaining generalizing done rows with
  | nil =>
      exact ⟨.bot, by simp [inferForeachMembership]⟩
  | cons current rest ih =>
      rcases Transformer.infer_foreachRuntime_cons_sound txnId env done current rest doneVar elemVar body db rows
          hEffect with
        ⟨rowsCurrent, rowsRest, hCurrent, hRest, hRows⟩
      rcases inferMembershipFull_some_of_inferEffect_some txnId
          (Transformer.foreachEnv env doneVar elemVar done current) outVar body db rowsCurrent hEnc hCurrent with
        ⟨φCurrent, hCurrentFormula⟩
      rcases ih (done ++ [current]) rowsRest hRest with ⟨φRest, hRestFormula⟩
      exact ⟨.or φCurrent φRest, by simp [inferForeachMembership, hCurrentFormula, hRestFormula]⟩

private theorem inferForeachMembership_sound_of_body_sound (txnId : TxnId)
    (env : DbAppProgramLogic.Env) (outVar doneVar elemVar : VarName)
    (body : Semantics.Program) (db : Database)
    (bodySound :
      ∀ (env' : DbAppProgramLogic.Env) (φ : MembershipFormula) (rows : Database) (row : Row),
        inferMembershipFull txnId env' outVar body db = some φ →
          Transformer.inferEffect txnId env' body db = some rows →
            (denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ ↔
              row ∈ rows))
    (done remaining : SetLit) (φ : MembershipFormula) (rows : Database) (row : Row)
    (hFormula : inferForeachMembership txnId env outVar doneVar elemVar body db done remaining = some φ)
    (hEffect :
      Transformer.inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
        db = some rows) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ ↔
      row ∈ rows := by
  induction remaining generalizing done φ rows row with
  | nil =>
      simp [inferForeachMembership] at hFormula
      subst φ
      have hRows : rows = [] :=
        Transformer.infer_foreachRuntime_nil_sound txnId env done doneVar elemVar body db rows hEffect
      subst rows
      simp [denoteMembership]
  | cons current rest ih =>
      cases hCurrent :
          inferMembershipFull txnId (Transformer.foreachEnv env doneVar elemVar done current)
            outVar body db with
      | none =>
          simp [inferForeachMembership, hCurrent] at hFormula
      | some φCurrent =>
          cases hRest :
              inferForeachMembership txnId env outVar doneVar elemVar body db (done ++ [current]) rest with
          | none =>
              simp [inferForeachMembership, hCurrent, hRest] at hFormula
          | some φRest =>
              simp [inferForeachMembership, hCurrent, hRest] at hFormula
              subst φ
              rcases Transformer.infer_foreachRuntime_cons_sound txnId env done current rest
                  doneVar elemVar body db rows hEffect with
                ⟨rowsCurrent, rowsRest, hCurrentEff, hRestRuntime, hRows⟩
              have hDenCurrent :=
                bodySound (Transformer.foreachEnv env doneVar elemVar done current)
                  φCurrent rowsCurrent row hCurrent hCurrentEff
              have hDenRest :=
                ih (done ++ [current]) φRest rowsRest row hRest hRestRuntime
              simp [denoteMembership_or, hDenCurrent, hDenRest, hRows]

theorem inferMembershipFull_sound (txnId : TxnId) (env : DbAppProgramLogic.Env)
      (outVar : VarName) (body : Semantics.Program) (db : Database) (φ : MembershipFormula)
      (rows : Database) (row : Row)
      (hFormula : inferMembershipFull txnId env outVar body db = some φ)
      (hEffect : Transformer.inferEffect txnId env body db = some rows) :
      denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ ↔
        row ∈ rows := by
    induction body generalizing env φ rows row with
    | skip =>
        simp [inferMembershipFull, Transformer.inferEffect, Transformer.emptyEffect] at hFormula hEffect
        subst φ
        subst rows
        simp [denoteMembership]
    | letE x expr body ih =>
        rcases Transformer.infer_let_sound txnId env x expr body db rows hEffect with
          ⟨value, hEval, hBody⟩
        simp [inferMembershipFull, hEval] at hFormula
        exact ih (env.insert x value) φ rows row hFormula hBody
    | ite cond thenBranch elseBranch ihThen ihElse =>
        rcases Transformer.infer_ite_sound txnId env cond thenBranch elseBranch db rows hEffect with
          ⟨hCond, hThen⟩ | ⟨hCond, hElse⟩
        · simp [inferMembershipFull, hCond] at hFormula
          exact ihThen env φ rows row hFormula hThen
        · simp [inferMembershipFull, hCond] at hFormula
          exact ihElse env φ rows row hFormula hElse
    | seq left right ihLeft ihRight =>
        cases hLeft : inferMembershipFull txnId env outVar left db with
        | none =>
            simp [inferMembershipFull, hLeft] at hFormula
        | some φLeft =>
            cases hRight : inferMembershipFull txnId env outVar right db with
            | none =>
                simp [inferMembershipFull, hLeft, hRight] at hFormula
            | some φRight =>
                simp [inferMembershipFull, hLeft, hRight] at hFormula
                subst φ
                rcases Transformer.infer_seq_sound txnId env left right db rows hEffect with
                  ⟨rowsLeft, rowsRight, hLeftEff, hRightEff, hRows⟩
                have hDenLeft := ihLeft env φLeft rowsLeft row hLeft hLeftEff
                have hDenRight := ihRight env φRight rowsRight row hRight hRightEff
                simp [denoteMembership_or, hDenLeft, hDenRight, hRows]
    | insert expr =>
        cases hEval : Transformer.evalInEnv env expr with
        | none =>
            simp [inferMembershipFull, hEval] at hFormula
        | some value =>
            cases value with
            | scalar scalar =>
                simp [inferMembershipFull, hEval] at hFormula
            | set records =>
                simp [inferMembershipFull, hEval] at hFormula
            | record record =>
                simp [inferMembershipFull, hEval] at hFormula
                subst φ
                rcases Transformer.infer_insert_sound txnId env expr db rows hEffect with
                  ⟨record', hEval', hRows⟩
                have hEvalExpr :
                    Expr.eval (Transformer.instantiateExpr env [] expr) = some (.record record) := by
                  simpa [Transformer.evalInEnv] using hEval
                rw [hEvalExpr] at hEval'
                injection hEval' with hRecord
                cases hRecord
                simp [encodeSingletonMembership_sound, hRows]
    | delete source predicate =>
        by_cases hNe : outVar = source
        · simp [inferMembershipFull, hNe] at hFormula
        · simp [inferMembershipFull, hNe] at hFormula
          subst φ
          have hCollect := Transformer.infer_delete_sound txnId env source predicate db rows hEffect
          exact Iff.trans
            (encodeDeleteMembership_sound outVar txnId env source predicate db row hNe)
            (Transformer.deleteSetExpr_sound txnId env source predicate db rows row hCollect)
    | select binder source predicate body ih =>
        rcases Transformer.infer_select_sound txnId env binder source predicate body db rows hEffect with
          ⟨selected, hSelect, hBody⟩
        simp [inferMembershipFull, hSelect] at hFormula
        exact ih (env.insert binder (.set selected)) φ rows row hFormula hBody
    | update source updateExpr predicate =>
        by_cases hNe : outVar = source
        · simp [inferMembershipFull, hNe] at hFormula
        · simp [inferMembershipFull, hNe] at hFormula
          subst φ
          have hCollect := Transformer.infer_update_sound txnId env source updateExpr predicate db rows hEffect
          exact Iff.trans
            (encodeUpdateMembership_sound outVar txnId env source updateExpr predicate db row hNe)
            (Transformer.updateSetExpr_sound txnId env source updateExpr predicate db rows row hCollect)
    | foreach source doneVar elemVar body ih =>
        rcases Transformer.infer_foreach_sound txnId env source doneVar elemVar body db rows hEffect with
          ⟨records, hEval, hRuntimeEff⟩
        simp [inferMembershipFull, hEval] at hFormula
        exact inferForeachMembership_sound_of_body_sound txnId env outVar doneVar elemVar body db
          ih [] records φ rows row hFormula hRuntimeEff
    | foreachRuntime done remaining doneVar elemVar body ih =>
        rcases Transformer.infer_foreachRuntime_sound txnId env done remaining doneVar elemVar body db rows hEffect with
          ⟨doneRecords, remainingRecords, hDoneEval, hRemainingEval, hRuntimeEff⟩
        simp [inferMembershipFull, hDoneEval, hRemainingEval] at hFormula
        exact inferForeachMembership_sound_of_body_sound txnId env outVar doneVar elemVar body db
          ih doneRecords remainingRecords φ rows row hFormula hRuntimeEff
    | txn txnId' isolation body =>
        have hFormula' : inferMembership txnId env outVar db (.txn txnId' isolation body) = some φ := by
          simpa [inferMembershipFull] using hFormula
        exact inferMembership_sound txnId env outVar (.txn txnId' isolation body) db φ rows row hFormula' hEffect
    | txnRuntime txnId' isolation localDb snapshot body =>
        have hFormula' :
            inferMembership txnId env outVar db (.txnRuntime txnId' isolation localDb snapshot body) = some φ := by
          simpa [inferMembershipFull] using hFormula
        exact inferMembership_sound txnId env outVar
          (.txnRuntime txnId' isolation localDb snapshot body) db φ rows row hFormula' hEffect
    | par left right =>
        have hFormula' : inferMembership txnId env outVar db (.par left right) = some φ := by
          simpa [inferMembershipFull] using hFormula
        exact inferMembership_sound txnId env outVar (.par left right) db φ rows row hFormula' hEffect

theorem inferMembershipFull_matches_inferSetEffect (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (outVar : VarName) (body : Semantics.Program) (db : Database)
    (φ : MembershipFormula) (s : SetLanguage.SetExpr) (rows : Database) (row : Row)
    (hFormula : inferMembershipFull txnId env outVar body db = some φ)
    (hSet : Transformer.inferSetEffect txnId env body db = some s)
    (hEffect : Transformer.inferEffect txnId env body db = some rows) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ ↔
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] db) s row := by
  have hMembership :=
    inferMembershipFull_sound txnId env outVar body db φ rows row hFormula hEffect
  have hSetDenotation :=
    Transformer.inferSetEffect_sound txnId env body db s rows row hSet hEffect
  exact Iff.trans hMembership hSetDenotation.symm

theorem inferMembershipFull_implies_weakened_setEffect (I : Assertion) (absVar : VarName)
    (txnId : TxnId) (env : DbAppProgramLogic.Env) (outVar : VarName)
    (body : Semantics.Program) (db : Database)
    (φ : MembershipFormula) (s : SetLanguage.SetExpr) (rows : Database) (row : Row)
    (hInv : I db)
    (hFormula : inferMembershipFull txnId env outVar body db = some φ)
    (hSet : Transformer.inferSetEffect txnId env body db = some s)
    (hEffect : Transformer.inferEffect txnId env body db = some rows)
    (hMem : denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ) :
    SetLanguage.denote
      (SetLanguage.Env.ofDatabases [] db)
      (SetLanguage.weakenToInvariant absVar (Transformer.assertionFormula I) s)
      row := by
  have hRows :
      row ∈ rows := (inferMembershipFull_sound txnId env outVar body db φ rows row hFormula hEffect).1 hMem
  exact Transformer.inferSetEffect_weaken_overapprox I absVar txnId env body db s rows
    hInv hSet hEffect row hRows

theorem inferForeachMembership_sound (txnId : TxnId) (env : DbAppProgramLogic.Env)
    (outVar doneVar elemVar : VarName) (body : Semantics.Program) (db : Database)
    (done remaining : SetLit) (φ : MembershipFormula) (rows : Database) (row : Row)
    (hFormula : inferForeachMembership txnId env outVar doneVar elemVar body db done remaining = some φ)
    (hEffect :
      Transformer.inferEffect txnId env
        (.foreachRuntime (Expr.setLit done) (Expr.setLit remaining) doneVar elemVar body)
        db = some rows) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem outVar row) φ ↔
      row ∈ rows := by
  exact inferForeachMembership_sound_of_body_sound txnId env outVar doneVar elemVar body db
    (fun env' φ rows row hFormula hEffect =>
      inferMembershipFull_sound txnId env' outVar body db φ rows row hFormula hEffect)
    done remaining φ rows row hFormula hEffect

theorem encodeSetExprMembership_sound (ρ : SetLanguage.Env) (elemVar : VarName)
    (s : SetLanguage.SetExpr) (φ : MembershipFormula) (row : Row)
    (hEncode : encodeSetExprMembership elemVar s = some φ) :
    denoteMembership (ρ.bindElem elemVar row) φ ↔
      SetLanguage.denote ρ s row := by
  simp [encodeSetExprMembership] at hEncode

end FirstOrder

end DbAppProgramLogic
