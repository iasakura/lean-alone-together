import DbAppProgramLogic.Transformer

namespace DbAppProgramLogic

namespace FirstOrder

abbrev Env := DbAppProgramLogic.Env

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
  deriving Inhabited

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

def encodeSetExprMembership (elemVar : VarName) : SetLanguage.SetExpr → Option MembershipFormula
  | .var setVar => some (.inVar elemVar setVar)
  | .localDb => some (.inLocalDb elemVar)
  | .globalDb => some (.inGlobalDb elemVar)
  | .union s₁ s₂ => do
      let φ₁ ← encodeSetExprMembership elemVar s₁
      let φ₂ ← encodeSetExprMembership elemVar s₂
      pure (.or φ₁ φ₂)
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
  have hOut : Transformer.defaultOutVar source ≠ source := Transformer.defaultOutVar_ne source
  constructor
  · intro h
    simp [encodeDeleteMembership, denoteMembership] at h
    rcases h with ⟨mid, hMid, hPred, hEq⟩
    have hLookup :
        ((((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row).bindElem source mid).lookupElem? elemVar) =
          some row := by
      rw [SetLanguage.Env.lookupElem_bindElem_ne
        (ρ := (SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
        (x := source) (y := elemVar) (row := mid) hNe.symm]
      simp
    have hRow :
        row = mid.markDeleted txnId := by
      simpa [hLookup] using hEq
    simp [Transformer.deleteSetExpr, Transformer.deleteSetExprWith, Transformer.rowPredicateFormula,
      SetLanguage.denote, SetLanguage.empty, hOut]
    refine ⟨mid, ?_, hPred, hRow⟩
    simpa [SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using hMid
  · intro h
    simp [Transformer.deleteSetExpr, Transformer.deleteSetExprWith, Transformer.rowPredicateFormula,
      SetLanguage.denote, SetLanguage.empty, hOut] at h
    rcases h with ⟨mid, hMid, hPred, hRow⟩
    have hLookup :
        ((((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row).bindElem source mid).lookupElem? elemVar) =
          some row := by
      rw [SetLanguage.Env.lookupElem_bindElem_ne
        (ρ := (SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
        (x := source) (y := elemVar) (row := mid) hNe.symm]
      simp
    simp [encodeDeleteMembership, denoteMembership]
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using hMid
    · simpa [hLookup] using hRow

theorem encodeUpdateMembership_sound (elemVar : VarName) (txnId : TxnId)
    (env : DbAppProgramLogic.Env) (source : VarName) (updateExpr predicate : Expr)
    (db : Database) (row : Row) (hNe : elemVar ≠ source) :
    denoteMembership ((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
      (encodeUpdateMembership elemVar txnId env source updateExpr predicate) ↔
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
        (Transformer.updateSetExpr txnId env source updateExpr predicate) row := by
  have hOut : Transformer.defaultOutVar source ≠ source := Transformer.defaultOutVar_ne source
  constructor
  · intro h
    simp [encodeUpdateMembership, denoteMembership] at h
    rcases h with ⟨mid, hMid, hPred, hEq⟩
    have hLookup :
        ((((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row).bindElem source mid).lookupElem? elemVar) =
          some row := by
      rw [SetLanguage.Env.lookupElem_bindElem_ne
        (ρ := (SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
        (x := source) (y := elemVar) (row := mid) hNe.symm]
      simp
    have hRow :
        ∃ updated,
          Expr.eval
              (Semantics.instantiateRecord source mid.visible
                (Transformer.instantiateExpr env [source] updateExpr)) =
            some (.record updated) ∧
          row = mid.overwrite txnId updated := by
      simpa [hLookup] using hEq
    simp [Transformer.updateSetExpr, Transformer.updateSetExprWith, Transformer.rowPredicateFormula,
      SetLanguage.denote, SetLanguage.empty, hOut]
    refine ⟨mid, ?_, hPred, hRow⟩
    simpa [SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using hMid
  · intro h
    simp [Transformer.updateSetExpr, Transformer.updateSetExprWith, Transformer.rowPredicateFormula,
      SetLanguage.denote, SetLanguage.empty, hOut] at h
    rcases h with ⟨mid, hMid, hPred, hRow⟩
    have hLookup :
        ((((SetLanguage.Env.ofDatabases [] db).bindElem elemVar row).bindElem source mid).lookupElem? elemVar) =
          some row := by
      rw [SetLanguage.Env.lookupElem_bindElem_ne
        (ρ := (SetLanguage.Env.ofDatabases [] db).bindElem elemVar row)
        (x := source) (y := elemVar) (row := mid) hNe.symm]
      simp
    simp [encodeUpdateMembership, denoteMembership]
    refine ⟨mid, ?_, hPred, ?_⟩
    · simpa [SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using hMid
    · simpa [hLookup] using hRow

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

theorem encodeSetExprMembership_sound (ρ : SetLanguage.Env) (elemVar : VarName)
    (s : SetLanguage.SetExpr) (φ : MembershipFormula) (row : Row)
    (hEncode : encodeSetExprMembership elemVar s = some φ) :
    denoteMembership (ρ.bindElem elemVar row) φ ↔
      SetLanguage.denote ρ s row := by
  induction s generalizing φ row with
  | var setVar =>
      simp [encodeSetExprMembership] at hEncode
      subst φ
      simp [denoteMembership, SetLanguage.denote, SetLanguage.Env.bindElem,
        SetLanguage.Env.lookupElem?, SetLanguage.Env.lookupElemList?, SetLanguage.Env.lookupSet?]
      cases hLookup : SetLanguage.Env.lookupSetList? ρ.setVars setVar <;> simp [hLookup]
  | localDb =>
      simp [encodeSetExprMembership] at hEncode
      subst φ
      exact denoteMembership_inLocalDb_bindElem ρ elemVar row
  | globalDb =>
      simp [encodeSetExprMembership] at hEncode
      subst φ
      exact denoteMembership_inGlobalDb_bindElem ρ elemVar row
  | comprehension x φ0 =>
      simp [encodeSetExprMembership] at hEncode
  | existsSet x ψ s ih =>
      simp [encodeSetExprMembership] at hEncode
  | bind s₁ x s₂ ih₁ ih₂ =>
      simp [encodeSetExprMembership] at hEncode
  | ite φ0 s₁ s₂ ih₁ ih₂ =>
      simp [encodeSetExprMembership] at hEncode
  | union s₁ s₂ ih₁ ih₂ =>
      cases hLeft : encodeSetExprMembership elemVar s₁ with
      | none =>
          simp [encodeSetExprMembership, hLeft] at hEncode
      | some φLeft =>
          cases hRight : encodeSetExprMembership elemVar s₂ with
          | none =>
              simp [encodeSetExprMembership, hLeft, hRight] at hEncode
          | some φRight =>
              simp [encodeSetExprMembership, hLeft, hRight] at hEncode
              subst φ
              simp [denoteMembership_or, SetLanguage.denote_union, ih₁ _ _ hLeft, ih₂ _ _ hRight]

end FirstOrder

end DbAppProgramLogic
