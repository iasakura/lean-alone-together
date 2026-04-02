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

end FirstOrder

end DbAppProgramLogic
