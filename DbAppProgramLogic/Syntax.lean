namespace DbAppProgramLogic

/-!
Surface and runtime syntax for the core language `T`.

The same `Command` datatype contains both user-facing constructors such as `txn` and `foreach`, and
runtime-only constructors such as `txnRuntime` and `foreachRuntime` that appear only in the small-
step semantics.
-/

abbrev VarName := String
abbrev FieldName := String
abbrev TxnId := Nat

inductive BinOp where
  | add
  | sub
  | le
  | ge
  | eq
  deriving Repr, DecidableEq, Inhabited

inductive ScalarLit where
  | int : Int → ScalarLit
  | bool : Bool → ScalarLit
  deriving Repr, DecidableEq, Inhabited

structure RecordLit where
  fields : List (FieldName × ScalarLit)
  deriving Repr, DecidableEq, Inhabited

abbrev SetLit := List RecordLit

inductive Literal where
  | scalar : ScalarLit → Literal
  | record : RecordLit → Literal
  | set : SetLit → Literal
  deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | lit : Literal → Expr
  | var : VarName → Expr
  | proj : Expr → FieldName → Expr
  | record : List (FieldName × Expr) → Expr
  | withUpdates : Expr → List (FieldName × Expr) → Expr
  | binop : BinOp → Expr → Expr → Expr
  deriving Repr, Inhabited

namespace Expr

def int (n : Int) : Expr :=
  .lit (.scalar (.int n))

def bool (b : Bool) : Expr :=
  .lit (.scalar (.bool b))

def recordLit (fields : List (FieldName × ScalarLit)) : Expr :=
  .lit (.record ⟨fields⟩)

def setLit (records : SetLit) : Expr :=
  .lit (.set records)

end Expr

/--
Core syntax for the paper's language `T`.

`σ` is the semantic type used by runtime transaction nodes to store local/global state snapshots.
The surface syntax itself does not commit to any particular representation.
-/
inductive Command (ι : Type) (σ : Type) where
  | skip
  | letE : VarName → Expr → Command ι σ → Command ι σ
  | ite : Expr → Command ι σ → Command ι σ → Command ι σ
  | seq : Command ι σ → Command ι σ → Command ι σ
  | insert : Expr → Command ι σ
  | delete : VarName → Expr → Command ι σ
  | select : VarName → VarName → Expr → Command ι σ → Command ι σ
  | update : VarName → Expr → Expr → Command ι σ
  | foreach : Expr → VarName → VarName → Command ι σ → Command ι σ
  | foreachRuntime : Expr → Expr → VarName → VarName → Command ι σ → Command ι σ
  | txn : TxnId → ι → Command ι σ → Command ι σ
  | txnRuntime : TxnId → ι → σ → σ → Command ι σ → Command ι σ
  | par : Command ι σ → Command ι σ → Command ι σ
  deriving Repr, Inhabited

namespace Command

def seqs [Inhabited ι] [Inhabited σ] : List (Command ι σ) → Command ι σ
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

end Command

abbrev SurfaceCommand (ι : Type) := Command ι PUnit

end DbAppProgramLogic
