import DbAppProgramLogic.Syntax

namespace DbAppProgramLogic

/-!
Small syntax sugar for writing example programs.

This file does not change the core language. It only provides lightweight expression and command
macros so tutorial files can read more like the intended handler code.
-/

syntax "v! " ident : term
macro_rules
  | `(v! $x:ident) => `(Expr.var $(Lean.quote x.getId.toString))

syntax "f! " ident "." ident : term
macro_rules
  | `(f! $x:ident.$field:ident) =>
      `(Expr.proj (Expr.var $(Lean.quote x.getId.toString)) $(Lean.quote field.getId.toString))

syntax "col(" ident "," ident ")" : term
macro_rules
  | `(col($x:ident, $field:ident)) =>
      `(Expr.proj (Expr.var $(Lean.quote x.getId.toString)) $(Lean.quote field.getId.toString))

syntax "i![" num "]" : term
macro_rules
  | `(i![$n:num]) => `(Expr.int $n)

infixl:65 " .+. " => fun lhs rhs => Expr.binop BinOp.add lhs rhs
infixl:65 " .-. " => fun lhs rhs => Expr.binop BinOp.sub lhs rhs
infix:50 " .==. " => fun lhs rhs => Expr.binop BinOp.eq lhs rhs
infix:50 " .>=. " => fun lhs rhs => Expr.binop BinOp.ge lhs rhs
infix:50 " .<=. " => fun lhs rhs => Expr.binop BinOp.le lhs rhs
infixr:35 " .&&. " => fun lhs rhs => Expr.binop BinOp.and lhs rhs
infixr:30 " .||. " => fun lhs rhs => Expr.binop BinOp.or lhs rhs

syntax term " with! " ident " := " term : term
macro_rules
  | `($base with! $field:ident := $rhs) =>
      `(Expr.withUpdates $base [($(Lean.quote field.getId.toString), $rhs)])

syntax "SKIP!" : term
macro_rules
  | `(SKIP!) => `(Command.skip)

syntax "INSERT! " term : term
macro_rules
  | `(INSERT! $expr) => `(Command.insert $expr)

syntax "UPDATE! " ident " SET " term " WHERE " term : term
macro_rules
  | `(UPDATE! $source:ident SET $updateExpr WHERE $predicate) =>
      `(Command.update
          $(Lean.quote source.getId.toString)
          $updateExpr
          $predicate)

/--
`Command.select selected row predicate body` reads more like a let-binding than SQL:
it binds the selected rows to `selected`, while `row` is only the predicate variable.
This syntax makes that distinction explicit.
-/
syntax "SELECTROWS! " ident " USING " ident " WHERE " term " DO " term : term
macro_rules
  | `(SELECTROWS! $binder:ident USING $source:ident WHERE $predicate DO $body) =>
      `(Command.select
          $(Lean.quote binder.getId.toString)
          $(Lean.quote source.getId.toString)
          $predicate
          $body)

/--
Lowercase alias used in tutorials when we want the command to read like a binding:
`let! rows = selectRows where row => p in body`.
-/
syntax "let!" ident " = " "selectRows" " where " ident " => " term " in " term : term
macro_rules
  | `(let! $binder:ident = selectRows where $source:ident => $predicate in $body) =>
      `(Command.select
          $(Lean.quote binder.getId.toString)
          $(Lean.quote source.getId.toString)
          $predicate
          $body)

/--
`Command.foreach source done elem body` iterates over `source`, exposing the current element as
`elem` and the already-processed prefix as `done`.
-/
syntax "FOREACH! " ident " IN " term " WITH " ident " DO " term : term
macro_rules
  | `(FOREACH! $elem:ident IN $source WITH $done:ident DO $body) =>
      `(Command.foreach
          $source
          $(Lean.quote done.getId.toString)
          $(Lean.quote elem.getId.toString)
          $body)

/--
Lowercase alias used in tutorials when we want the command to read like ordinary pseudocode.
-/
syntax "foreach!" ident " in " term " with " ident " do " term : term
macro_rules
  | `(foreach! $elem:ident in $source with $done:ident do $body) =>
      `(Command.foreach
          $source
          $(Lean.quote done.getId.toString)
          $(Lean.quote elem.getId.toString)
          $body)

syntax "IF! " term " THEN " term " ELSE " term : term
macro_rules
  | `(IF! $cond THEN $thenBranch ELSE $elseBranch) =>
      `(Command.ite $cond $thenBranch $elseBranch)

end DbAppProgramLogic
