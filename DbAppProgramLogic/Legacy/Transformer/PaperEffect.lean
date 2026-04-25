import DbAppProgramLogic.Transformer.Basic

/-!
Legacy paper-style symbolic effect inference.

`inferPaperEffect`/`inferPaperForeach` belong to the older "concrete VCG" line of development:
they are total recursive functions that try to materialize the paper-style effect for a closed
program. This is exactly the *wrong* direction for the inference judgment of Fig. 13 of the arxiv
extended version `1710.09844v2.pdf`, which is a relational *judgment* on derivations, not a
function on syntax.

The paper-aligned formalization in `DbAppProgramLogic/Transformer/Inference.lean` and
`InferenceSoundness.lean` supersedes these definitions. They are kept under `Legacy/` only so that
the legacy `Soundness.lean` (which still references them) keeps building.
-/

namespace DbAppProgramLogic

namespace Transformer

mutual

  private def inferPaperForeach (_txnId : TxnId) (_env : SymEnv)
      (_elemVar : VarName) (_body : Semantics.Program) (_sourceSet : SetLanguage.SetExpr) :
      Option SetLanguage.SetExpr := none

  /--
  Paper-style symbolic effect inference, following Fig. 8 more closely than `inferEffect`.

  In particular, `let` and `if` stay symbolic, and `SELECT` binds a symbolic set expression instead
  of concretely materializing rows from a specific database.
  -/
  def inferPaperEffect (txnId : TxnId) (env : SymEnv) :
      Semantics.Program → Option SetLanguage.SetExpr
    | .skip => some SetLanguage.empty
    | .letE x expr body =>
        inferPaperEffect txnId (env.insertScalar x (instantiateSymExpr env [] expr)) body
    | .ite cond thenBranch elseBranch => do
        let sThen ← inferPaperEffect txnId env thenBranch
        let sElse ← inferPaperEffect txnId env elseBranch
        let cond' := instantiateSymExpr env [] cond
        pure (SetLanguage.SetExpr.ite (formulaOfExpr { env with scalarVars := [] } cond') sThen sElse)
    | .seq left right => do
        let sLeft ← inferPaperEffect txnId env left
        let sRight ← inferPaperEffect txnId env right
        pure (SetLanguage.SetExpr.union sLeft sRight)
    | .insert expr =>
        some (insertedRowSet txnId env (instantiateSymExpr env [] expr))
    | .delete source predicate =>
        some (SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb (fun row =>
          if evalSymExprAtRow env source row (instantiateSymExpr env [source] predicate) =
              some (.scalar (.bool true)) then
            deletedRowSet txnId row
          else
            SetLanguage.empty))
    | .select binder source predicate body => do
        let selected := globalSelectionSet env source (instantiateSymExpr env [source] predicate)
        inferPaperEffect txnId (env.insertSet binder selected) body
    | .update source updateExpr predicate =>
        some (SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb (fun row =>
          if evalSymExprAtRow env source row (instantiateSymExpr env [source] predicate) =
              some (.scalar (.bool true)) then
            updatedRowSet txnId env source row (instantiateSymExpr env [source] updateExpr)
          else
            SetLanguage.empty))
    | .foreach source doneVar elemVar body => do
        inferPaperForeach txnId ((env.eraseSet doneVar).eraseScalar doneVar) elemVar body
          (← sourceSetExpr env source)
    | .foreachRuntime _done _remaining _doneVar _elemVar _body =>
        none
    | .txn .. => none
    | .txnRuntime .. => none
    | .par .. => none

end

/-- Closed form of `inferPaperEffect` on `insert` under the empty symbolic environment. -/
theorem inferPaperEffect_insert_empty (txnId : TxnId) (expr : Expr) :
    inferPaperEffect txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.insert expr) =
      some (insertedRowSet txnId { scalarVars := [], setVars := [] } expr) := by
  simp [inferPaperEffect, instantiateSymExpr]

/-- Closed form of `inferPaperEffect` on `delete` under the empty symbolic environment. -/
theorem inferPaperEffect_delete_empty (txnId : TxnId) (source : VarName) (predicate : Expr) :
    inferPaperEffect txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.delete source predicate) =
      some (deleteSetExpr txnId ([] : Env) source predicate) := by
  apply congrArg some
  funext localDb globalDb out
  apply propext
  constructor <;> intro h
  · rcases h with ⟨mid, hMid, hBody⟩
    refine ⟨mid, hMid, ?_⟩
    simpa [deleteSetExpr, deleteSetExprWith, rowPredicateFormula, instantiateExpr,
      instantiateSymExpr, evalSymExprAtRow, deletedRowSet, SetLanguage.singleton,
      SetLanguage.empty, satisfiesPredicate_eq_some_true_iff_eval_true] using hBody
  · rcases h with ⟨mid, hMid, hBody⟩
    refine ⟨mid, hMid, ?_⟩
    simpa [deleteSetExpr, deleteSetExprWith, rowPredicateFormula, instantiateExpr,
      instantiateSymExpr, evalSymExprAtRow, deletedRowSet, SetLanguage.singleton,
      SetLanguage.empty, satisfiesPredicate_eq_some_true_iff_eval_true] using hBody

@[simp] theorem inferPaperEffect_foreach_none (txnId : TxnId) (env : SymEnv)
    (source : Expr) (doneVar elemVar : VarName) (body : Semantics.Program) :
    inferPaperEffect txnId env (.foreach source doneVar elemVar body) = none := by
  simp [inferPaperEffect, inferPaperForeach]

@[simp] theorem inferPaperEffect_foreachRuntime_none (txnId : TxnId) (env : SymEnv)
    (done remaining : Expr) (doneVar elemVar : VarName) (body : Semantics.Program) :
    inferPaperEffect txnId env (.foreachRuntime done remaining doneVar elemVar body) = none := by
  simp [inferPaperEffect]

end Transformer

end DbAppProgramLogic
