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

/--
Symbolic environment for the paper-style state-transformer inference of §5.

Scalar variables are tracked as expressions, while set-valued binders introduced by `SELECT`
are tracked as explicit `SetExpr`s. This avoids the premature concrete evaluation performed by
`inferEffect`.
-/
structure SymEnv where
  scalarVars : List (VarName × Expr) := []
  setVars : List (VarName × SetLanguage.SetExpr) := []

namespace SymEnv

def lookupScalar? : SymEnv → VarName → Option Expr
  | ⟨[], _⟩, _ => none
  | ⟨(y, e) :: rest, sets⟩, x => if x = y then some e else lookupScalar? ⟨rest, sets⟩ x

def lookupSet? : SymEnv → VarName → Option SetLanguage.SetExpr
  | ⟨_, []⟩, _ => none
  | ⟨scalars, (y, s) :: rest⟩, x => if x = y then some s else lookupSet? ⟨scalars, rest⟩ x

def eraseScalar (env : SymEnv) (x : VarName) : SymEnv :=
  { env with scalarVars := env.scalarVars.filter (fun binding => binding.1 ≠ x) }

def eraseSet (env : SymEnv) (x : VarName) : SymEnv :=
  { env with setVars := env.setVars.filter (fun binding => binding.1 ≠ x) }

def insertScalar (env : SymEnv) (x : VarName) (e : Expr) : SymEnv :=
  { (env.eraseScalar x) with scalarVars := (x, e) :: (env.eraseScalar x).scalarVars }

def insertSet (env : SymEnv) (x : VarName) (s : SetLanguage.SetExpr) : SymEnv :=
  { (env.eraseSet x) with setVars := (x, s) :: (env.eraseSet x).setVars }

end SymEnv

/-- Substitute only scalar symbolic bindings into an expression. Set-valued bindings are handled
separately by the symbolic effect inference. -/
def instantiateSymExpr (env : SymEnv) (blocked : List VarName) (expr : Expr) : Expr :=
  env.scalarVars.foldr
    (fun (binding : VarName × Expr) acc =>
      if binding.1 ∈ blocked then acc else Expr.subst binding.1 binding.2 acc)
    expr

@[simp] theorem instantiateSymExpr_noScalars (setVars : List (VarName × SetLanguage.SetExpr))
    (blocked : List VarName) (expr : Expr) :
    instantiateSymExpr { scalarVars := [], setVars := setVars } blocked expr = expr := by
  simp [instantiateSymExpr]

private def instantiateElemVars (ρ : SetLanguage.Env) (expr : Expr) : Expr :=
  ρ.elemVars.foldr
    (fun (binding : VarName × Row) acc =>
      Expr.subst binding.1 (.lit (.record binding.2.visible)) acc)
    expr

/-- Evaluate an expression under the symbolic scalar environment and the row binders currently
introduced by a `SetExpr` denotation. -/
def evalExprInSetEnv (env : SymEnv) (ρ : SetLanguage.Env) (expr : Expr) : Option Value :=
  Expr.eval (instantiateElemVars ρ (instantiateSymExpr env [] expr))

/-- Interpret a boolean expression as a shallow `SetLanguage` formula. -/
def formulaOfExpr (env : SymEnv) (expr : Expr) : SetLanguage.Formula0 :=
  fun (_localDb _globalDb : SetLanguage.SetDenotation) =>
    Expr.eval (instantiateSymExpr env [] expr) = some (.scalar (.bool true))

def evalSymExprAtRow (env : SymEnv) (x : VarName) (row : Row) (expr : Expr) : Option Value :=
  Expr.eval (Semantics.instantiateRecord x row.visible (instantiateSymExpr env [x] expr))

def insertedRowSet (txnId : TxnId) (env : SymEnv) (expr : Expr) : SetLanguage.SetExpr :=
  fun (_localDb _globalDb : SetLanguage.SetDenotation) (row : Row) =>
    match Expr.eval (instantiateSymExpr env [] expr) with
    | some (.record record) => row = Row.fromInsert txnId record
    | _ => False

def deletedRowSet (txnId : TxnId) (src : Row) : SetLanguage.SetExpr :=
  SetLanguage.singleton (src.markDeleted txnId)

def updatedRowSet (txnId : TxnId) (env : SymEnv) (x : VarName) (src : Row) (updateExpr : Expr) :
    SetLanguage.SetExpr :=
  fun (_localDb _globalDb : SetLanguage.SetDenotation) (row : Row) =>
    match evalSymExprAtRow env x src updateExpr with
    | some (.record updated) => row = src.overwrite txnId updated
    | _ => False

def globalSelectionSet (env : SymEnv) (x : VarName) (predicate : Expr) :
    SetLanguage.SetExpr :=
  SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb (fun row =>
    if evalSymExprAtRow env x row predicate = some (.scalar (.bool true)) then
      SetLanguage.singleton row
    else
      SetLanguage.empty)

def sourceSetExpr (env : SymEnv) (source : Expr) : Option SetLanguage.SetExpr :=
  match instantiateSymExpr env [] source with
  | .var x => env.lookupSet? x
  | .lit (.set rows) =>
      some (fun (_localDb _globalDb : SetLanguage.SetDenotation) (row : Row) => row.visible ∈ rows)
  | _ => none

/-- Materialize a symbolic row-set against the current visible database by keeping the visible
projection of each committed row that satisfies the symbolic denotation. This is the bridge needed
to compare paper-style symbolic binders with the operational `SetLit` values used by `SELECT` and
`FOREACH`. -/
noncomputable def materializeRows (snapshot rows : Database) (s : SetLanguage.SetExpr) : SetLit :=
  by
    classical
    exact rows.foldr
      (fun row acc =>
        if SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshot) s row then
          row.visible :: acc
        else
          acc)
      []

noncomputable def materializeSet (visibleDb : Database) (s : SetLanguage.SetExpr) : SetLit :=
  materializeRows visibleDb visibleDb s

/-- Instantiate scalar symbolic bindings into a command. This mirrors `instantiateSymExpr`, but at
the command level so that paper-style symbolic environments can later be materialized into ordinary
transaction bodies before appealing to `LocalValid` lemmas such as `localValid_select`. -/
def instantiateScalarCommand (env : SymEnv) : Semantics.Program → Semantics.Program :=
  env.scalarVars.foldl (fun acc binding => Command.subst binding.1 binding.2 acc)

/-- Instantiate set-valued symbolic bindings into a command by materializing them against the
current visible database and substituting the resulting concrete `SetLit`. Using `foldl` keeps the
most recent binding (stored at the head of `setVars`) outermost, which makes the `insertSet`
equations line up with `Command.subst`. -/
noncomputable def instantiateSetCommand (env : SymEnv) (visibleDb : Database) :
    Semantics.Program → Semantics.Program :=
  env.setVars.foldl
    (fun acc binding => Command.subst binding.1 (.lit (.set (materializeSet visibleDb binding.2))) acc)

/-- Materialize the full symbolic environment into a concrete command at the current visible
database. -/
noncomputable def instantiateSymCommand (env : SymEnv) (visibleDb : Database)
    (cmd : Semantics.Program) : Semantics.Program :=
  instantiateSetCommand env visibleDb (instantiateScalarCommand env cmd)

/-- Denotation of `globalSelectionSet env source predicate` over an empty local context.
A row `r` lies in the symbolic selection iff it lies in the global database and the predicate,
evaluated under `env` with `source` bound to `r`, holds.

The bridge to surface forms based on `evalExprInSetEnv` / `Semantics.satisfiesPredicate` is
left to dedicated wrappers below; expressing the right-hand side via `evalSymExprAtRow` keeps
this lemma a pure unfolding of `globalSelectionSet`. -/
theorem globalSelectionSet_denote (env : SymEnv) (source : VarName) (predicate : Expr)
    (db : Database) (row : Row) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (globalSelectionSet env source predicate) row ↔
      row ∈ db ∧
        evalSymExprAtRow env source row predicate = some (.scalar (.bool true)) := by
  simp only [globalSelectionSet, SetLanguage.denote_bind,
    SetLanguage.denote_globalDb_ofDatabases]
  constructor
  · rintro ⟨mid, hMid, hBody⟩
    by_cases hPred :
        evalSymExprAtRow env source mid predicate = some (.scalar (.bool true))
    · simp [hPred, SetLanguage.denote, SetLanguage.singleton] at hBody
      subst hBody
      exact ⟨hMid, hPred⟩
    · simp [hPred, SetLanguage.denote, SetLanguage.empty] at hBody
  · rintro ⟨hMem, hPred⟩
    refine ⟨row, hMem, ?_⟩
    simp [hPred, SetLanguage.denote, SetLanguage.singleton]

theorem evalExprInSetEnv_closed_bindElem_eq_instantiateRecord
    (setVars : List (VarName × SetLanguage.SetExpr)) (source : VarName)
    (snapshot : Database) (row : Row) (expr : Expr) :
    evalExprInSetEnv { scalarVars := [], setVars := setVars }
      ((SetLanguage.Env.ofDatabases [] snapshot).bindElem source row) expr =
      Expr.eval (Semantics.instantiateRecord source row.visible expr) := by
  simp [evalExprInSetEnv, instantiateElemVars, SetLanguage.Env.ofDatabases,
    SetLanguage.Env.bindElem, instantiateSymExpr, Semantics.instantiateRecord]

theorem satisfiesPredicate_eq_some_true_iff_eval_true
    (source : VarName) (predicate : Expr) (record : RecordLit) :
    Semantics.satisfiesPredicate source predicate record = some true ↔
      Expr.eval (Semantics.instantiateRecord source record predicate) =
        some (.scalar (.bool true)) := by
  unfold Semantics.satisfiesPredicate
  cases hEval : Expr.eval (Semantics.instantiateRecord source record predicate) <;> simp [hEval]
  case some value =>
    cases value <;> simp [hEval]
    case scalar lit =>
      cases lit <;> simp [hEval]

/-- Closed-environment specialization of `globalSelectionSet_denote`. With no scalar/set
substitutions, `evalSymExprAtRow` reduces to evaluating the predicate against the row, which
matches `Semantics.satisfiesPredicate`. -/
theorem globalSelectionSet_closed_denote_iff (source : VarName) (predicate : Expr)
    (db : Database) (row : Row) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (globalSelectionSet { scalarVars := [], setVars := [] } source predicate) row ↔
      row ∈ db ∧ Semantics.satisfiesPredicate source predicate row.visible = some true := by
  rw [globalSelectionSet_denote]
  refine and_congr_right (fun _ => ?_)
  have hEvalSym :
      evalSymExprAtRow ({ scalarVars := [], setVars := [] } : SymEnv) source row predicate =
        Expr.eval (Semantics.instantiateRecord source row.visible predicate) := by
    simp [evalSymExprAtRow, instantiateSymExpr_noScalars]
  rw [hEvalSym, satisfiesPredicate_eq_some_true_iff_eval_true]

/-- Variant of `globalSelectionSet_closed_denote_iff` for non-empty `env`. The bridging
hypothesis `hEval` discharges the gap between the symbolic per-row evaluation
`evalSymExprAtRow env source row predicate` and the closed-form predicate evaluation. -/
theorem globalSelectionSet_denote_iff_of_eval
    (env : SymEnv) (source : VarName) (predicate : Expr)
    (db : Database) (row : Row)
    (hEval :
      evalSymExprAtRow env source row predicate =
        Expr.eval (Semantics.instantiateRecord source row.visible predicate)) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] db)
      (globalSelectionSet env source predicate) row ↔
      row ∈ db ∧ Semantics.satisfiesPredicate source predicate row.visible = some true := by
  rw [globalSelectionSet_denote]
  refine and_congr_right (fun _ => ?_)
  rw [hEval, satisfiesPredicate_eq_some_true_iff_eval_true]

theorem materializeRows_globalSelectionSet_eq_collectSelected
    (source : VarName) (predicate : Expr) (snapshot rows : Database) (selected : SetLit)
    (hSource : source ≠ "_row")
    (hSubset : ∀ row, row ∈ rows → row ∈ snapshot)
    (hSelect : Semantics.collectSelected rows source predicate = some selected) :
    materializeRows snapshot rows
      (globalSelectionSet { scalarVars := [], setVars := [] } source predicate) = selected := by
  classical
  induction rows generalizing selected with
  | nil =>
      simp [Semantics.collectSelected] at hSelect
      cases hSelect
      simp [materializeRows]
  | cons head tail ih =>
      cases hKeep : Semantics.satisfiesPredicate source predicate head.visible with
      | none =>
          have : False := by
            simp [Semantics.collectSelected, Semantics.collectSelected.go, hKeep] at hSelect
          exact False.elim this
      | some keep =>
          cases hGo : Semantics.collectSelected.go source predicate tail with
          | none =>
              have : False := by
                cases keep <;> simp [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] at hSelect
              exact False.elim this
          | some rest =>
              cases keep
              · have hEqSel : rest = selected := by
                  simpa [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] using hSelect
                subst selected
                have hHead :
                    ¬ SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshot)
                        (globalSelectionSet { scalarVars := [], setVars := [] } source predicate) head := by
                  intro hDenote
                  have := (globalSelectionSet_closed_denote_iff source predicate snapshot head).1 hDenote
                  have : some false = some true := hKeep.symm.trans this.2
                  cases this
                simp [materializeRows, hHead]
                refine ih rest ?_ hGo
                intro row hMem
                exact hSubset row (List.mem_cons_of_mem _ hMem)
              · have hEqSel : head.visible :: rest = selected := by
                  simpa [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] using hSelect
                subst selected
                have hHead :
                    SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshot)
                      (globalSelectionSet { scalarVars := [], setVars := [] } source predicate) head := by
                  exact (globalSelectionSet_closed_denote_iff source predicate snapshot head).2
                    ⟨hSubset head (by simp), by simpa [Semantics.satisfiesPredicate, hKeep]⟩
                simp [materializeRows, hHead]
                refine ih rest ?_ hGo
                intro row hMem
                exact hSubset row (List.mem_cons_of_mem _ hMem)

theorem materializeSet_globalSelectionSet_eq_collectSelected
    (source : VarName) (predicate : Expr) (db : Database) (selected : SetLit)
    (hSource : source ≠ "_row")
    (hSelect : Semantics.collectSelected db source predicate = some selected) :
    materializeSet db
      (globalSelectionSet { scalarVars := [], setVars := [] } source predicate) = selected := by
  exact materializeRows_globalSelectionSet_eq_collectSelected source predicate db db selected
    hSource (fun _ => id) hSelect

theorem materializeRows_globalSelectionSet_eq_collectSelected_of_eval
    (env : SymEnv) (source : VarName) (predicate : Expr)
    (snapshot rows : Database) (selected : SetLit)
    (hSubset : ∀ row, row ∈ rows → row ∈ snapshot)
    (hEval :
      ∀ row, row ∈ rows →
        evalSymExprAtRow env source row predicate =
          Expr.eval (Semantics.instantiateRecord source row.visible predicate))
    (hSelect : Semantics.collectSelected rows source predicate = some selected) :
    materializeRows snapshot rows (globalSelectionSet env source predicate) = selected := by
  classical
  induction rows generalizing selected with
  | nil =>
      simp [Semantics.collectSelected] at hSelect
      cases hSelect
      simp [materializeRows]
  | cons head tail ih =>
      cases hKeep : Semantics.satisfiesPredicate source predicate head.visible with
      | none =>
          have : False := by
            simp [Semantics.collectSelected, Semantics.collectSelected.go, hKeep] at hSelect
          exact False.elim this
      | some keep =>
          cases hGo : Semantics.collectSelected.go source predicate tail with
          | none =>
              have : False := by
                cases keep <;> simp [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] at hSelect
              exact False.elim this
          | some rest =>
              cases keep
              · have hEqSel : rest = selected := by
                  simpa [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] using hSelect
                subst selected
                have hHead :
                    ¬ SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshot)
                        (globalSelectionSet env source predicate) head := by
                  intro hDenote
                  have :=
                    (globalSelectionSet_denote_iff_of_eval env source predicate snapshot head
                      (hEval head (by simp))).1 hDenote
                  have : some false = some true := hKeep.symm.trans this.2
                  cases this
                simp [materializeRows, hHead]
                refine ih rest ?_ ?_ hGo
                · intro row hMem
                  exact hSubset row (List.mem_cons_of_mem _ hMem)
                · intro row hMem
                  exact hEval row (List.mem_cons_of_mem _ hMem)
              · have hEqSel : head.visible :: rest = selected := by
                  simpa [Semantics.collectSelected, Semantics.collectSelected.go, hKeep, hGo] using hSelect
                subst selected
                have hHead :
                    SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshot)
                      (globalSelectionSet env source predicate) head := by
                  exact (globalSelectionSet_denote_iff_of_eval env source predicate snapshot head
                    (hEval head (by simp))).2
                    ⟨hSubset head (by simp), by simpa [Semantics.satisfiesPredicate, hKeep]⟩
                simp [materializeRows, hHead]
                refine ih rest ?_ ?_ hGo
                · intro row hMem
                  exact hSubset row (List.mem_cons_of_mem _ hMem)
                · intro row hMem
                  exact hEval row (List.mem_cons_of_mem _ hMem)

theorem materializeSet_globalSelectionSet_eq_collectSelected_of_eval
    (env : SymEnv) (source : VarName) (predicate : Expr)
    (db : Database) (selected : SetLit)
    (hEval :
      ∀ row, row ∈ db →
        evalSymExprAtRow env source row predicate =
          Expr.eval (Semantics.instantiateRecord source row.visible predicate))
    (hSelect : Semantics.collectSelected db source predicate = some selected) :
    materializeSet db (globalSelectionSet env source predicate) = selected := by
  exact materializeRows_globalSelectionSet_eq_collectSelected_of_eval env source predicate db db selected
    (fun _ => id) hEval hSelect

theorem instantiateSetCommand_insertSet (env : SymEnv) (visibleDb : Database)
    (binder : VarName) (s : SetLanguage.SetExpr) (body : Semantics.Program) :
    instantiateSetCommand (env.insertSet binder s) visibleDb body =
      instantiateSetCommand (env.eraseSet binder) visibleDb
        (Command.subst binder (.lit (.set (materializeSet visibleDb s))) body) := by
  unfold instantiateSetCommand SymEnv.insertSet
  simp [SymEnv.eraseSet]

theorem instantiateScalarCommand_insertScalar (env : SymEnv)
    (x : VarName) (expr : Expr) (body : Semantics.Program) :
    instantiateScalarCommand (env.insertScalar x expr) body =
      instantiateScalarCommand (env.eraseScalar x) (Command.subst x expr body) := by
  unfold instantiateScalarCommand SymEnv.insertScalar
  simp [SymEnv.eraseScalar]

theorem instantiateSymCommand_insertSet (env : SymEnv) (visibleDb : Database)
    (binder : VarName) (s : SetLanguage.SetExpr) (body : Semantics.Program) :
    instantiateSymCommand (env.insertSet binder s) visibleDb body =
      instantiateSetCommand (env.eraseSet binder) visibleDb
        (Command.subst binder (.lit (.set (materializeSet visibleDb s)))
          (instantiateScalarCommand env body)) := by
  have hScalars :
      instantiateScalarCommand (env.insertSet binder s) body =
        instantiateScalarCommand env body := by
    simp [instantiateScalarCommand, SymEnv.insertSet, SymEnv.eraseSet]
  rw [instantiateSymCommand, instantiateSetCommand_insertSet, hScalars]

theorem instantiateSymCommand_insertScalar (env : SymEnv) (visibleDb : Database)
    (x : VarName) (expr : Expr) (body : Semantics.Program) :
    instantiateSymCommand (env.insertScalar x expr) visibleDb body =
      instantiateSetCommand (env.insertScalar x expr) visibleDb
        (instantiateScalarCommand (env.eraseScalar x) (Command.subst x expr body)) := by
  simp [instantiateSymCommand, instantiateScalarCommand_insertScalar]

/-!
`inferPaperEffect`/`inferPaperForeach` and their closed-form lemmas have moved to
`DbAppProgramLogic/Legacy/Transformer/PaperEffect.lean`. They were the wrong direction for the
inference judgment: a total recursive function on closed programs, instead of the relational
judgment of Fig. 13. The paper-aligned formalization in `Transformer/Inference.lean` and
`InferenceSoundness.lean` supersedes them.
-/

/-- Paper-style precondition from Theorem 5.1: the current local database is exactly the context
effect `Fctxt`, interpreted against the current visible database, and the visible database satisfies
the invariant `I`. -/
def transformerPre (I : Assertion) (Fctxt : SetLanguage.SetExpr) : BiAssertion :=
  fun localDb visibleDb =>
    (∀ row, SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) Fctxt row ↔ row ∈ localDb) ∧
      I visibleDb

/-- Paper-style postcondition from Theorem 5.1: the current local database is the union of the
incoming context effect and the newly inferred effect. -/
def transformerPost (Fctxt F : SetLanguage.SetExpr) : BiAssertion :=
  fun localDb visibleDb =>
    ∀ row,
      SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) (.union Fctxt F) row ↔
        row ∈ localDb

/-- Paper-style local soundness statement corresponding to Theorem 5.1. -/
def paperInferenceSound (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (body : Semantics.Program) (F : SetLanguage.SetExpr) : Prop :=
  Logic.LocalValid R txnId (transformerPre I Fctxt) body (transformerPost Fctxt F)

/-- Variant of `paperInferenceSound` that keeps the symbolic environment explicit. The command is
materialized against the current visible database before the `LocalValid` judgment is stated. This
is the form needed to recurse through `SELECT` and `FOREACH`, where the body is not executed
directly but after binding concrete sets computed from the current visible database. -/
def paperInferenceSoundEnv (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr)
    (env : SymEnv) (body : Semantics.Program) (F : SetLanguage.SetExpr) : Prop :=
  ∀ visibleDb,
    Logic.LocalValid R txnId (transformerPre I Fctxt)
      (instantiateSymCommand env visibleDb body)
      (transformerPost Fctxt F)

theorem paperInferenceSound_toEnvEmpty (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt F : SetLanguage.SetExpr) (body : Semantics.Program)
    (h : paperInferenceSound R txnId I Fctxt body F) :
    paperInferenceSoundEnv R txnId I Fctxt { scalarVars := [], setVars := [] } body F := by
  intro visibleDb
  simpa [paperInferenceSoundEnv, paperInferenceSound, instantiateSymCommand,
    instantiateSetCommand, instantiateScalarCommand] using h

theorem paperInferenceSoundEnv_materializeSetBody (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (binder : VarName) (s : SetLanguage.SetExpr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hBody : paperInferenceSoundEnv R txnId I Fctxt (env.insertSet binder s) body F) :
    ∀ visibleDb selected,
      materializeSet visibleDb s = selected →
      Logic.LocalValid R txnId (transformerPre I Fctxt)
        (instantiateSetCommand (env.eraseSet binder) visibleDb
          (Command.subst binder (.lit (.set selected)) (instantiateScalarCommand env body)))
        (transformerPost Fctxt F) := by
  intro visibleDb selected hSelected
  have hLocal := hBody visibleDb
  have hEq :
      instantiateSymCommand (env.insertSet binder s) visibleDb body =
        instantiateSetCommand (env.eraseSet binder) visibleDb
          (Command.subst binder (.lit (.set selected)) (instantiateScalarCommand env body)) := by
    simpa [hSelected] using instantiateSymCommand_insertSet env visibleDb binder s body
  simpa [hEq] using hLocal

theorem paperInferenceSoundEnv_materializeScalarBody (R : LocalRely) (txnId : TxnId)
    (I : Assertion) (Fctxt : SetLanguage.SetExpr) (env : SymEnv)
    (x : VarName) (expr : Expr) (body : Semantics.Program) (F : SetLanguage.SetExpr)
    (hBody : paperInferenceSoundEnv R txnId I Fctxt (env.insertScalar x expr) body F) :
    ∀ visibleDb,
      Logic.LocalValid R txnId (transformerPre I Fctxt)
        (instantiateSetCommand (env.insertScalar x expr) visibleDb
          (instantiateScalarCommand (env.eraseScalar x) (Command.subst x expr body)))
        (transformerPost Fctxt F) := by
  intro visibleDb
  have hLocal := hBody visibleDb
  have hEq := instantiateSymCommand_insertScalar env visibleDb x expr body
  simpa [hEq] using hLocal

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

  def inferForeach (txnId : TxnId) (env : Env)
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

theorem inferEffect_foreach_singleton {txnId : TxnId} {env : Env}
    {doneVar elemVar : VarName} {body : Semantics.Program}
    {source : Expr} {current : RecordLit} {db rows : Database}
    (hSource : evalInEnv env source = some (.set [current]))
    (hBody :
      inferEffect txnId (foreachEnv env doneVar elemVar [] current) body db = some rows) :
    inferEffect txnId env (.foreach source doneVar elemVar body) db = some rows := by
  simp [inferEffect, inferForeach, hSource]
  simpa [foreachEnv] using hBody

def effectStable (R : LocalRely) (F : TxnEffect) : Prop :=
  ∀ localDb visibleDb visibleDb', R localDb visibleDb visibleDb' → F visibleDb = F visibleDb'

def guaranteeValid (G : Guarantee) (F : TxnEffect) : Prop :=
  ∀ visibleDb localDb, F visibleDb = some localDb → G visibleDb (Database.flush localDb visibleDb)

/--
Concrete soundness of `inferEffect` under a fixed visible database.

This is intentionally a no-interference statement: it shows that when `F visibleDb = some localDb'`,
executing the instantiated body from an empty local store under that same `visibleDb` produces
exactly `localDb'`. This is weaker than the paper's Theorem 5.1, which is parameterized by a
non-trivial rely relation and keeps conditionals symbolic.
-/
def inferenceSoundEnv (txnId : TxnId) (env : Env) (body : Semantics.Program) (F : TxnEffect) : Prop :=
  ∀ visibleDb localDb',
    F visibleDb = some localDb' →
    Logic.LocalValid (fun _ _ _ => False) txnId
      (fun localDb visible => localDb = [] ∧ visible = visibleDb)
      (instantiateCommand (ι := IsolationSpec Database) env body)
      (fun localDb visible => localDb = localDb' ∧ visible = visibleDb)

/--
Environment-free version of `inferenceSoundEnv`.

Like `inferenceSoundEnv`, this is a concrete/no-interference property rather than the full
rely-parameterized theorem from the paper.
-/
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
  fun rows => ∃ db : Database, I db ∧ ∀ row, rows row ↔ row ∈ db

def currentGlobalBinding (db : Database) : SetLanguage.SetDenotation :=
  fun row => row ∈ db

def setEnvOfDatabase (x : VarName) (db : Database) : SetLanguage.Env :=
  SetLanguage.Env.ofDatabases [] db

def weakenSetEffect (I : Assertion) (absVar : VarName) (F : SetEffect) : SetEffect :=
  fun db => do
    let s ← F db
    pure (SetLanguage.weakenToInvariant absVar (assertionFormula I) s)

theorem assertionFormula_current (I : Assertion) (x : VarName) (db : Database) (hI : I db) :
    assertionFormula I (currentGlobalBinding db) := by
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

def rowPredicateFormula (env : Env) (source : VarName) (predicate : Expr) (row : Row) : Prop :=
  Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate) row.visible = some true

def insertSetExpr (txnId : TxnId) (env : Env) (expr : Expr) : Option SetLanguage.SetExpr := do
  let .record record ← evalInEnv env expr | none
  pure (SetLanguage.singleton (Row.fromInsert txnId record))

def deleteSetExprWith (outVar : VarName) (txnId : TxnId) (env : Env) (source : VarName) (predicate : Expr) :
    SetLanguage.SetExpr :=
  SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb (fun src =>
    by
      classical
      exact if rowPredicateFormula env source predicate src then
        SetLanguage.singleton (src.markDeleted txnId)
      else
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
  SetLanguage.SetExpr.bind SetLanguage.SetExpr.globalDb (fun src =>
    by
      classical
      exact if rowPredicateFormula env source predicate src then
        (fun (_localDb _globalDb : SetLanguage.SetDenotation) (out : Row) =>
          ∃ updated,
            Expr.eval (Semantics.instantiateRecord source src.visible
              (instantiateExpr env [source] updateExpr)) = some (.record updated) ∧
            out = src.overwrite txnId updated)
      else
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
  classical
  rw [Semantics.mem_collectDeleted_iff hCollect]
  constructor
  · intro h
    simp [deleteSetExprWith, SetLanguage.denote, rowPredicateFormula, SetLanguage.SetExpr.bind,
      SetLanguage.SetExpr.globalDb] at h
    rcases h with ⟨mid, hMid, hBody⟩
    by_cases hPred : rowPredicateFormula env source predicate mid
    · have hEq : row = mid.markDeleted txnId := by
        have hPred' :
            Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate)
              mid.visible = some true := by
          simpa [rowPredicateFormula] using hPred
        simp [rowPredicateFormula, hPred', SetLanguage.singleton, SetLanguage.empty] at hBody
        exact hBody
      exact ⟨mid, by simpa [SetLanguage.Env.ofDatabases] using hMid, hPred, hEq⟩
    · have : False := by
        have hPred' :
            ¬ Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate)
              mid.visible = some true := by
          simpa [rowPredicateFormula] using hPred
        simp [rowPredicateFormula, hPred', SetLanguage.singleton, SetLanguage.empty] at hBody
      exact False.elim this
  · rintro ⟨mid, hMid, hPred, hEq⟩
    refine ⟨mid, ?_, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMid
    · simpa [deleteSetExprWith, SetLanguage.denote, rowPredicateFormula, SetLanguage.SetExpr.bind,
        SetLanguage.SetExpr.globalDb, hPred, SetLanguage.singleton, SetLanguage.empty] using hEq

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
  classical
  rw [Semantics.mem_collectUpdated_iff hCollect]
  constructor
  · intro h
    simp [updateSetExprWith, SetLanguage.denote, rowPredicateFormula, SetLanguage.SetExpr.bind,
      SetLanguage.SetExpr.globalDb] at h
    rcases h with ⟨mid, hMid, hBody⟩
    by_cases hPred : rowPredicateFormula env source predicate mid
    · have hUpdated :
        ∃ updated,
          Expr.eval (Semantics.instantiateRecord source mid.visible
            (instantiateExpr env [source] updateExpr)) = some (.record updated) ∧
          row = mid.overwrite txnId updated := by
          have hPred' :
              Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate)
                mid.visible = some true := by
            simpa [rowPredicateFormula] using hPred
          simp [rowPredicateFormula, hPred', SetLanguage.empty] at hBody
          exact hBody
      rcases hUpdated with ⟨updated, hEval, hEq⟩
      exact ⟨mid, by simpa [SetLanguage.Env.ofDatabases] using hMid, hPred, updated, hEval, hEq⟩
    · have : False := by
        have hPred' :
            ¬ Semantics.satisfiesPredicate source (instantiateExpr env [source] predicate)
              mid.visible = some true := by
          simpa [rowPredicateFormula] using hPred
        simp [rowPredicateFormula, hPred', SetLanguage.empty] at hBody
      exact False.elim this
  · rintro ⟨mid, hMid, hPred, updated, hEval, hEq⟩
    refine ⟨mid, ?_, ?_⟩
    · simpa [SetLanguage.Env.ofDatabases] using hMid
    · simpa [updateSetExprWith, SetLanguage.denote, rowPredicateFormula, SetLanguage.SetExpr.bind,
        SetLanguage.SetExpr.globalDb, hPred, SetLanguage.empty] using ⟨updated, hEval, hEq⟩

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

theorem evalExprInSetEnv_ofDatabases (env : SymEnv) (globalDb : Database) (expr : Expr) :
    evalExprInSetEnv env (SetLanguage.Env.ofDatabases [] globalDb) expr =
      Expr.eval (instantiateSymExpr env [] expr) := by
  simp [evalExprInSetEnv, instantiateElemVars, SetLanguage.Env.ofDatabases, instantiateSymExpr]

theorem formulaOfExpr_closed_true_of_eval (env : SymEnv) (globalDb : Database) (expr : Expr)
    (hEval : Expr.eval expr = some (.scalar (.bool true))) :
    formulaOfExpr { env with scalarVars := [] } expr
      (SetLanguage.Env.ofDatabases [] globalDb).localDb
      (SetLanguage.Env.ofDatabases [] globalDb).globalDb := by
  simp [formulaOfExpr, hEval]

theorem formulaOfExpr_closed_false_of_eval (env : SymEnv) (globalDb : Database) (expr : Expr)
    (hEval : Expr.eval expr = some (.scalar (.bool false))) :
    ¬ formulaOfExpr { env with scalarVars := [] } expr
      (SetLanguage.Env.ofDatabases [] globalDb).localDb
      (SetLanguage.Env.ofDatabases [] globalDb).globalDb := by
  simp [formulaOfExpr, hEval]

theorem denote_insertedRowSet (txnId : TxnId) (env : SymEnv) (expr : Expr)
    (globalDb : Database) (row : Row) (record : RecordLit)
    (hClosed :
      evalExprInSetEnv env ((SetLanguage.Env.ofDatabases [] globalDb).bindElem "_row" row) expr =
        Expr.eval (instantiateSymExpr env [] expr))
    (hEval : Expr.eval (instantiateSymExpr env [] expr) = some (.record record)) :
    SetLanguage.denote (SetLanguage.Env.ofDatabases [] globalDb)
      (insertedRowSet txnId env expr) row ↔ row = Row.fromInsert txnId record := by
  simp [insertedRowSet, SetLanguage.denote, hEval]

theorem deleteSetExpr_abstractGlobal_sound (absVar : VarName) (txnId : TxnId) (env : Env)
    (source : VarName) (predicate : Expr)
    (db rows : Database) (row : Row)
    (hCollect : Semantics.collectDeleted db txnId source (instantiateExpr env [source] predicate) = some rows) :
    SetLanguage.denote (setEnvOfDatabase absVar db)
      (SetLanguage.abstractGlobal absVar (deleteSetExpr txnId env source predicate)) row ↔
      row ∈ rows := by
  simpa [setEnvOfDatabase, SetLanguage.abstractGlobal] using
    deleteSetExpr_sound txnId env source predicate db rows row hCollect

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
  simpa [setEnvOfDatabase, SetLanguage.abstractGlobal] using
    updateSetExpr_sound txnId env source updateExpr predicate db rows row hCollect


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


end Transformer

end DbAppProgramLogic
