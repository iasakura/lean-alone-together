import DbAppProgramLogic.Syntax

namespace DbAppProgramLogic

/-!
Operational semantics and runtime database model.

This file introduces the hidden metadata carried by runtime rows, the isolation specifications used
by transactions, and the local/top-level small-step relations that the later logic reasons about.
-/

inductive Value where
  | scalar : ScalarLit → Value
  | record : RecordLit → Value
  | set : SetLit → Value
  deriving Repr, DecidableEq, Inhabited

namespace Literal

def toValue : Literal → Value
  | .scalar s => .scalar s
  | .record r => .record r
  | .set s => .set s

end Literal

namespace Value

def toExpr : Value → Expr
  | .scalar s => .lit (.scalar s)
  | .record r => .lit (.record r)
  | .set s => .lit (.set s)

end Value

namespace RecordLit

def lookup? (record : RecordLit) (field : FieldName) : Option ScalarLit :=
  (record.fields.find? fun entry => entry.1 = field).map Prod.snd

def setField (record : RecordLit) (field : FieldName) (value : ScalarLit) : RecordLit :=
  let rec go : List (FieldName × ScalarLit) → List (FieldName × ScalarLit)
    | [] => [(field, value)]
    | (name, current) :: rest =>
        if name = field then
          (field, value) :: rest
        else
          (name, current) :: go rest
  ⟨go record.fields⟩

def id? (record : RecordLit) : Option Int :=
  match record.lookup? "id" with
  | some (.int value) => some value
  | _ => none

end RecordLit

namespace Expr

mutual

  private def substFieldExprs (x : VarName) (replacement : Expr) :
      List (FieldName × Expr) → List (FieldName × Expr)
    | [] => []
    | (field, value) :: rest =>
        (field, subst x replacement value) :: substFieldExprs x replacement rest

  def subst (x : VarName) (replacement : Expr) : Expr → Expr
    | Expr.lit litVal => Expr.lit litVal
    | Expr.var y => if x = y then replacement else Expr.var y
    | Expr.proj e field => Expr.proj (subst x replacement e) field
    | Expr.record fields => Expr.record (substFieldExprs x replacement fields)
    | Expr.withUpdates base updates =>
        Expr.withUpdates (subst x replacement base) (substFieldExprs x replacement updates)
    | Expr.binop op lhs rhs => Expr.binop op (subst x replacement lhs) (subst x replacement rhs)

end

mutual

  private theorem substFieldExprs_shadow_lit (x : VarName) (replacement : Expr) (lit : Literal) :
      ∀ fields,
        substFieldExprs x replacement (substFieldExprs x (.lit lit) fields) =
          substFieldExprs x (.lit lit) fields
    | [] => by
        simp [substFieldExprs]
    | (_, value) :: rest => by
        simp [substFieldExprs, subst_shadow_lit, substFieldExprs_shadow_lit]

  theorem subst_shadow_lit (x : VarName) (replacement : Expr) (lit : Literal) :
      ∀ expr,
        subst x replacement (subst x (.lit lit) expr) = subst x (.lit lit) expr
    | .lit litVal => by
        simp [subst]
    | .var y => by
        by_cases hxy : x = y <;> simp [subst, hxy]
    | .proj e field => by
        simp [subst, subst_shadow_lit]
    | .record fields => by
        simp [subst, substFieldExprs_shadow_lit]
    | .withUpdates base updates => by
        simp [subst, subst_shadow_lit, substFieldExprs_shadow_lit]
    | .binop op lhs rhs => by
        simp [subst, subst_shadow_lit]

end

mutual

  private def evalFieldValues : List (FieldName × Expr) → Option (List (FieldName × ScalarLit))
    | [] => some []
    | (field, expr) :: rest => do
        let .scalar value ← eval expr | none
        let rest ← evalFieldValues rest
        pure ((field, value) :: rest)

  def eval : Expr → Option Value
    | Expr.lit litVal => some litVal.toValue
    | Expr.var _ => none
    | Expr.proj e field => do
        let value ← eval e
        match value with
        | Value.record recVal =>
            let fieldValue ← recVal.lookup? field
            pure (.scalar fieldValue)
        | _ => none
    | Expr.record fields => do
        let fields ← evalFieldValues fields
        pure (.record ⟨fields⟩)
    | Expr.withUpdates base updates => do
        let value ← eval base
        match value with
        | Value.record recVal =>
            let updates ← evalFieldValues updates
            pure <| .record <| updates.foldl (fun acc (field, value) => acc.setField field value) recVal
        | _ => none
    | Expr.binop op lhs rhs => do
        let lhs ← eval lhs
        let rhs ← eval rhs
        match op, lhs, rhs with
        | .add, .scalar (.int x), .scalar (.int y) => pure <| .scalar (.int (x + y))
        | .sub, .scalar (.int x), .scalar (.int y) => pure <| .scalar (.int (x - y))
        | .le, .scalar (.int x), .scalar (.int y) => pure <| .scalar (.bool (x <= y))
        | .ge, .scalar (.int x), .scalar (.int y) => pure <| .scalar (.bool (x >= y))
        | .eq, .scalar x, .scalar y => pure <| .scalar (.bool (x = y))
        | _, _, _ => none

end

theorem evalFieldValues_singleton {field : FieldName} {expr : Expr} {value : ScalarLit}
    (hEval : eval expr = some (.scalar value)) :
    evalFieldValues [(field, expr)] = some [(field, value)] := by
  simp [evalFieldValues, hEval]

theorem eval_lit_record_withUpdates {record : RecordLit} {updates : List (FieldName × Expr)}
    {fields : List (FieldName × ScalarLit)}
    (hFields : evalFieldValues updates = some fields) :
    eval (.withUpdates (.lit (.record record)) updates) =
      some (.record (fields.foldl (fun acc (field, value) => acc.setField field value) record)) := by
  simp [eval, hFields, Literal.toValue]

theorem eval_lit_record_single_update {record : RecordLit} {field : FieldName}
    {expr : Expr} {value : ScalarLit}
    (hEval : eval expr = some (.scalar value)) :
    eval (.withUpdates (.lit (.record record)) [(field, expr)]) =
      some (.record (record.setField field value)) := by
  have hFields : evalFieldValues [(field, expr)] = some [(field, value)] := by
    simp [evalFieldValues, hEval]
  simpa [RecordLit.setField] using
    (eval_lit_record_withUpdates (record := record) (updates := [(field, expr)]) hFields)

mutual

  private theorem evalFieldValues_subst_of_eval
      (x : VarName) (replacement : Expr) (value : Value)
      (hEval : eval replacement = some value) :
      ∀ fields,
        evalFieldValues (substFieldExprs x replacement fields) =
          evalFieldValues (substFieldExprs x value.toExpr fields)
    | [] => by
        simp [evalFieldValues, substFieldExprs]
    | (_, expr) :: rest => by
        simp [evalFieldValues, substFieldExprs, eval_subst_of_eval x replacement value hEval,
          evalFieldValues_subst_of_eval x replacement value hEval rest]

  theorem eval_subst_of_eval
      (x : VarName) (replacement : Expr) (value : Value)
      (hEval : eval replacement = some value) :
      ∀ expr, eval (subst x replacement expr) = eval (subst x value.toExpr expr)
    | .lit litVal => by
        simp [subst, eval]
    | .var y => by
        by_cases hxy : x = y
        · subst hxy
          cases value <;> simpa [subst, eval, Value.toExpr] using hEval
        · simp [subst, eval, hxy]
    | .proj expr field => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval expr]
    | .record fields => by
        simp [subst, eval, evalFieldValues_subst_of_eval x replacement value hEval fields]
    | .withUpdates base updates => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval base,
          evalFieldValues_subst_of_eval x replacement value hEval updates]
    | .binop op lhs rhs => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval lhs,
          eval_subst_of_eval x replacement value hEval rhs]

end

end Expr

namespace Command

def subst (x : VarName) (replacement : Expr) : Command ι σ → Command ι σ
  | .skip => .skip
  | .letE y expr body =>
      .letE y (Expr.subst x replacement expr) (if x = y then body else subst x replacement body)
  | .ite cond thenBranch elseBranch =>
      .ite
        (Expr.subst x replacement cond)
        (subst x replacement thenBranch)
        (subst x replacement elseBranch)
  | .seq left right => .seq (subst x replacement left) (subst x replacement right)
  | .insert expr => .insert (Expr.subst x replacement expr)
  | .delete y predicate =>
      .delete y (if x = y then predicate else Expr.subst x replacement predicate)
  | .select y z predicate body =>
      .select
        y
        z
        (if x = z then predicate else Expr.subst x replacement predicate)
        (if x = y then body else subst x replacement body)
  | .update y updateExpr predicate =>
      .update
        y
        (if x = y then updateExpr else Expr.subst x replacement updateExpr)
        (if x = y then predicate else Expr.subst x replacement predicate)
  | .foreach source y z body =>
      .foreach
        (Expr.subst x replacement source)
        y
        z
        (if _ : x = y ∨ x = z then body else subst x replacement body)
  | .foreachRuntime done remaining y z body =>
      .foreachRuntime
        (Expr.subst x replacement done)
        (Expr.subst x replacement remaining)
        y
        z
        (if _ : x = y ∨ x = z then body else subst x replacement body)
  | .txn txnId isolation body => .txn txnId isolation (subst x replacement body)
  | .txnRuntime txnId isolation localDb snapshot body =>
      .txnRuntime txnId isolation localDb snapshot (subst x replacement body)
  | .par left right => .par (subst x replacement left) (subst x replacement right)

theorem subst_shadow_lit (x : VarName) (replacement : Expr) (lit : Literal)
    (cmd : Command ι σ) :
    subst x replacement (subst x (.lit lit) cmd) = subst x (.lit lit) cmd := by
  induction cmd with
  | skip =>
      simp [subst]
  | letE y expr body ih =>
      by_cases hxy : x = y <;> simp [subst, hxy, Expr.subst_shadow_lit, ih]
  | ite cond thenBranch elseBranch ihThen ihElse =>
      simp [subst, Expr.subst_shadow_lit, ihThen, ihElse]
  | seq left right ihLeft ihRight =>
      simp [subst, ihLeft, ihRight]
  | insert expr =>
      simp [subst, Expr.subst_shadow_lit]
  | delete y predicate =>
      by_cases hxy : x = y <;> simp [subst, hxy, Expr.subst_shadow_lit]
  | select y z predicate body ih =>
      by_cases hxy : x = y
      · by_cases hyz : y = z
        · simp [subst, hxy, hyz, Expr.subst_shadow_lit]
        · simp [subst, hxy, hyz, Expr.subst_shadow_lit]
      · by_cases hxz : x = z
        · subst hxz
          simp [subst, hxy, Expr.subst_shadow_lit, ih]
        · simp [subst, hxy, hxz, Expr.subst_shadow_lit, ih]
  | update y updateExpr predicate =>
      by_cases hxy : x = y <;> simp [subst, hxy, Expr.subst_shadow_lit]
  | foreach source y z body ih =>
      by_cases hBlock : x = y ∨ x = z <;> simp [subst, hBlock, Expr.subst_shadow_lit, ih]
  | foreachRuntime done remaining y z body ih =>
      by_cases hBlock : x = y ∨ x = z <;> simp [subst, hBlock, Expr.subst_shadow_lit, ih]
  | txn txnId isolation body ih =>
      simp [subst, ih]
  | txnRuntime txnId isolation localDb snapshot body ih =>
      simp [subst, ih]
  | par left right ihLeft ihRight =>
      simp [subst, ihLeft, ihRight]

end Command

structure Row where
  visible : RecordLit
  txn : TxnId
  del : Bool
  deriving Repr, DecidableEq, Inhabited

abbrev Database := List Row

namespace Row

def id? (row : Row) : Option Int :=
  row.visible.id?

def markDeleted (row : Row) (txnId : TxnId) : Row :=
  { row with txn := txnId, del := true }

def overwrite (row : Row) (txnId : TxnId) (updated : RecordLit) : Row :=
  let visible :=
    match row.id? with
    | some id => updated.setField "id" (.int id)
    | none => updated
  { visible := visible, txn := txnId, del := row.del }

def fromInsert (txnId : TxnId) (record : RecordLit) : Row :=
  { visible := record, txn := txnId, del := false }

end Row

namespace Database

def dom (db : Database) : List Int :=
  db.filterMap Row.id?

def hasId (db : Database) (id : Int) : Prop :=
  id ∈ db.dom

def disjointIds (left right : Database) : Prop :=
  ∀ id, id ∈ left.dom → id ∈ right.dom → False

theorem hasId_append_left (left right : Database) (id : Int) :
    hasId left id → hasId (left ++ right) id := by
  intro h
  unfold hasId dom at h ⊢
  simpa [List.mem_filterMap, List.filterMap_append] using (Or.inl h)

theorem hasId_append_right (left right : Database) (id : Int) :
    hasId right id → hasId (left ++ right) id := by
  intro h
  unfold hasId dom at h ⊢
  simpa [List.mem_filterMap, List.filterMap_append] using (Or.inr h)

theorem hasId_append_middle (left mid right : Database) (id : Int) :
    hasId (left ++ right) id → hasId (left ++ mid ++ right) id := by
  intro h
  unfold hasId dom at h ⊢
  simp [List.mem_filterMap, List.filterMap_append, List.append_assoc] at h ⊢
  cases h with
  | inl hLeft =>
      exact Or.inl hLeft
  | inr hRight =>
      exact Or.inr (Or.inr hRight)

theorem disjointIds_append_left (prefixDb localDb right : Database)
    (h : disjointIds (prefixDb ++ localDb) right) :
    disjointIds localDb right := by
  intro id hLocal hRight
  apply h id
  · unfold dom at hLocal ⊢
    simp [List.mem_filterMap, List.filterMap_append] at hLocal ⊢
    exact Or.inr hLocal
  · exact hRight

def flush (localDb globalDb : Database) : Database :=
  let localIds := localDb.dom
  let preserved := globalDb.filter fun row =>
    match row.id? with
    | some id => !(localIds.contains id)
    | none => true
  let committed := localDb.filter fun row => !row.del
  preserved ++ committed

def visibleRecords (db : Database) : List RecordLit :=
  db.map Row.visible

end Database

structure IsolationSpec (σ : Type) where
  exec : σ → σ → σ → Prop
  commit : σ → σ → σ → Prop

namespace IsolationSpec

def readCommitted (σ : Type) : IsolationSpec σ :=
  { exec := fun _ _ _ => True, commit := fun _ _ _ => True }

def snapshot [DecidableEq σ] : IsolationSpec σ :=
  { exec := fun _ previous current => previous = current
    commit := fun _ previous current => previous = current }

end IsolationSpec

namespace Database

def uniqueIds : IsolationSpec Database :=
  { exec := fun localDb previous current =>
      ∀ row, row ∈ localDb →
        match row.id? with
        | some id => hasId previous id → hasId current id
        | none => True
    commit := fun localDb previous current =>
      ∀ row, row ∈ localDb →
        match row.id? with
        | some id => hasId previous id → hasId current id
        | none => True }

def writeWriteConflictFree : IsolationSpec Database :=
  { exec := fun _ _ _ => True
    commit := fun localDb previous current =>
      ∀ written original,
        written ∈ localDb →
        original ∈ previous →
        written.id? = original.id? →
        original ∈ current }

def snapshotIsolation : IsolationSpec Database :=
  { exec := fun _ previous current => previous = current
    commit := writeWriteConflictFree.commit }

end Database

namespace Semantics

def instantiateRecord (x : VarName) (record : RecordLit) (expr : Expr) : Expr :=
  Expr.subst x (.lit (.record record)) expr

def satisfiesPredicate (x : VarName) (predicate : Expr) (record : RecordLit) : Option Bool := do
  let .scalar (.bool result) ← Expr.eval (instantiateRecord x record predicate) | none
  pure result

def collectSelected (db : Database) (x : VarName) (predicate : Expr) : Option SetLit := do
  let rec go : Database → Option SetLit
    | [] => some []
    | row :: rows => do
        let keep ← satisfiesPredicate x predicate row.visible
        let rest ← go rows
        pure <| if keep then row.visible :: rest else rest
  go db

def collectDeleted (db : Database) (txnId : TxnId) (x : VarName) (predicate : Expr) :
    Option Database := do
  let rec go : Database → Option Database
    | [] => some []
    | row :: rows => do
        let keep ← satisfiesPredicate x predicate row.visible
        let rest ← go rows
        pure <| if keep then row.markDeleted txnId :: rest else rest
  go db

def collectUpdated (db : Database) (txnId : TxnId) (x : VarName)
    (updateExpr predicate : Expr) : Option Database := do
  let rec go : Database → Option Database
    | [] => some []
    | row :: rows => do
        let keep ← satisfiesPredicate x predicate row.visible
        let rest ← go rows
        if keep then
          let .record updated ← Expr.eval (instantiateRecord x row.visible updateExpr) | none
          pure <| row.overwrite txnId updated :: rest
        else
          pure rest
  go db

theorem collectSelected_singleton_true {row : Row} {x : VarName} {predicate : Expr}
    (hPred : satisfiesPredicate x predicate row.visible = some true) :
    collectSelected [row] x predicate = some [row.visible] := by
  simp [collectSelected, collectSelected.go, hPred]

theorem collectUpdated_singleton_true {row : Row} {txnId : TxnId} {x : VarName}
    {updateExpr predicate : Expr} {updated : RecordLit}
    (hPred : satisfiesPredicate x predicate row.visible = some true)
    (hUpdate : Expr.eval (instantiateRecord x row.visible updateExpr) = some (.record updated)) :
    collectUpdated [row] txnId x updateExpr predicate = some [row.overwrite txnId updated] := by
  simp [collectUpdated, collectUpdated.go, hPred, hUpdate]

theorem collectUpdated_singleton_false {row : Row} {txnId : TxnId} {x : VarName}
    {updateExpr predicate : Expr}
    (hPred : satisfiesPredicate x predicate row.visible = some false) :
    collectUpdated [row] txnId x updateExpr predicate = some [] := by
  simp [collectUpdated, collectUpdated.go, hPred]

theorem mem_collectDeleted_go_iff {db : Database} {txnId : TxnId} {x : VarName} {predicate : Expr}
    {rows : Database} {row : Row}
    (hCollect : collectDeleted.go txnId x predicate db = some rows) :
    row ∈ rows ↔
      ∃ sourceRow, sourceRow ∈ db ∧
        satisfiesPredicate x predicate sourceRow.visible = some true ∧
        row = sourceRow.markDeleted txnId := by
  induction db generalizing rows with
  | nil =>
      simp [collectDeleted.go] at hCollect
      cases hCollect
      simp
  | cons head tail ih =>
      cases hKeep : satisfiesPredicate x predicate head.visible with
      | none =>
          have : False := by
            simpa [collectDeleted.go, hKeep] using hCollect
          exact False.elim this
      | some keep =>
          cases keep
          · have hRest : collectDeleted.go txnId x predicate tail = some rows := by
              simpa [collectDeleted.go, hKeep] using hCollect
            simp [ih hRest, hKeep]
          · cases hRest : collectDeleted.go txnId x predicate tail with
            | none =>
                have : False := by
                  simpa [collectDeleted.go, hKeep, hRest] using hCollect
                exact False.elim this
            | some rest =>
                have hRows : head.markDeleted txnId :: rest = rows := by
                  simpa [collectDeleted.go, hKeep, hRest] using hCollect
                symm at hRows
                subst hRows
                simp [ih hRest, hKeep]

theorem mem_collectDeleted_iff {db : Database} {txnId : TxnId} {x : VarName} {predicate : Expr}
    {rows : Database} {row : Row}
    (hCollect : collectDeleted db txnId x predicate = some rows) :
    row ∈ rows ↔
      ∃ sourceRow, sourceRow ∈ db ∧
        satisfiesPredicate x predicate sourceRow.visible = some true ∧
        row = sourceRow.markDeleted txnId := by
  simpa [collectDeleted] using
    (mem_collectDeleted_go_iff (db := db) (txnId := txnId) (x := x) (predicate := predicate)
      (rows := rows) (row := row) hCollect)

theorem mem_collectUpdated_go_iff {db : Database} {txnId : TxnId} {x : VarName}
    {updateExpr predicate : Expr} {rows : Database} {row : Row}
    (hCollect : collectUpdated.go txnId x updateExpr predicate db = some rows) :
    row ∈ rows ↔
      ∃ sourceRow, sourceRow ∈ db ∧
        satisfiesPredicate x predicate sourceRow.visible = some true ∧
        ∃ updated,
          Expr.eval (instantiateRecord x sourceRow.visible updateExpr) = some (.record updated) ∧
          row = sourceRow.overwrite txnId updated := by
  induction db generalizing rows with
  | nil =>
      simp [collectUpdated.go] at hCollect
      cases hCollect
      simp
  | cons head tail ih =>
      cases hKeep : satisfiesPredicate x predicate head.visible with
      | none =>
          have : False := by
            simpa [collectUpdated.go, hKeep] using hCollect
          exact False.elim this
      | some keep =>
          cases keep
          · have hRest : collectUpdated.go txnId x updateExpr predicate tail = some rows := by
              simpa [collectUpdated.go, hKeep] using hCollect
            simp [ih hRest, hKeep]
          · cases hEval : Expr.eval (instantiateRecord x head.visible updateExpr) with
            | none =>
                have : False := by
                  simpa [collectUpdated.go, hKeep, hEval] using hCollect
                exact False.elim this
            | some value =>
                cases value with
                | scalar scalar =>
                    have : False := by
                      simpa [collectUpdated.go, hKeep, hEval] using hCollect
                    exact False.elim this
                | set records =>
                    have : False := by
                      simpa [collectUpdated.go, hKeep, hEval] using hCollect
                    exact False.elim this
                | record updated =>
                    cases hRest : collectUpdated.go txnId x updateExpr predicate tail with
                    | none =>
                        have : False := by
                          simpa [collectUpdated.go, hKeep, hEval, hRest] using hCollect
                        exact False.elim this
                    | some rest =>
                        have hRows : head.overwrite txnId updated :: rest = rows := by
                          simpa [collectUpdated.go, hKeep, hEval, hRest] using hCollect
                        symm at hRows
                        subst hRows
                        simp [ih hRest, hKeep, hEval]

theorem mem_collectUpdated_iff {db : Database} {txnId : TxnId} {x : VarName}
    {updateExpr predicate : Expr} {rows : Database} {row : Row}
    (hCollect : collectUpdated db txnId x updateExpr predicate = some rows) :
    row ∈ rows ↔
      ∃ sourceRow, sourceRow ∈ db ∧
        satisfiesPredicate x predicate sourceRow.visible = some true ∧
        ∃ updated,
          Expr.eval (instantiateRecord x sourceRow.visible updateExpr) = some (.record updated) ∧
          row = sourceRow.overwrite txnId updated := by
  simpa [collectUpdated] using
    (mem_collectUpdated_go_iff (db := db) (txnId := txnId) (x := x)
      (updateExpr := updateExpr) (predicate := predicate)
      (rows := rows) (row := row) hCollect)

def insertFresh (snapshot localDb : Database) (record : RecordLit) : Prop :=
  match record.id? with
  | some id => ¬ Database.hasId (snapshot ++ localDb) id
  | none => False

theorem insertFresh_append_left (snapshot prefixDb localDb : Database) (record : RecordLit)
    (h : insertFresh snapshot (prefixDb ++ localDb) record) :
    insertFresh snapshot localDb record := by
  unfold insertFresh at h ⊢
  cases hId : record.id? with
  | none =>
      simp [hId] at h ⊢
  | some id =>
      simp [hId] at h ⊢
      intro hHas
      apply h
      simpa [List.append_assoc] using
        (Database.hasId_append_middle snapshot prefixDb localDb id hHas)

inductive LocalStep (snapshot : Database) (txnId : TxnId) :
    Command ι Database → Database → Command ι Database → Database → Prop where
  | letE {x expr body value localDb} :
      Expr.eval expr = some value →
      LocalStep snapshot txnId (.letE x expr body) localDb (Command.subst x value.toExpr body) localDb
  | iteTrue {condition thenBranch elseBranch localDb} :
      Expr.eval condition = some (.scalar (.bool true)) →
      LocalStep snapshot txnId (.ite condition thenBranch elseBranch) localDb thenBranch localDb
  | iteFalse {condition thenBranch elseBranch localDb} :
      Expr.eval condition = some (.scalar (.bool false)) →
      LocalStep snapshot txnId (.ite condition thenBranch elseBranch) localDb elseBranch localDb
  | seqLeft {left left' right localDb localDb'} :
      LocalStep snapshot txnId left localDb left' localDb' →
      LocalStep snapshot txnId (.seq left right) localDb (.seq left' right) localDb'
  | seqSkip {next localDb} :
      LocalStep snapshot txnId (.seq .skip next) localDb next localDb
  | insert {expr record localDb} :
      Expr.eval expr = some (.record record) →
      insertFresh snapshot localDb record →
      LocalStep snapshot txnId (.insert expr) localDb .skip (localDb ++ [Row.fromInsert txnId record])
  | select {binder source predicate body selected localDb} :
      collectSelected snapshot source predicate = some selected →
      LocalStep
        snapshot
        txnId
        (.select binder source predicate body)
        localDb
        (Command.subst binder (.lit (.set selected)) body)
        localDb
  | delete {source predicate localDb removed} :
      collectDeleted snapshot txnId source predicate = some removed →
      Database.disjointIds localDb removed →
      LocalStep snapshot txnId (.delete source predicate) localDb .skip (localDb ++ removed)
  | update {source updateExpr predicate localDb updated} :
      collectUpdated snapshot txnId source updateExpr predicate = some updated →
      Database.disjointIds localDb updated →
      LocalStep snapshot txnId (.update source updateExpr predicate) localDb .skip (localDb ++ updated)
  | foreachStart {source doneVar elemVar body localDb records} :
      Expr.eval source = some (.set records) →
      LocalStep
        snapshot
        txnId
        (.foreach source doneVar elemVar body)
        localDb
        (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body)
        localDb
  | foreachNext {done rest doneVar elemVar body current localDb} :
      LocalStep
        snapshot
        txnId
        (.foreachRuntime (Expr.setLit done) (Expr.setLit (current :: rest)) doneVar elemVar body)
        localDb
        (.seq
          (Command.subst doneVar (Expr.setLit done)
            (Command.subst elemVar (.lit (.record current)) body))
          (.foreachRuntime
            (Expr.setLit (done ++ [current]))
            (Expr.setLit rest)
            doneVar
            elemVar
            body))
        localDb
  | foreachDone {done doneVar elemVar body localDb} :
      LocalStep
        snapshot
        txnId
        (.foreachRuntime (Expr.setLit done) (Expr.setLit []) doneVar elemVar body)
        localDb
        .skip
        localDb

abbrev Program := Command (IsolationSpec Database) Database

inductive Step : Program → Database → Program → Database → Prop where
  | txnStart {txnId isolation body globalDb} :
      Step (.txn txnId isolation body) globalDb (.txnRuntime txnId isolation [] globalDb body) globalDb
  | txnExec {txnId isolation localDb snapshot body body' localDb' currentDb} :
      isolation.exec localDb snapshot currentDb →
      LocalStep currentDb txnId body localDb body' localDb' →
      Step
        (.txnRuntime txnId isolation localDb snapshot body)
        currentDb
        (.txnRuntime txnId isolation localDb' currentDb body')
        currentDb
  | txnCommit {txnId isolation localDb snapshot currentDb} :
      isolation.commit localDb snapshot currentDb →
      Step
        (.txnRuntime txnId isolation localDb snapshot .skip)
        currentDb
        .skip
        (Database.flush localDb currentDb)
  | parLeft {left left' right globalDb globalDb'} :
      Step left globalDb left' globalDb' →
      Step (.par left right) globalDb (.par left' right) globalDb'
  | parRight {left right right' globalDb globalDb'} :
      Step right globalDb right' globalDb' →
      Step (.par left right) globalDb (.par left right') globalDb'

end Semantics

end DbAppProgramLogic
