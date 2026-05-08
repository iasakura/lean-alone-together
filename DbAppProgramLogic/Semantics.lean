import DbAppProgramLogic.Syntax

namespace DbAppProgramLogic

/-!
Operational semantics and runtime database model.

This file introduces the hidden metadata carried by runtime rows, the isolation specifications used
by transactions, and the local/top-level small-step relations that the later logic reasons about.
-/

abbrev TableName := Int
abbrev RowKey := TableName × Int

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

def table? (record : RecordLit) : Option TableName :=
  match record.lookup? "table" with
  | some (.int value) => some value
  | _ =>
      match record.lookup? "kind" with
      | some (.int value) => some value
      | _ => some 0

def key? (record : RecordLit) : Option RowKey :=
  match record.table?, record.id? with
  | some table, some id => some (table, id)
  | _, _ => none

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
    | Expr.natPair lhs rhs => Expr.natPair (subst x replacement lhs) (subst x replacement rhs)
    | Expr.setNonempty source => Expr.setNonempty (subst x replacement source)
    | Expr.setMinField source field => Expr.setMinField (subst x replacement source) field
    | Expr.setMaxField source field => Expr.setMaxField (subst x replacement source) field
    | Expr.rangeRows field lo hi => Expr.rangeRows field (subst x replacement lo) (subst x replacement hi)

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
    | .natPair lhs rhs => by
        simp [subst, subst_shadow_lit]
    | .setNonempty source => by
        simp [subst, subst_shadow_lit]
    | .setMinField source field => by
        simp [subst, subst_shadow_lit]
    | .setMaxField source field => by
        simp [subst, subst_shadow_lit]
    | .rangeRows field lo hi => by
        simp [subst, subst_shadow_lit]

end

private def intField? (record : RecordLit) (field : FieldName) : Option Int :=
  match record.lookup? field with
  | some (.int value) => some value
  | _ => none

private def collectIntFieldValues (field : FieldName) : SetLit → Option (List Int)
  | [] => some []
  | rec :: records => do
      let value ← intField? rec field
      let rest ← collectIntFieldValues field records
      pure (value :: rest)

private def minInt? : List Int → Option Int
  | [] => none
  | value :: values => some (values.foldl min value)

private def maxInt? : List Int → Option Int
  | [] => none
  | value :: values => some (values.foldl max value)

private def intRangeRecords (field : FieldName) (lo hi : Int) : SetLit :=
  (List.range (Int.toNat (hi - lo))).map fun (offset : Nat) =>
    ⟨[(field, .int (lo + (offset : Int)))]⟩

def natPairCode (a b : Nat) : Nat :=
  ((a + b) * (a + b + 1)) / 2 + b

def intNatPair? (a b : Int) : Option Int :=
  if a < 0 ∨ b < 0 then
    none
  else
    some (natPairCode a.toNat b.toNat)

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
    | Expr.binop BinOp.and lhs rhs => do
        let lhs ← eval lhs
        match lhs with
        | .scalar (.bool false) => pure <| .scalar (.bool false)
        | .scalar (.bool true) => do
            let .scalar (.bool rhs) ← eval rhs | none
            pure <| .scalar (.bool rhs)
        | _ => none
    | Expr.binop BinOp.or lhs rhs => do
        let lhs ← eval lhs
        match lhs with
        | .scalar (.bool true) => pure <| .scalar (.bool true)
        | .scalar (.bool false) => do
            let .scalar (.bool rhs) ← eval rhs | none
            pure <| .scalar (.bool rhs)
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
    | Expr.natPair lhs rhs => do
        let .scalar (.int lhs) ← eval lhs | none
        let .scalar (.int rhs) ← eval rhs | none
        let value ← intNatPair? lhs rhs
        pure <| .scalar (.int value)
    | Expr.setNonempty source => do
        let .set records ← eval source | none
        pure <| .scalar (.bool (!records.isEmpty))
    | Expr.setMinField source field => do
        let .set records ← eval source | none
        let values ← collectIntFieldValues field records
        let value ← minInt? values
        pure <| .scalar (.int value)
    | Expr.setMaxField source field => do
        let .set records ← eval source | none
        let values ← collectIntFieldValues field records
        let value ← maxInt? values
        pure <| .scalar (.int value)
    | Expr.rangeRows field lo hi => do
        let .scalar (.int loValue) ← eval lo | none
        let .scalar (.int hiValue) ← eval hi | none
        if loValue <= hiValue then
          pure <| .set (intRangeRecords field loValue hiValue)
        else
          none

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
        cases op <;>
          simp [subst, eval, eval_subst_of_eval x replacement value hEval lhs,
            eval_subst_of_eval x replacement value hEval rhs]
    | .natPair lhs rhs => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval lhs,
          eval_subst_of_eval x replacement value hEval rhs]
    | .setNonempty source => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval source]
    | .setMinField source field => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval source]
    | .setMaxField source field => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval source]
    | .rangeRows field lo hi => by
        simp [subst, eval, eval_subst_of_eval x replacement value hEval lo,
          eval_subst_of_eval x replacement value hEval hi]

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

def key? (row : Row) : Option RowKey :=
  row.visible.key?

def markDeleted (row : Row) (txnId : TxnId) : Row :=
  { row with txn := txnId, del := true }

private def preserveKeyFields (original updated : RecordLit) : RecordLit :=
  let updated :=
    match original.id? with
    | some id => updated.setField "id" (.int id)
    | none => updated
  match original.lookup? "table" with
  | some (.int table) => updated.setField "table" (.int table)
  | _ =>
      match original.lookup? "kind" with
      | some (.int kind) => updated.setField "kind" (.int kind)
      | _ => updated

def overwrite (row : Row) (txnId : TxnId) (updated : RecordLit) : Row :=
  { visible := preserveKeyFields row.visible updated, txn := txnId, del := row.del }

def fromInsert (txnId : TxnId) (record : RecordLit) : Row :=
  { visible := record, txn := txnId, del := false }

/-- `Row.overwrite` preserves `del`. -/
@[simp] theorem overwrite_del (row : Row) (txnId : TxnId) (updated : RecordLit) :
    (row.overwrite txnId updated).del = row.del := rfl

end Row

namespace RecordLit

private theorem find?_setField_go_of_ne {field other : FieldName}
    {value : ScalarLit} (hNe : other ≠ field) (fields : List (FieldName × ScalarLit)) :
    (setField.go field value fields).find? (fun e => e.fst = other) =
      fields.find? (fun e => e.fst = other) := by
  induction fields with
  | nil =>
      simp [setField.go, decide_eq_true_eq, hNe.symm]
  | cons head tail ih =>
      rcases head with ⟨name, val⟩
      simp only [setField.go]
      by_cases hName : name = field
      · subst hName
        simp [List.find?, decide_eq_true_eq, hNe.symm]
      · simp [List.find?, decide_eq_true_eq, hName, ih]

private theorem find?_setField_go_eq {field : FieldName} {value : ScalarLit}
    (fields : List (FieldName × ScalarLit)) :
    (setField.go field value fields).find? (fun e => e.fst = field) = some (field, value) := by
  induction fields with
  | nil => simp [setField.go]
  | cons head tail ih =>
      rcases head with ⟨name, val⟩
      simp only [setField.go]
      by_cases hName : name = field
      · subst hName; simp [List.find?]
      · simp [List.find?, decide_eq_true_eq, hName, ih]

/-- `setField` of a different field commutes with `lookup?`. -/
theorem lookup?_setField_of_ne {rec : RecordLit} {field other : FieldName}
    {value : ScalarLit} (hNe : other ≠ field) :
    (rec.setField field value).lookup? other = rec.lookup? other := by
  unfold setField lookup?
  simp [find?_setField_go_of_ne hNe rec.fields]

/-- `setField field value` makes `lookup? field` return `value`. -/
theorem lookup?_setField {rec : RecordLit} {field : FieldName} {value : ScalarLit} :
    (rec.setField field value).lookup? field = some value := by
  unfold setField lookup?
  simp [find?_setField_go_eq]

end RecordLit

namespace Row

/-- `Row.overwrite` preserves the key when both the original `id` and explicit
`table` fields are set as integer scalars. -/
theorem overwrite_key?_of_explicit
    (row : Row) (txnId : TxnId) (updated : RecordLit) {id : Int} {table : Int}
    (hId : row.visible.lookup? "id" = some (.int id))
    (hTable : row.visible.lookup? "table" = some (.int table)) :
    (row.overwrite txnId updated).key? = some (table, id) := by
  unfold Row.key? Row.overwrite preserveKeyFields
  have hOrigId? : row.visible.id? = some id := by
    unfold RecordLit.id?; rw [hId]
  rw [show row.visible.id? = some id from hOrigId?]
  rw [show row.visible.lookup? "table" = some (.int table) from hTable]
  unfold RecordLit.key? RecordLit.table? RecordLit.id?
  have hFinalTable :
      ((updated.setField "id" (.int id)).setField "table" (.int table)).lookup? "table" =
        some (.int table) := RecordLit.lookup?_setField
  have hFinalId :
      ((updated.setField "id" (.int id)).setField "table" (.int table)).lookup? "id" =
        some (.int id) := by
    have hNe : ("id" : FieldName) ≠ "table" := by decide
    rw [RecordLit.lookup?_setField_of_ne hNe]
    exact RecordLit.lookup?_setField
  rw [hFinalTable, hFinalId]

/-- For fields other than the key fields (`id`, `table`, `kind`),
`Row.overwrite` passes the lookup through to `updated`. -/
theorem overwrite_lookup?_of_ne
    (row : Row) (txnId : TxnId) (updated : RecordLit) {field : FieldName}
    (hNeId : field ≠ "id") (hNeTable : field ≠ "table") (hNeKind : field ≠ "kind") :
    (row.overwrite txnId updated).visible.lookup? field = updated.lookup? field := by
  unfold Row.overwrite preserveKeyFields
  show (let updated' := match row.visible.id? with
                        | some id => updated.setField "id" (.int id)
                        | none => updated;
        match row.visible.lookup? "table" with
        | some (.int table) => updated'.setField "table" (.int table)
        | _ =>
            match row.visible.lookup? "kind" with
            | some (.int kind) => updated'.setField "kind" (.int kind)
            | _ => updated').lookup? field = updated.lookup? field
  -- After both potential setFields, lookup? field passes through if field ≠ "id"/"table"/"kind".
  have hStep1 : ∀ (rec : RecordLit),
      (match row.visible.id? with
       | some id => rec.setField "id" (.int id)
       | none => rec).lookup? field = rec.lookup? field := by
    intro rec
    cases hI : row.visible.id? with
    | none => simp
    | some idVal =>
        simp [RecordLit.lookup?_setField_of_ne hNeId]
  generalize hUpd' : (match row.visible.id? with
                       | some id => updated.setField "id" (.int id)
                       | none => updated) = updated' at *
  have hUpd'_lookup : updated'.lookup? field = updated.lookup? field := by
    rw [← hUpd']; exact hStep1 updated
  cases hT : row.visible.lookup? "table" with
  | none =>
      cases hK : row.visible.lookup? "kind" with
      | none => simp [hT, hK]; exact hUpd'_lookup
      | some lit =>
          cases lit with
          | int kind =>
              simp [hT, hK, RecordLit.lookup?_setField_of_ne hNeKind]
              exact hUpd'_lookup
          | bool _ => simp [hT, hK]; exact hUpd'_lookup
  | some lit =>
      cases lit with
      | int table =>
          simp [hT, RecordLit.lookup?_setField_of_ne hNeTable]
          exact hUpd'_lookup
      | bool _ =>
          cases hK : row.visible.lookup? "kind" with
          | none => simp [hT, hK]; exact hUpd'_lookup
          | some lit =>
              cases lit with
              | int kind =>
                  simp [hT, hK, RecordLit.lookup?_setField_of_ne hNeKind]
                  exact hUpd'_lookup
              | bool _ => simp [hT, hK]; exact hUpd'_lookup

end Row

namespace Database

def dom (db : Database) : List Int :=
  db.filterMap Row.id?

def keyDom (db : Database) : List RowKey :=
  db.filterMap Row.key?

def hasId (db : Database) (id : Int) : Prop :=
  id ∈ db.dom

def hasKey (db : Database) (key : RowKey) : Prop :=
  key ∈ db.keyDom

def disjointIds (left right : Database) : Prop :=
  ∀ key, key ∈ left.keyDom → key ∈ right.keyDom → False

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

theorem hasKey_append_left (left right : Database) (key : RowKey) :
    hasKey left key → hasKey (left ++ right) key := by
  intro h
  unfold hasKey keyDom at h ⊢
  simpa [List.mem_filterMap, List.filterMap_append] using (Or.inl h)

theorem hasKey_append_right (left right : Database) (key : RowKey) :
    hasKey right key → hasKey (left ++ right) key := by
  intro h
  unfold hasKey keyDom at h ⊢
  simpa [List.mem_filterMap, List.filterMap_append] using (Or.inr h)

theorem hasKey_append_middle (left mid right : Database) (key : RowKey) :
    hasKey (left ++ right) key → hasKey (left ++ mid ++ right) key := by
  intro h
  unfold hasKey keyDom at h ⊢
  simp [List.mem_filterMap, List.filterMap_append, List.append_assoc] at h ⊢
  cases h with
  | inl hLeft =>
      exact Or.inl hLeft
  | inr hRight =>
      exact Or.inr (Or.inr hRight)

theorem disjointIds_append_left (prefixDb localDb right : Database)
    (h : disjointIds (prefixDb ++ localDb) right) :
    disjointIds localDb right := by
  intro key hLocal hRight
  apply h key
  · unfold keyDom at hLocal ⊢
    simp [List.mem_filterMap, List.filterMap_append] at hLocal ⊢
    exact Or.inr hLocal
  · exact hRight

def flush (localDb globalDb : Database) : Database :=
  let localKeys := localDb.keyDom
  let preserved := globalDb.filter fun row =>
    match row.key? with
    | some key => !(localKeys.contains key)
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
        match row.key? with
        | some key => hasKey previous key → hasKey current key
        | none => True
    commit := fun localDb previous current =>
      ∀ row, row ∈ localDb →
        match row.key? with
        | some key => hasKey previous key → hasKey current key
        | none => True }

def writeWriteConflictFree : IsolationSpec Database :=
  { exec := fun _ _ _ => True
    commit := fun localDb previous current =>
      ∀ written original,
        written ∈ localDb →
        original ∈ previous →
        written.key? = original.key? →
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
  match record.key? with
  | some key => ¬ Database.hasKey (snapshot ++ localDb) key
  | none => False

theorem insertFresh_append_left (snapshot prefixDb localDb : Database) (record : RecordLit)
    (h : insertFresh snapshot (prefixDb ++ localDb) record) :
    insertFresh snapshot localDb record := by
  unfold insertFresh at h ⊢
  cases hKey : record.key? with
  | none =>
      simp [hKey] at h
  | some key =>
      simp [hKey] at h ⊢
      intro hHas
      apply h
      simpa [List.append_assoc] using
        (Database.hasKey_append_middle snapshot prefixDb localDb key hHas)

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
  | seqLeft {left left' right globalDb globalDb'} :
      Step left globalDb left' globalDb' →
      Step (.seq left right) globalDb (.seq left' right) globalDb'
  | seqSkip {right globalDb} :
      Step (.seq .skip right) globalDb right globalDb
  | parLeft {left left' right globalDb globalDb'} :
      Step left globalDb left' globalDb' →
      Step (.par left right) globalDb (.par left' right) globalDb'
  | parRight {left right right' globalDb globalDb'} :
      Step right globalDb right' globalDb' →
      Step (.par left right) globalDb (.par left right') globalDb'

end Semantics

end DbAppProgramLogic
