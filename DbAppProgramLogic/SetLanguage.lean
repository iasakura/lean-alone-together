import DbAppProgramLogic.Semantics

namespace DbAppProgramLogic

namespace SetLanguage

abbrev SetDenotation := Row → Prop

structure Env where
  elemVars : List (VarName × Row) := []
  setVars : List (VarName × SetDenotation) := []
  localDb : SetDenotation := fun _ => False
  globalDb : SetDenotation := fun _ => False

namespace Env

def lookupElemList? : List (VarName × Row) → VarName → Option Row
  | [], _ => none
  | (y, row) :: rest, x => if y = x then some row else lookupElemList? rest x

def lookupSetList? : List (VarName × SetDenotation) → VarName → Option SetDenotation
  | [], _ => none
  | (y, rows) :: rest, x => if y = x then some rows else lookupSetList? rest x

def lookupElem? (ρ : Env) (x : VarName) : Option Row :=
  lookupElemList? ρ.elemVars x

def lookupSet? (ρ : Env) (x : VarName) : Option SetDenotation :=
  lookupSetList? ρ.setVars x

def bindElem (ρ : Env) (x : VarName) (row : Row) : Env :=
  { ρ with elemVars := (x, row) :: ρ.elemVars }

def bindSet (ρ : Env) (x : VarName) (rows : SetDenotation) : Env :=
  { ρ with setVars := (x, rows) :: ρ.setVars }

def ofDatabases (localDb globalDb : Database) : Env :=
  { localDb := fun row => row ∈ localDb
    globalDb := fun row => row ∈ globalDb }

@[simp] theorem lookupElem_bindElem_eq (ρ : Env) (x : VarName) (row : Row) :
    (ρ.bindElem x row).lookupElem? x = some row := by
  simp [lookupElem?, bindElem, lookupElemList?]

@[simp] theorem lookupElem_bindElem_ne (ρ : Env) (x y : VarName) (row : Row) (hxy : x ≠ y) :
    (ρ.bindElem x row).lookupElem? y = ρ.lookupElem? y := by
  simp [lookupElem?, bindElem, lookupElemList?, hxy]

@[simp] theorem lookupSet_bindSet_eq (ρ : Env) (x : VarName) (rows : SetDenotation) :
    (ρ.bindSet x rows).lookupSet? x = some rows := by
  simp [lookupSet?, bindSet, lookupSetList?]

end Env

abbrev Formula0 := Env → Prop
abbrev Formula1 := Env → SetDenotation → Prop

/--
Syntax of the set language `S` from Fig. 7.

The formula fragments `φ` and `ϕ` are represented shallowly as meta-level predicates over the
current environment; the set combinators remain an explicit AST.
-/
inductive SetExpr where
  | var : VarName → SetExpr
  | localDb
  | globalDb
  | comprehension : VarName → Formula0 → SetExpr
  | existsSet : VarName → Formula1 → SetExpr → SetExpr
  | bind : SetExpr → VarName → SetExpr → SetExpr
  | ite : Formula0 → SetExpr → SetExpr → SetExpr
  | union : SetExpr → SetExpr → SetExpr
  deriving Inhabited

def abstractGlobal (x : VarName) : SetExpr → SetExpr
  | .var y => .var y
  | .localDb => .localDb
  | .globalDb => .var x
  | .comprehension y φ => .comprehension y φ
  | .existsSet y ψ s => .existsSet y ψ (abstractGlobal x s)
  | .bind s₁ y s₂ => .bind (abstractGlobal x s₁) y (abstractGlobal x s₂)
  | .ite φ s₁ s₂ => .ite φ (abstractGlobal x s₁) (abstractGlobal x s₂)
  | .union s₁ s₂ => .union (abstractGlobal x s₁) (abstractGlobal x s₂)

def weakenToInvariant (x : VarName) (I : Formula1) (s : SetExpr) : SetExpr :=
  .existsSet x I (abstractGlobal x s)

noncomputable def denote (ρ : Env) : SetExpr → SetDenotation
  | .var x =>
      match ρ.lookupSet? x with
      | some rows => rows
      | none => fun _ => False
  | .localDb => ρ.localDb
  | .globalDb => ρ.globalDb
  | .comprehension x φ => fun row => φ (ρ.bindElem x row)
  | .existsSet x ψ s =>
      fun row => ∃ rows, ψ (ρ.bindSet x rows) rows ∧ denote (ρ.bindSet x rows) s row
  | .bind s₁ x s₂ =>
      fun row => ∃ mid, denote ρ s₁ mid ∧ denote (ρ.bindElem x mid) s₂ row
  | .ite φ s₁ s₂ =>
      fun row => by
        classical
        exact if φ ρ then denote ρ s₁ row else denote ρ s₂ row
  | .union s₁ s₂ =>
      fun row => denote ρ s₁ row ∨ denote ρ s₂ row

def ofRows (rows : Database) : SetExpr :=
  .comprehension "_row" (fun ρ =>
    match ρ.lookupElem? "_row" with
    | some row => row ∈ rows
    | none => False)

def empty : SetExpr :=
  .comprehension "_row" (fun _ => False)

def singleton (row₀ : Row) : SetExpr :=
  .comprehension "_row" (fun ρ =>
    match ρ.lookupElem? "_row" with
    | some row => row = row₀
    | none => False)

@[simp] theorem abstractGlobal_var (x y : VarName) :
    abstractGlobal x (.var y) = .var y := rfl

@[simp] theorem abstractGlobal_localDb (x : VarName) :
    abstractGlobal x .localDb = .localDb := rfl

@[simp] theorem abstractGlobal_globalDb (x : VarName) :
    abstractGlobal x .globalDb = .var x := rfl

@[simp] theorem abstractGlobal_existsSet (x y : VarName) (I : Formula1) (s : SetExpr) :
    abstractGlobal x (.existsSet y I s) = .existsSet y I (abstractGlobal x s) := rfl

@[simp] theorem abstractGlobal_bind (x y : VarName) (s₁ s₂ : SetExpr) :
    abstractGlobal x (.bind s₁ y s₂) = .bind (abstractGlobal x s₁) y (abstractGlobal x s₂) := rfl

@[simp] theorem abstractGlobal_ite (x : VarName) (φ : Formula0) (s₁ s₂ : SetExpr) :
    abstractGlobal x (.ite φ s₁ s₂) = .ite φ (abstractGlobal x s₁) (abstractGlobal x s₂) := rfl

@[simp] theorem abstractGlobal_union (x : VarName) (s₁ s₂ : SetExpr) :
    abstractGlobal x (.union s₁ s₂) = .union (abstractGlobal x s₁) (abstractGlobal x s₂) := rfl

@[simp] theorem denote_comprehension (ρ : Env) (x : VarName) (φ : Formula0) (row : Row) :
    denote ρ (.comprehension x φ) row ↔ φ (ρ.bindElem x row) := Iff.rfl

@[simp] theorem denote_existsSet (ρ : Env) (x : VarName) (ψ : Formula1) (s : SetExpr) (row : Row) :
    denote ρ (.existsSet x ψ s) row ↔
      ∃ rows, ψ (ρ.bindSet x rows) rows ∧ denote (ρ.bindSet x rows) s row := Iff.rfl

@[simp] theorem denote_bind (ρ : Env) (s₁ s₂ : SetExpr) (x : VarName) (row : Row) :
    denote ρ (.bind s₁ x s₂) row ↔
      ∃ mid, denote ρ s₁ mid ∧ denote (ρ.bindElem x mid) s₂ row := Iff.rfl

@[simp] theorem denote_union (ρ : Env) (s₁ s₂ : SetExpr) (row : Row) :
    denote ρ (.union s₁ s₂) row ↔ denote ρ s₁ row ∨ denote ρ s₂ row := Iff.rfl

theorem denote_ite_true (ρ : Env) (φ : Formula0) (s₁ s₂ : SetExpr) (hφ : φ ρ) :
    denote ρ (.ite φ s₁ s₂) = denote ρ s₁ := by
  funext row
  simp [denote, hφ]

theorem denote_ite_false (ρ : Env) (φ : Formula0) (s₁ s₂ : SetExpr) (hφ : ¬ φ ρ) :
    denote ρ (.ite φ s₁ s₂) = denote ρ s₂ := by
  funext row
  simp [denote, hφ]

@[simp] theorem denote_ofRows (ρ : Env) (rows : Database) (row : Row) :
    denote ρ (ofRows rows) row ↔ row ∈ rows := by
  simp [ofRows, denote]

@[simp] theorem denote_empty (ρ : Env) (row : Row) :
    ¬ denote ρ empty row := by
  simp [empty, denote]

@[simp] theorem denote_singleton (ρ : Env) (row₀ row : Row) :
    denote ρ (singleton row₀) row ↔ row = row₀ := by
  simp [singleton, denote]

@[simp] theorem denote_localDb_ofDatabases (localDb globalDb : Database) (row : Row) :
    denote (Env.ofDatabases localDb globalDb) .localDb row ↔ row ∈ localDb := Iff.rfl

@[simp] theorem denote_globalDb_ofDatabases (localDb globalDb : Database) (row : Row) :
    denote (Env.ofDatabases localDb globalDb) .globalDb row ↔ row ∈ globalDb := Iff.rfl

end SetLanguage

end DbAppProgramLogic
