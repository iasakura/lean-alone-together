import DbAppProgramLogic.Semantics

namespace DbAppProgramLogic

namespace SetLanguage

/-!
Partial explicit syntax for the paper's set language `S`.

The development uses this file as the symbolic layer between transaction bodies and the later
first-order encoding. The set combinators are represented directly as Lean functions over the
local and global databases, rather than as a separate deep AST.
-/

abbrev SetDenotation := Row → Prop

/-- Runtime environment retained for formula evaluation and the first-order bridge. The symbolic
set language itself only reads the distinguished local/global databases via `denote`.

The local and global databases are stored as `Database` (= `List Row`) — paper Fig.8 ST-SELECT
requires order-and-multiplicity information at evaluation time so that operations like
`collectSelected` produce a deterministic result. -/
structure Env where
  elemVars : List (VarName × Row) := []
  setVars : List (VarName × Database) := []
  localDb : Database := []
  globalDb : Database := []

namespace Env

def lookupElemList? : List (VarName × Row) → VarName → Option Row
  | [], _ => none
  | (y, row) :: rest, x => if y = x then some row else lookupElemList? rest x

def lookupSetList? : List (VarName × Database) → VarName → Option Database
  | [], _ => none
  | (y, rows) :: rest, x => if y = x then some rows else lookupSetList? rest x

def lookupElem? (ρ : Env) (x : VarName) : Option Row :=
  lookupElemList? ρ.elemVars x

def lookupSet? (ρ : Env) (x : VarName) : Option Database :=
  lookupSetList? ρ.setVars x

def bindElem (ρ : Env) (x : VarName) (row : Row) : Env :=
  { ρ with elemVars := (x, row) :: ρ.elemVars }

def bindSet (ρ : Env) (x : VarName) (rows : Database) : Env :=
  { ρ with setVars := (x, rows) :: ρ.setVars }

def ofDatabases (localDb globalDb : Database) : Env :=
  { localDb := localDb, globalDb := globalDb }

@[simp] theorem lookupElem_bindElem_eq (ρ : Env) (x : VarName) (row : Row) :
    (ρ.bindElem x row).lookupElem? x = some row := by
  simp [lookupElem?, bindElem, lookupElemList?]

@[simp] theorem lookupElem_bindElem_ne (ρ : Env) (x y : VarName) (row : Row) (hxy : x ≠ y) :
    (ρ.bindElem x row).lookupElem? y = ρ.lookupElem? y := by
  simp [lookupElem?, bindElem, lookupElemList?, hxy]

@[simp] theorem lookupSet_bindSet_eq (ρ : Env) (x : VarName) (rows : Database) :
    (ρ.bindSet x rows).lookupSet? x = some rows := by
  simp [lookupSet?, bindSet, lookupSetList?]

@[simp] theorem lookupSet_bindSet_ne (ρ : Env) (x y : VarName) (rows : Database) (hxy : x ≠ y) :
    (ρ.bindSet x rows).lookupSet? y = ρ.lookupSet? y := by
  simp [lookupSet?, bindSet, lookupSetList?, hxy]

end Env

abbrev Formula0 := Database → Database → Prop
abbrev Formula1 := Database → Prop

/--
Closed denotation of a symbolic set effect. The two arguments are the current local and global
databases (`Database = List Row`) — list structure is preserved so that order- and multiplicity-
sensitive operations such as `collectSelected` evaluate deterministically.
-/
abbrev SetExpr := Database → Database → SetDenotation

namespace SetExpr

def localDb : SetExpr :=
  fun localDb _globalDb row => row ∈ localDb

def globalDb : SetExpr :=
  fun _localDb globalDb row => row ∈ globalDb

def comprehension (body : Row → Database → Database → Prop) : SetExpr :=
  fun (localDb globalDb : Database) (row : Row) => body row localDb globalDb

def bind (source : SetExpr) (body : Row → SetExpr) : SetExpr :=
  fun (localDb globalDb : Database) (row : Row) =>
    ∃ mid, source localDb globalDb mid ∧ body mid localDb globalDb row

def ite (cond : Formula0) (s₁ s₂ : SetExpr) : SetExpr :=
  fun (localDb globalDb : Database) (row : Row) =>
    by
      classical
      exact if cond localDb globalDb then
        s₁ localDb globalDb row
      else
        s₂ localDb globalDb row

def union (s₁ s₂ : SetExpr) : SetExpr :=
  fun (localDb globalDb : Database) (row : Row) =>
    s₁ localDb globalDb row ∨ s₂ localDb globalDb row

end SetExpr

def abstractGlobal (_x : VarName) (s : SetExpr) : SetExpr :=
  s

/-- Replace the global database parameter by an existential witness that satisfies the invariant. -/
def weakenToInvariant (_x : VarName) (I : Formula1) (s : SetExpr) : SetExpr :=
  fun (localDb _globalDb : Database) (row : Row) =>
    ∃ rows, I rows ∧ s localDb rows row

/-- Denotational semantics for symbolic set expressions. -/
def denote (ρ : Env) (s : SetExpr) : SetDenotation :=
  s ρ.localDb ρ.globalDb

def ofRows (rows : Database) : SetExpr :=
  fun (_localDb _globalDb : Database) (row : Row) => row ∈ rows

def empty : SetExpr :=
  fun (_localDb _globalDb : Database) (_row : Row) => False

def singleton (row₀ : Row) : SetExpr :=
  fun (_localDb _globalDb : Database) (row : Row) => row = row₀

@[simp] theorem abstractGlobal_ite (x : VarName) (φ : Formula0) (s₁ s₂ : SetExpr) :
    abstractGlobal x (.ite φ s₁ s₂) = .ite φ (abstractGlobal x s₁) (abstractGlobal x s₂) := rfl

@[simp] theorem abstractGlobal_union (x : VarName) (s₁ s₂ : SetExpr) :
    abstractGlobal x (.union s₁ s₂) = .union (abstractGlobal x s₁) (abstractGlobal x s₂) := rfl

@[simp] theorem denote_comprehension (ρ : Env) (body : Row → Database → Database → Prop)
    (row : Row) :
    denote ρ (.comprehension body) row ↔ body row ρ.localDb ρ.globalDb := Iff.rfl

@[simp] theorem denote_bind (ρ : Env) (s : SetExpr) (body : Row → SetExpr) (row : Row) :
    denote ρ (.bind s body) row ↔
      ∃ mid, denote ρ s mid ∧ denote ρ (body mid) row := Iff.rfl

@[simp] theorem denote_union (ρ : Env) (s₁ s₂ : SetExpr) (row : Row) :
    denote ρ (.union s₁ s₂) row ↔ denote ρ s₁ row ∨ denote ρ s₂ row := Iff.rfl

theorem denote_ite_true (ρ : Env) (φ : Formula0) (s₁ s₂ : SetExpr)
    (hφ : φ ρ.localDb ρ.globalDb) :
    denote ρ (.ite φ s₁ s₂) = denote ρ s₁ := by
  funext row
  classical
  simp [denote, SetExpr.ite, hφ]

theorem denote_ite_false (ρ : Env) (φ : Formula0) (s₁ s₂ : SetExpr)
    (hφ : ¬ φ ρ.localDb ρ.globalDb) :
    denote ρ (.ite φ s₁ s₂) = denote ρ s₂ := by
  funext row
  classical
  simp [denote, SetExpr.ite, hφ]

@[simp] theorem denote_ofRows (ρ : Env) (rows : Database) (row : Row) :
    denote ρ (ofRows rows) row ↔ row ∈ rows := Iff.rfl

@[simp] theorem denote_empty (ρ : Env) (row : Row) :
    ¬ denote ρ empty row := by
  simp [empty, denote]

@[simp] theorem denote_singleton (ρ : Env) (row₀ row : Row) :
    denote ρ (singleton row₀) row ↔ row = row₀ := Iff.rfl

@[simp] theorem denote_localDb_ofDatabases (localDb globalDb : Database) (row : Row) :
    denote (Env.ofDatabases localDb globalDb) .localDb row ↔ row ∈ localDb := by
  simp [denote, Env.ofDatabases, SetExpr.localDb]

@[simp] theorem denote_globalDb_ofDatabases (localDb globalDb : Database) (row : Row) :
    denote (Env.ofDatabases localDb globalDb) .globalDb row ↔ row ∈ globalDb := by
  simp [denote, Env.ofDatabases, SetExpr.globalDb]

end SetLanguage

end DbAppProgramLogic
