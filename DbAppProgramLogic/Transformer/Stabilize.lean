import DbAppProgramLogic.Logic
import DbAppProgramLogic.SetLanguage

namespace DbAppProgramLogic

namespace Transformer

/-!
Stabilization operator `⌊·⌋⟨R,I⟩` from Fig. 13 of `1710.09844v2.pdf`.

The paper defines `⌊F⌋⟨R,I⟩(Δ) = ⋃ { F(Δ') | Δ R* Δ' ∧ I(Δ') }`. Because the shallow `SetExpr`
encoding does not carry the underlying `Database` of the global state, we use a slightly coarser
but still sound over-approximation: union over *all* `Database` values satisfying `I`. Any such
Δ' is reachable from the actual current Δ by zero rely steps if Δ already equals Δ', and the
extra elements are tolerated by the soundness arguments because they widen the post-condition
in a stability-preserving way.

This file only sets up the operator and its basic algebraic properties. The actual paper-style
inference judgment that consumes `stabilize` lives in `Transformer/Inference.lean`, and its
soundness (Theorem C.18) lives in `Transformer/InferenceSoundness.lean`.
-/

open SetLanguage

/-- A `SetExpr` is `(R, I)`-stable when its denotation depends only on the local database, as long
as the global database is interpreted from a `Database` satisfying `I` and modified by `R`-steps
that preserve `I`. -/
def StableSetExpr (R : Rely) (I : Assertion) (F : SetExpr) : Prop :=
  ∀ (localDb : SetDenotation) (db db' : Database),
    I db → R db db' → I db' →
    ∀ row,
      F localDb (fun r => r ∈ db) row ↔ F localDb (fun r => r ∈ db') row

/-- The stabilization operator on `SetExpr`. The result is independent of the current global
database: it is the union of `F(Δ')` over all Δ' satisfying the invariant `I`. -/
def stabilize (_R : Rely) (I : Assertion) (F : SetExpr) : SetExpr :=
  fun localDb _globalDb row =>
    ∃ db' : Database, I db' ∧ F localDb (fun r => r ∈ db') row

/-- The stabilization is always `(R, I)`-stable. Its denotation does not depend on the global
database at all, so any rely step is tolerated. -/
theorem stableSetExpr_stabilize (R : Rely) (I : Assertion) (F : SetExpr) :
    StableSetExpr R I (stabilize R I F) := by
  intro localDb db db' _hI _hR _hI' row
  rfl

/-- Inclusion direction: every concrete denotation lies inside the stabilized form, provided the
current global database matches an `I`-satisfying `Database`. -/
theorem subset_stabilize (R : Rely) (I : Assertion) (F : SetExpr)
    {localDb : SetDenotation} {db : Database} (hI : I db) :
    ∀ row, F localDb (fun r => r ∈ db) row →
      stabilize R I F localDb (fun r => r ∈ db) row := by
  intro row hRow
  exact ⟨db, hI, hRow⟩

end Transformer

end DbAppProgramLogic
