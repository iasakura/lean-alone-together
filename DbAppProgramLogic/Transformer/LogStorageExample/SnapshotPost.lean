import DbAppProgramLogic.Transformer.InferenceCapstone

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Snapshot-indexed transaction postconditions

Concrete read-committed transactions compute their local delta from one visible
snapshot, but may commit after other transactions have advanced the visible
database. A postcondition phrased only as `F(currentVisible)` is therefore too
strong for commands such as `archiveLog`, whose effect depends on the snapshot's
log set.

`txnSnapshotPost I R F` records the snapshot explicitly and only requires the
current visible database to be reachable from it by rely steps.
-/

/-- The local delta is the denotation of `F` at some invariant snapshot, and
the current visible database is reachable from that snapshot by rely steps. -/
def txnSnapshotPost (I : Assertion) (R : Rely) (F : SetLanguage.SetExpr) : BiAssertion :=
  fun localDb visibleDb =>
    ∃ snapshotDb,
      I snapshotDb ∧
        Logic.MultiStep R snapshotDb visibleDb ∧
        ∀ row,
          SetLanguage.denote (SetLanguage.Env.ofDatabases [] snapshotDb) F row ↔
            row ∈ localDb

/-- Assertion stability lifts from one rely step to a finite rely path. -/
theorem stableAssertion_multiStep {I : Assertion} {R : Rely}
    (hStable : Logic.stableAssertion R I) :
    ∀ {db db'}, Logic.MultiStep R db db' → I db → I db' := by
  intro db db' hReach hInv
  induction hReach with
  | refl => exact hInv
  | tail hPrev hLast ih => exact hStable _ _ ih hLast

/-- `txnSnapshotPost` is stable under read-committed commit interference by
extending the snapshot-to-visible rely path. -/
theorem txnSnapshotPost_stable_readCommitted
    (I : Assertion) (R : Rely) (F : SetLanguage.SetExpr) :
    Logic.stableBiAssertion
      (Logic.relyMod R (IsolationSpec.readCommitted Database).commit)
      (txnSnapshotPost I R F) := by
  intro localDb visibleDb visibleDb' hPost hStep
  rcases hPost with ⟨snapshotDb, hInv, hReach, hRows⟩
  rcases hStep with ⟨_baseDb, hR, _hCommitOld, _hCommitNew⟩
  exact ⟨snapshotDb, hInv, Logic.MultiStep.tail hReach hR, hRows⟩

/-- A current-visible invariant postcondition is a snapshot postcondition with
the current visible database as the snapshot. -/
theorem transformerPostI_to_txnSnapshotPost
    (I : Assertion) (R : Rely) (F : SetLanguage.SetExpr) :
    ∀ localDb visibleDb,
      transformerPostI I SetLanguage.empty F localDb visibleDb →
        txnSnapshotPost I R F localDb visibleDb := by
  intro localDb visibleDb hPostI
  rcases hPostI with ⟨hPost, hInv⟩
  refine ⟨visibleDb, hInv, Logic.MultiStep.refl, ?_⟩
  intro row
  have hRow := hPost row
  simpa [transformerPost, SetLanguage.SetExpr.union, SetLanguage.empty,
    SetLanguage.denote] using hRow

/-- Weakening the snapshot's invariant. Any snapshot post under a stronger
invariant is also a snapshot post under any weaker invariant. -/
theorem txnSnapshotPost_weaken
    {I I' : Assertion} (hImpl : ∀ db, I db → I' db)
    {R : Rely} {F : SetLanguage.SetExpr}
    {localDb visibleDb : Database}
    (hPost : txnSnapshotPost I R F localDb visibleDb) :
    txnSnapshotPost I' R F localDb visibleDb := by
  rcases hPost with ⟨snapshotDb, hInv, hReach, hRows⟩
  exact ⟨snapshotDb, hImpl snapshotDb hInv, hReach, hRows⟩

end LogStorageExample

end Transformer

end DbAppProgramLogic
