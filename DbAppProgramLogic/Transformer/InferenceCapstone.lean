import DbAppProgramLogic.Transformer.InferenceSoundness

/-!
Paper-aligned capstone: from the inference judgment `PaperInfer` (Fig. 13) to whole-program
soundness.

This file chains together three existing results:

* `PaperInfer.sound` (Theorem C.18) — `PaperInfer` yields a `LocalValid` triple.
* `Logic.txnGlobalValid_of_localValid` — a `LocalValid` triple at an empty local database and
  `I`-satisfying visible DB yields `GlobalValid` for the enclosing `.txn`.
* `Logic.globalValid_par` — two `GlobalValid` triples at compatible relies compose in parallel.

The intermediate lemma is Theorem C.19 (`PaperInfer.sound_emptyContext`), which restates the
empty-context precondition `transformerPre I empty` in the `localDb = [] ∧ I visibleDb` shape
required by `txnGlobalValid_of_localValid`.
-/

namespace DbAppProgramLogic

namespace Transformer

open SetLanguage

/-- The empty-context precondition `transformerPre I empty` is equivalent to
`localDb = [] ∧ I visibleDb`. -/
theorem transformerPre_empty_iff (I : Assertion) (localDb visibleDb : Database) :
    transformerPre I SetLanguage.empty localDb visibleDb ↔
      localDb = [] ∧ I visibleDb := by
  unfold transformerPre
  constructor
  · rintro ⟨hDenote, hI⟩
    refine ⟨?_, hI⟩
    cases localDb with
    | nil => rfl
    | cons row _ =>
        have := (hDenote row).mpr List.mem_cons_self
        simp [SetLanguage.denote, SetLanguage.empty] at this
  · rintro ⟨rfl, hI⟩
    refine ⟨?_, hI⟩
    intro row
    simp [SetLanguage.denote, SetLanguage.empty]

/-- **Theorem C.19** — the `s = ∅` corollary of Theorem C.18. With an empty incoming context
effect, the precondition reduces to `localDb = [] ∧ I visibleDb`. -/
theorem PaperInfer.sound_emptyContext
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {F : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I SetLanguage.empty body F) :
    Logic.LocalValid R txnId
      (fun localDb visibleDb => localDb = [] ∧ I visibleDb)
      body
      (transformerPost SetLanguage.empty F) :=
  Logic.localValid_conseq
    (fun localDb visibleDb hPre => (transformerPre_empty_iff I localDb visibleDb).mpr hPre)
    (PaperInfer.sound hStableI h)
    (fun _ _ hPost => hPost)

/-- A global rely `R : Rely` trivially induces a local rely `relyMod R isolation.exec` that
preserves any `Assertion` whenever `R` does. -/
theorem stableBiAssertion_relyMod_of_stableAssertion
    {R : Rely} {I : Assertion}
    (isolation : IsolationSpec Database)
    (hStableI : Logic.stableAssertion R I) :
    Logic.stableBiAssertion (Logic.relyMod R isolation.exec) (fun _ visibleDb => I visibleDb) := by
  intro localDb visibleDb visibleDb' hI hStep
  rcases hStep with ⟨_baseDb, hR, _, _⟩
  exact hStableI _ _ hI hR

/-- **`PaperInfer → GlobalValid` for a single transaction.** Given a Fig. 13 derivation for the
body of a `.txn txnId isolation body` together with the standard stability, guarantee, and
invariant-preservation side conditions, one obtains `GlobalValid`. -/
theorem PaperInfer.globalValid_txn
    {R : Rely} {I : Assertion} {txnId : TxnId}
    {isolation : IsolationSpec Database} {body : Semantics.Program}
    {F : SetExpr} {G : Guarantee}
    (hStableI : Logic.stableAssertion R I)
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
    (hInfer : PaperInfer (Logic.relyMod R isolation.exec) txnId I SetLanguage.empty body F)
    (hQstable :
      Logic.stableBiAssertion (Logic.relyMod R isolation.commit)
        (transformerPost SetLanguage.empty F))
    (hGuarantee :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty F localDb visibleDb →
          G visibleDb (Database.flush localDb visibleDb))
    (hPreserve : ∀ db db', I db → G db db' → I db') :
    Logic.GlobalValid I R (.txn txnId isolation body) G I := by
  have hStableIBi := stableBiAssertion_relyMod_of_stableAssertion isolation hStableI
  have hLocal := PaperInfer.sound_emptyContext hStableIBi hInfer
  exact Logic.txnGlobalValid_of_localValid hStableI hExecStable hCommitIsoStable
    (fun localDb visibleDb => Iff.rfl) hLocal hQstable hGuarantee hPreserve

/-- **Parallel composition from `PaperInfer`.** Two `.txn` programs whose bodies have Fig. 13
derivations (each mutually tolerating the other's guarantee in its local rely) combine into a
paper-aligned `GlobalValid` for their parallel composition.

This is the direct paper-aligned analogue of the legacy `vcg_sound`-backed parallel composition:
the only difference is that both halves come out of a `PaperInfer` derivation rather than the
concrete VCG pipeline. -/
theorem PaperInfer.globalValid_txnPar
    {R : Rely} {I : Assertion}
    {txnIdLeft txnIdRight : TxnId}
    {isoLeft isoRight : IsolationSpec Database}
    {bodyLeft bodyRight : Semantics.Program}
    {Fleft Fright : SetExpr}
    {Gleft Gright : Guarantee}
    -- Left transaction
    (hExecStableLeft :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gright db db') isoLeft.exec)
    (hCommitIsoStableLeft :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gright db db') isoLeft.commit)
    (hInferLeft :
      PaperInfer
        (Logic.relyMod (fun db db' => R db db' ∨ Gright db db') isoLeft.exec)
        txnIdLeft I SetLanguage.empty bodyLeft Fleft)
    (hQstableLeft :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gright db db') isoLeft.commit)
        (transformerPost SetLanguage.empty Fleft))
    (hGuaranteeLeft :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty Fleft localDb visibleDb →
          Gleft visibleDb (Database.flush localDb visibleDb))
    -- Right transaction
    (hExecStableRight :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gleft db db') isoRight.exec)
    (hCommitIsoStableRight :
      Logic.stableIsolation (fun db db' => R db db' ∨ Gleft db db') isoRight.commit)
    (hInferRight :
      PaperInfer
        (Logic.relyMod (fun db db' => R db db' ∨ Gleft db db') isoRight.exec)
        txnIdRight I SetLanguage.empty bodyRight Fright)
    (hQstableRight :
      Logic.stableBiAssertion
        (Logic.relyMod (fun db db' => R db db' ∨ Gleft db db') isoRight.commit)
        (transformerPost SetLanguage.empty Fright))
    (hGuaranteeRight :
      ∀ localDb visibleDb,
        transformerPost SetLanguage.empty Fright localDb visibleDb →
          Gright visibleDb (Database.flush localDb visibleDb))
    -- Invariant preservation under each guarantee
    (hPreserveLeft : ∀ db db', I db → Gleft db db' → I db')
    (hPreserveRight : ∀ db db', I db → Gright db db' → I db')
    -- Both halves tolerate R (in case the environment takes a pure-R step)
    (hStableILeft : Logic.stableAssertion (fun db db' => R db db' ∨ Gright db db') I)
    (hStableIRight : Logic.stableAssertion (fun db db' => R db db' ∨ Gleft db db') I) :
    Logic.GlobalValid I R
      (.par (.txn txnIdLeft isoLeft bodyLeft) (.txn txnIdRight isoRight bodyRight))
      (fun db db' => Gleft db db' ∨ Gright db db') I := by
  have hLeft :
      Logic.GlobalValid I (fun db db' => R db db' ∨ Gright db db')
        (.txn txnIdLeft isoLeft bodyLeft) Gleft I :=
    PaperInfer.globalValid_txn hStableILeft hExecStableLeft hCommitIsoStableLeft
      hInferLeft hQstableLeft hGuaranteeLeft hPreserveLeft
  have hRight :
      Logic.GlobalValid I (fun db db' => R db db' ∨ Gleft db db')
        (.txn txnIdRight isoRight bodyRight) Gright I :=
    PaperInfer.globalValid_txn hStableIRight hExecStableRight hCommitIsoStableRight
      hInferRight hQstableRight hGuaranteeRight hPreserveRight
  exact Logic.globalValid_par hLeft hRight

/-! ## Wrap-flavoured capstone (Fig. 8's `⟦·⟧⟨R,I⟩`)

The plain `globalValid_txn` requires the user to discharge `transformerPost ∅ F` stability under
the commit-phase rely (`hQstable`). For inference judgments whose `F` is genuinely
global-database-dependent (typical for SELECT-bound bodies), this stability fails directly. The
paper's solution is to weaken `F` via `⟦·⟧⟨R,I⟩` before the final hand-off.

`globalValid_txn_wrapped` packages this: it accepts a `PaperInfer` derivation under any `F`,
together with stability witnesses for `Fctxt = ∅` and `F`, and returns `GlobalValid` using the
weakened subset-post. Because the wrap's payload is always `StableSetExprBi` (either the
original `F` re-witnessed by the caller, or the always-stable `weakenF` branch), commit-phase
stability is delivered automatically.
-/

/-- Empty context is trivially stable under any rely. -/
theorem stableSetExprBi_empty_inferCapstone (R : LocalRely) :
    StableSetExprBi R SetLanguage.empty :=
  stableSetExprBi_empty R

/-- The empty-context precondition reformulated for `transformerPostSubI`. -/
theorem transformerPostSubI_empty_iff
    (I : Assertion) (F : SetExpr) (localDb visibleDb : Database) :
    transformerPostSubI I SetLanguage.empty F localDb visibleDb ↔
      (∀ row, row ∈ localDb →
        SetLanguage.denote (SetLanguage.Env.ofDatabases [] visibleDb) F row) ∧ I visibleDb := by
  unfold transformerPostSubI transformerPostSub
  refine and_congr (forall_congr' (fun row => ?_)) Iff.rfl
  refine forall_congr' (fun _hMem => ?_)
  constructor
  · intro h
    rcases h with hEmpty | hF
    · exact absurd hEmpty (SetLanguage.denote_empty _ row)
    · exact hF
  · intro hF
    exact Or.inr hF

/-- **Wrap-flavoured `PaperInfer → GlobalValid`.** Same as `globalValid_txn`, but uses the
subset-style wrapped post-condition for the commit-phase stability requirement. The wrap is
applied to `F` so the user only needs a `StableSetExprBi`-style stability claim on the
*unwrapped* part of `Fctxt` (which is `empty` here, hence trivial). -/
theorem PaperInfer.globalValid_txn_wrapped
    {R : Rely} {I : Assertion} {txnId : TxnId}
    {isolation : IsolationSpec Database} {body : Semantics.Program}
    {F : SetExpr} {G : Guarantee}
    (hStableI : Logic.stableAssertion R I)
    (hExecStable : Logic.stableIsolation R isolation.exec)
    (hCommitIsoStable : Logic.stableIsolation R isolation.commit)
    (hInfer : PaperInfer (Logic.relyMod R isolation.exec) txnId I SetLanguage.empty body F)
    -- F is StableSetExprBi-stable under the commit-phase rely (only needed when the wrap stays
    -- in the pass-through branch). The user can always discharge this by switching to the
    -- weakened branch via `weakenF I F` directly.
    (hQstable :
      Logic.stableBiAssertion (Logic.relyMod R isolation.commit)
        (transformerPostSubI I SetLanguage.empty
          (stabilizeWrap (Logic.relyMod R isolation.exec) I SetLanguage.empty F)))
    (hGuarantee :
      ∀ localDb visibleDb,
        transformerPostSubI I SetLanguage.empty
            (stabilizeWrap (Logic.relyMod R isolation.exec) I SetLanguage.empty F)
            localDb visibleDb →
          G visibleDb (Database.flush localDb visibleDb))
    (hPreserve : ∀ db db', I db → G db db' → I db') :
    Logic.GlobalValid I R (.txn txnId isolation body) G I := by
  have hStableIBi := stableBiAssertion_relyMod_of_stableAssertion isolation hStableI
  have hLocalRaw :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (transformerPre I SetLanguage.empty) body
        (transformerPostSubI I SetLanguage.empty
          (stabilizeWrap (Logic.relyMod R isolation.exec) I SetLanguage.empty F)) :=
    PaperInfer.sound_wrapped hStableIBi hInfer
  -- Bridge the precondition from `transformerPre I empty` to `localDb = [] ∧ I visibleDb`.
  have hLocal :
      Logic.LocalValid (Logic.relyMod R isolation.exec) txnId
        (fun localDb visibleDb => localDb = [] ∧ I visibleDb) body
        (transformerPostSubI I SetLanguage.empty
          (stabilizeWrap (Logic.relyMod R isolation.exec) I SetLanguage.empty F)) :=
    Logic.localValid_conseq
      (fun localDb visibleDb hPre =>
        (transformerPre_empty_iff I localDb visibleDb).mpr hPre)
      hLocalRaw
      (fun _ _ hPost => hPost)
  exact Logic.txnGlobalValid_of_localValid hStableI hExecStable hCommitIsoStable
    (fun localDb visibleDb => Iff.rfl) hLocal hQstable hGuarantee hPreserve

end Transformer

end DbAppProgramLogic
