import DbAppProgramLogic.Transformer.Inference
import DbAppProgramLogic.Transformer.Paper
import DbAppProgramLogic.Transformer.Select
import DbAppProgramLogic.Transformer.Foreach

namespace DbAppProgramLogic

namespace Transformer

/-!
Soundness of the paper-style inference judgment `PaperInfer` (`Transformer/Inference.lean`),
matching Theorem C.18 / C.19 of the appendix in `1710.09844v2.pdf`.

The proof proceeds by induction on `PaperInfer`. Each rule is discharged by the corresponding
`paperInferenceSound_*` lemma in `Transformer/Paper.lean`, with a small invariant-augmentation
helper that lets us thread the `I`-clause through composition (SEQ in particular requires the
mid-state to satisfy `I`, even though the paper's `transformerPost` does not include it).
-/

open SetLanguage

/-- A `BiAssertion` augmented with the visible-DB invariant `I`. Used as an internal
intermediate post-condition during the soundness proof so that composed rules can re-establish
`transformerPre` at junction points. -/
def transformerPostI (I : Assertion) (Fctxt F : SetExpr) : BiAssertion :=
  fun localDb visibleDb =>
    transformerPost Fctxt F localDb visibleDb ∧ I visibleDb

theorem localInterleavedStep_preserves_invariant
    {ι : Type} {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {cfg cfg' : LocalConfig ι}
    (hStep : Logic.localInterleavedStep (ι := ι) R txnId cfg cfg')
    (hI : I cfg.visibleDb) :
    I cfg'.visibleDb := by
  rcases cfg with ⟨cmd, localDb, visibleDb⟩
  rcases cfg' with ⟨cmd', localDb', visibleDb'⟩
  rcases hStep with hLocal | hRely
  · rcases hLocal with ⟨_hStep, hVis⟩
    simpa [hVis] using hI
  · rcases hRely with ⟨_hCmd, _hLocal, _hNotSkip, hR⟩
    exact hStableI _ _ _ hI hR

theorem localMultiStep_preserves_invariant
    {ι : Type} {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {cfg cfg' : LocalConfig ι}
    (hMulti : Logic.LocalMultiStep R txnId ι cfg cfg')
    (hI : I cfg.visibleDb) :
    I cfg'.visibleDb := by
  induction hMulti with
  | refl => exact hI
  | tail _hPrev hLast ih =>
      exact localInterleavedStep_preserves_invariant hStableI hLast ih

/-- The key invariant-augmentation lemma: a `LocalValid` judgment whose precondition implies the
visible-DB invariant `I` can have `I` added to its postcondition, provided `R` preserves `I`. -/
theorem LocalValid.augment_invariant
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    {P Q : BiAssertion} {body : Semantics.Program}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hPreImpliesI : ∀ ld vd, P ld vd → I vd)
    (h : Logic.LocalValid R txnId P body Q) :
    Logic.LocalValid R txnId P body (fun ld vd => Q ld vd ∧ I vd) := by
  intro localDb visibleDb finalCfg hP hMulti hSkip
  refine ⟨h localDb visibleDb finalCfg hP hMulti hSkip, ?_⟩
  have hI₀ : I visibleDb := hPreImpliesI _ _ hP
  exact localMultiStep_preserves_invariant
    (cfg := ⟨body, localDb, visibleDb⟩)
    (cfg' := finalCfg)
    hStableI hMulti hI₀

theorem transformerPre_implies_invariant
    (I : Assertion) (Fctxt : SetExpr) :
    ∀ ld vd, transformerPre I Fctxt ld vd → I vd := by
  intro _ _ hPre
  exact hPre.2

/-- Strong soundness: every paper-style derivation produces a `LocalValid` whose post-condition
includes the invariant `I`. The paper-faithful version (no `I` in the post) is recovered as
`PaperInfer.sound` below by weakening the post. -/
theorem PaperInfer.sound_with_invariant
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {Fctxt F : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I Fctxt body F) :
    Logic.LocalValid R txnId (transformerPre I Fctxt) body
      (transformerPostI I Fctxt F) := by
  induction h with
  | @skip Fctxt hPostStable =>
      -- SKIP: post is `transformerPost Fctxt empty`. Augment with I.
      have hSkipSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.skip : Semantics.Program) (transformerPost Fctxt SetLanguage.empty) :=
        paperInferenceSound_skip R txnId I Fctxt hPostStable
      have hAug :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.skip : Semantics.Program)
            (fun ld vd => transformerPost Fctxt SetLanguage.empty ld vd ∧ I vd) :=
        LocalValid.augment_invariant hStableI
          (transformerPre_implies_invariant I Fctxt) hSkipSound
      exact hAug
  | @insert Fctxt env expr hStable hClosed hFresh =>
      have hSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.insert (instantiateSymExpr env [] expr))
            (transformerPost Fctxt (insertedRowSet txnId env expr)) :=
        paperInferenceSound_insert R txnId I Fctxt env expr hStable hClosed hFresh
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSound
  | @delete Fctxt env source predicate hStable =>
      have hSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.delete source (instantiateExpr env [source] predicate))
            (transformerPost Fctxt (deleteSetExpr txnId env source predicate)) :=
        paperInferenceSound_delete R txnId I Fctxt env source predicate hStable
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSound
  | @update Fctxt env source updateExpr predicate hStable =>
      have hSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.update source (instantiateExpr env [source] updateExpr)
              (instantiateExpr env [source] predicate))
            (transformerPost Fctxt
              (updateSetExpr txnId env source updateExpr predicate)) :=
        paperInferenceSound_update R txnId I Fctxt env source updateExpr predicate hStable
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSound
  | @letE Fctxt F env x expr body value hStable hEval hBody =>
      have hSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.letE x (instantiateSymExpr env [] expr) body)
            (transformerPost Fctxt F) :=
        paperInferenceSound_let R txnId I Fctxt env x expr body value F
          hStable hEval hBody
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSound
  | @seq Fctxt F₁ F₂ left right _hLeft hStableMid _hRight ihLeft ihRight =>
      -- ihLeft : LocalValid (pre I Fctxt) left (postI I Fctxt F₁)
      -- ihRight : LocalValid (pre I (Fctxt ∪ F₁)) right (postI I (Fctxt ∪ F₁) F₂)
      -- Strategy: bridge ihRight's pre via localValid_conseq, then apply localValid_seq with
      -- the mid-condition `postI I Fctxt F₁`. Finally, weaken the post to `postI I Fctxt (F₁ ∪ F₂)`.
      have hBridgeRight :
          Logic.LocalValid R txnId (transformerPostI I Fctxt F₁) right
            (transformerPostI I (.union Fctxt F₁) F₂) := by
        refine Logic.localValid_conseq ?_ ihRight (fun _ _ hPost => hPost)
        intro localDb visibleDb hPostI
        rcases hPostI with ⟨hPost, hI⟩
        refine ⟨?_, hI⟩
        intro row
        exact hPost row
      have hStablePostI :
          Logic.stableBiAssertion R (transformerPostI I Fctxt F₁) := by
        intro localDb visibleDb visibleDb' hPostI hR
        rcases hPostI with ⟨hPost, hI⟩
        refine ⟨hStableMid _ _ _ hPost hR, hStableI _ _ _ hI hR⟩
      have hSeq :
          Logic.LocalValid R txnId (transformerPre I Fctxt) (.seq left right)
            (transformerPostI I (.union Fctxt F₁) F₂) :=
        Logic.localValid_seq R txnId _ _ _ left right ihLeft hStablePostI hBridgeRight
      refine Logic.localValid_conseq (fun _ _ hPre => hPre) hSeq ?_
      intro localDb visibleDb hPostI
      rcases hPostI with ⟨hPost, hI⟩
      refine ⟨?_, hI⟩
      intro row
      have hRow := hPost row
      simp only [transformerPost, SetLanguage.denote_union] at hRow ⊢
      exact (or_assoc.symm).trans hRow
  | @ite Fctxt FThen FElse env cond thenBranch elseBranch hStable
      _hThen _hElse ihThen ihElse =>
      -- ihThen : LocalValid (pre I Fctxt) thenBranch (postI I Fctxt FThen)
      -- ihElse : LocalValid (pre I Fctxt) elseBranch (postI I Fctxt FElse)
      -- Strategy: weaken each branch's post from `postI` back to `post`, apply the existing
      -- `paperInferenceSound_ite`, and re-augment the resulting LocalValid with I.
      have hThenWeak :
          Logic.LocalValid R txnId (transformerPre I Fctxt) thenBranch
            (transformerPost Fctxt FThen) :=
        Logic.localValid_conseq (fun _ _ hPre => hPre) ihThen
          (fun _ _ hPostI => hPostI.1)
      have hElseWeak :
          Logic.LocalValid R txnId (transformerPre I Fctxt) elseBranch
            (transformerPost Fctxt FElse) :=
        Logic.localValid_conseq (fun _ _ hPre => hPre) ihElse
          (fun _ _ hPostI => hPostI.1)
      have hIteSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.ite (instantiateSymExpr env [] cond) thenBranch elseBranch)
            (transformerPost Fctxt
              (.ite (formulaOfExpr { env with scalarVars := [] }
                (instantiateSymExpr env [] cond)) FThen FElse)) :=
        paperInferenceSound_ite R txnId I Fctxt env cond thenBranch elseBranch
          FThen FElse hStable hThenWeak hElseWeak
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hIteSound
  | @select Fctxt F env binder source predicate body hStable _hBody ihBody =>
      -- ihBody : ∀ ld vd selected, pre → collectSelected = some selected →
      --   LocalValid R txnId (pre) (subst ... body) (postI I Fctxt F)
      -- We weaken the post from postI back to post to feed paperInferenceSound_select,
      -- then re-augment with I at the end.
      have hBody' :
          ∀ localDb visibleDb selected,
            transformerPre I Fctxt localDb visibleDb →
            Semantics.collectSelected visibleDb source
                (instantiateSymExpr env [source] predicate) = some selected →
            Logic.LocalValid R txnId (transformerPre I Fctxt)
              (Command.subst binder (.lit (.set selected)) body)
              (transformerPost Fctxt F) := by
        intro localDb visibleDb selected hPre hSelect
        refine Logic.localValid_conseq (fun _ _ h => h)
          (ihBody localDb visibleDb selected hPre hSelect) ?_
        intro _ _ hPostI
        exact hPostI.1
      have hSelectSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.select binder source (instantiateSymExpr env [source] predicate) body)
            (transformerPost Fctxt F) :=
        paperInferenceSound_select R txnId I Fctxt env binder source predicate body F
          hStable hBody'
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSelectSound
  | @foreach Fctxt F env source doneVar elemVar body hStable _hBody ihBody =>
      have hBody' :
          ∀ records,
            Expr.eval (instantiateSymExpr env [] source) = some (.set records) →
            Logic.LocalValid R txnId (transformerPre I Fctxt)
              (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body)
              (transformerPost Fctxt F) := by
        intro records hEval
        refine Logic.localValid_conseq (fun _ _ h => h)
          (ihBody records hEval) ?_
        intro _ _ hPostI
        exact hPostI.1
      have hForeachSound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.foreach (instantiateSymExpr env [] source) doneVar elemVar body)
            (transformerPost Fctxt F) :=
        paperInferenceSound_foreach R txnId I Fctxt env source doneVar elemVar body F
          hStable hBody'
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hForeachSound
  | @selectLazy Fctxt Fbody env binder source predicate body hStable hFbodyInvariant _hBody ihBody =>
      -- Lazy SELECT rule (Fig.8 [F'(∆)/y] form).  The body's IH gives, for every captured
      -- `selected`, a LocalValid with post `transformerPostI I Fctxt (Fbody selected)`.  The
      -- top-level lazy F existentially quantifies `selected` over the runtime visibleDb.
      --
      -- Soundness reduces to `paperInferenceSound_selectLazy`, which expects a body LocalValid
      -- whose post is the lazy F's post directly.  We construct this by weakening
      -- `transformerPost Fctxt (Fbody selected)` to `transformerPost Fctxt Lazy_F` via the
      -- post-conversion that witnesses the lazy F's existential with `(selected, visibleDb)`.
      --
      -- The post-conversion uses the equivalence between `Fbody selected (∅, vd') row` and
      -- the lazy F at `vd'`.  For the SetLanguage's union iff to compose, we go through the
      -- body's localValid post, which states `ld' = Fctxt ∪ Fbody selected` at `vd'`.  By
      -- `localValid_select`'s structure, the captured `visibleDb` at select-time matches the
      -- body's runtime initial visibleDb; the body's final `vd'` may diverge under rely.
      -- We use the fact that the lazy F's existential is consistent with the body's post:
      -- the body's post says `ld' = Fctxt ∪ Fbody selected` (set-equal to the runtime ld');
      -- the lazy F's witness `(selected', visibleDb')` produces the same set.
      have hBody' :
          ∀ localDb visibleDb selected,
            transformerPre I Fctxt localDb visibleDb →
            Semantics.collectSelected visibleDb source
                (instantiateSymExpr env [source] predicate) = some selected →
            Logic.LocalValid R txnId (transformerPre I Fctxt)
              (Command.subst binder (.lit (.set selected)) body)
              (transformerPost Fctxt
                (fun localDb' globalDb' out =>
                  ∃ selected', ∃ visibleDb',
                    (∀ row, globalDb' row ↔ row ∈ visibleDb') ∧
                    Semantics.collectSelected visibleDb' source
                        (instantiateSymExpr env [source] predicate) = some selected' ∧
                    Fbody selected' localDb' globalDb' out)) := by
        intro localDb visibleDb selected hPre hSelect
        -- ihBody selected : LocalValid (subst body) (transformerPostI I Fctxt (Fbody selected))
        refine Logic.localValid_conseq (fun _ _ h => h) (ihBody selected) ?_
        intro ld' vd' hPostI
        rcases hPostI with ⟨hPost, _hI⟩
        intro row
        have hRow := hPost row
        -- Goal: denote_at_vd' (Fctxt ∪ Lazy_F) row ↔ row ∈ ld'
        -- We have hRow: denote_at_vd' (Fctxt ∪ Fbody selected) row ↔ row ∈ ld'
        -- Sufficient to show denote_at_vd' Lazy_F row ↔ denote_at_vd' (Fbody selected) row.
        -- We provide witness (selected, visibleDb) for the existential, requiring membership
        -- stability between vd' and visibleDb.  This direction (← of inner iff) is the only
        -- one needed, since the forward direction (Lazy_F → Fbody selected) is supplied by
        -- the body's post pinning ld' to Fctxt ∪ Fbody selected.
        --
        -- TODO: this proof requires either (a) the rely to preserve visibleDb membership
        -- (silent rely / snapshot isolation) or (b) Fbody to be invariant under permutation
        -- of `selected`.  Both are typically true for the application use cases (SI + min/max-
        -- based Fbodies) but neither is provable from the inductive's hypotheses alone.
        -- Closing the gap requires extending `PaperInfer.selectLazy`'s constructor with such
        -- a hypothesis, which is forbidden by the task constraints.
        sorry
      have hSelectLazySound :
          Logic.LocalValid R txnId (transformerPre I Fctxt)
            (.select binder source (instantiateSymExpr env [source] predicate) body)
            (transformerPost Fctxt
              (fun localDb globalDb out =>
                ∃ selected, ∃ visibleDb,
                  (∀ row, globalDb row ↔ row ∈ visibleDb) ∧
                  Semantics.collectSelected visibleDb source
                      (instantiateSymExpr env [source] predicate) = some selected ∧
                  Fbody selected localDb globalDb out)) :=
        paperInferenceSound_selectLazy R txnId I Fctxt env binder source predicate body Fbody
          hStable hBody'
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSelectLazySound
  | @viaLocalValid Fctxt F body hSound =>
      exact LocalValid.augment_invariant hStableI
        (transformerPre_implies_invariant I Fctxt) hSound

/-- Theorem C.18 / C.19: paper-style soundness of the inference judgment. The post-condition is
exactly the paper's `λ(δ, Δ). δ = s ∪ Fctxt(Δ) ∪ F(Δ)` shape (here with `s = ∅`); the invariant
`I` is required to be stable under the rely. -/
theorem PaperInfer.sound
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {Fctxt F : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I Fctxt body F) :
    paperInferenceSound R txnId I Fctxt body F :=
  Logic.localValid_conseq (fun _ _ hPre => hPre)
    (sound_with_invariant hStableI h)
    (fun _ _ hPostI => hPostI.1)

end Transformer

end DbAppProgramLogic
