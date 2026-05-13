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
  | @selectLazy Fctxt Fbody env binder source predicate body hStable hCollectStable
      _hBody ihBody =>
      -- Lazy SELECT rule (Fig.8 [F'(∆)/y] form). The body LocalValid produced by
      -- `Logic.localValid_select_collectInvariant` carries the
      -- `collectSelected vd_init src pred = some selected` witness in its
      -- precondition (paper p.45 strengthening `P'(δ,Δ) ⇔ P ∧ y = sel(Δ)`).
      -- Inside the body, `hCollectStable` propagates this through the rely
      -- multistep to `collectSelected finalCfg.vd`, allowing the bridge from
      -- `Fbody selected` (body's effect) to `LazyF` (outer existential effect).
      refine Logic.localValid_select_collectInvariant R txnId _ _ binder source
        (instantiateSymExpr env [source] predicate) body hStable ?_
      intro selected
      intro ld_init vd_init finalCfg hPreStrong hMulti hSkip
      rcases hPreStrong with ⟨hPreBody, hSelectInit⟩
      -- ihBody (selected) gives the body's `transformerPostI I Fctxt (Fbody selected)`.
      have hPostBody := (ihBody selected) ld_init vd_init finalCfg hPreBody hMulti hSkip
      rcases hPostBody with ⟨hPost, hI_final⟩
      -- Propagate `collectSelected` from `vd_init` to `finalCfg.visibleDb`.
      have hCollect_preserved :
          ∀ {cfg cfg' : LocalConfig (IsolationSpec Database)},
            Logic.LocalMultiStep R txnId (IsolationSpec Database) cfg cfg' →
            Semantics.collectSelected cfg.visibleDb source
                (instantiateSymExpr env [source] predicate) =
              Semantics.collectSelected cfg'.visibleDb source
                (instantiateSymExpr env [source] predicate) := by
        intro cfg cfg' hM
        induction hM with
        | refl => rfl
        | tail _hPrev hLast ih =>
            rcases hLast with hLocal | hRely
            · rcases hLocal with ⟨_hStep, hVisEq⟩
              exact ih.trans (by rw [hVisEq])
            · rcases hRely with ⟨_hCmd, _hLocal, _hNotSkip, hR⟩
              exact ih.trans (hCollectStable _ _ _ hR).symm
      have hSelectFinal :
          Semantics.collectSelected finalCfg.visibleDb source
              (instantiateSymExpr env [source] predicate) = some selected := by
        have hEq := hCollect_preserved
          (cfg := ⟨Command.subst binder (.lit (.set selected)) body, ld_init, vd_init⟩)
          (cfg' := finalCfg) hMulti
        exact hEq ▸ hSelectInit
      -- Bridge `Fbody selected` (body's effect) ↔ `LazyF` (outer effect) at
      -- `finalCfg.visibleDb`, using `hSelectFinal` as the existential witness.
      refine ⟨?_, hI_final⟩
      intro row
      have hPostRow := hPost row
      simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote,
        SetLanguage.Env.ofDatabases] at hPostRow ⊢
      constructor
      · rintro (hFctxt | hLazy)
        · exact hPostRow.mp (Or.inl hFctxt)
        · -- `hLazy : LazyF [] finalCfg.vd row` definitionally reduces to the existential.
          obtain ⟨selected', hSel', hFbody'⟩ := hLazy
          have hEq : selected' = selected := by
            rw [hSelectFinal] at hSel'
            exact (Option.some.inj hSel').symm
          subst hEq
          exact hPostRow.mp (Or.inr hFbody')
      · intro hRow
        rcases hPostRow.mpr hRow with hFctxt | hFbody
        · exact Or.inl hFctxt
        · exact Or.inr ⟨selected, hSelectFinal, hFbody⟩
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

/-- Paper Fig.8 wrap-aware soundness. The iff post from `PaperInfer.sound`
is lifted to the existential-wrapped post via `vd' := vd` witness, using `I vd`
preserved through `R` (via `localMultiStep_preserves_invariant`).

In the stable branch of `transformerPostWrapped`, the wrap forces `vd' = vd`
and the iff post is recovered exactly. In the unstable branch, `vd'` is free
and `vd' := vd` discharges the existential trivially. -/
theorem PaperInfer.sound_wrapped
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {Fctxt F : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I Fctxt body F) :
    paperInferenceSoundWrapped R txnId I Fctxt body F := by
  intro localDb visibleDb finalCfg hPre hMulti hSkip
  have hPost := PaperInfer.sound hStableI h localDb visibleDb finalCfg hPre hMulti hSkip
  have hIInit : I visibleDb := hPre.2
  have hIFinal : I finalCfg.visibleDb :=
    localMultiStep_preserves_invariant
      (cfg := ⟨body, localDb, visibleDb⟩)
      (cfg' := finalCfg)
      hStableI hMulti hIInit
  exact transformerPostWrapped_of_transformerPost hIFinal hPost

/-- Derived F-weakening combinator: if `PaperInfer ... F` holds and the iff-form
post `transformerPost Fctxt F` implies `transformerPost Fctxt F'` pointwise,
then `PaperInfer ... F'` holds. Internally uses `PaperInfer.viaLocalValid` +
`PaperInfer.sound` + `Logic.localValid_conseq`. Used at the "F-conversion"
points in example proofs (e.g. converting the constructor-natural F of `.ite`
to a denote-equivalent custom F like `archiveLogEffect_with_selected`). -/
theorem PaperInfer.conseqF
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {Fctxt F F' : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I Fctxt body F)
    (hFEq : ∀ localDb visibleDb,
      transformerPost Fctxt F localDb visibleDb →
      transformerPost Fctxt F' localDb visibleDb) :
    PaperInfer R txnId I Fctxt body F' := by
  refine PaperInfer.viaLocalValid ?_
  have hSound := PaperInfer.sound hStableI h
  exact Logic.localValid_conseq (fun _ _ hp => hp) hSound hFEq

/-- Invariant-aware variant of `PaperInfer.conseqF`: the F-equivalence may use
`I visibleDb` at the post point. This is needed when the bridge between F and
F' only holds at `I`-respecting databases (e.g. `LazyF ↔ archiveLogEffect`
requires `collectSelected vd ...` to succeed, which follows from `logSystemInv vd`).
`I` is propagated from the precondition through the rely multistep via
`localMultiStep_preserves_invariant`. -/
theorem PaperInfer.conseqF_withInv
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    {Fctxt F F' : SetExpr} {body : Semantics.Program}
    (h : PaperInfer R txnId I Fctxt body F)
    (hFEq : ∀ localDb visibleDb,
      I visibleDb →
      transformerPost Fctxt F localDb visibleDb →
      transformerPost Fctxt F' localDb visibleDb) :
    PaperInfer R txnId I Fctxt body F' := by
  refine PaperInfer.viaLocalValid ?_
  intro localDb visibleDb finalCfg hPre hMulti hSkip
  have hSound := PaperInfer.sound hStableI h
  have hPost := hSound localDb visibleDb finalCfg hPre hMulti hSkip
  have hIInit : I visibleDb := hPre.2
  have hIFinal : I finalCfg.visibleDb :=
    localMultiStep_preserves_invariant
      (cfg := ⟨body, localDb, visibleDb⟩)
      (cfg' := finalCfg)
      hStableI hMulti hIInit
  exact hFEq _ _ hIFinal hPost

/-- Derived `PaperInfer` rule for a stuck `.letE`: when the expression doesn't
evaluate, the letE never reduces, so any post-condition is vacuously valid.
Uses `viaLocalValid + Logic.localValid_letE_none` internally. Works under any
rely (the stuck-ness is purely operational). -/
theorem PaperInfer.letE_none
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    {Fctxt F : SetExpr}
    {x : VarName} {expr : Expr} {body : Semantics.Program}
    (hNone : Expr.eval expr = none) :
    PaperInfer R txnId I Fctxt (.letE x expr body) F := by
  refine PaperInfer.viaLocalValid ?_
  exact Logic.localValid_letE_none R txnId _ _ x expr body hNone

/-- Paper-aligned `PaperInfer` rule for `.select` with **invariant-strengthened
body precondition** (1710.09844v2.pdf, Appendix C p.45 SELECT case:
`P' = P ∧ y = {r ∈ Δ|[r/x]e}`).

The body LocalValid is proven under a strengthened pre that includes
`hSelect : collectSelected vd source predicate = some selected`. This is the
paper's body Hoare triple, where `y` is pinned to `collectSelected(Δ)`.

Internally uses `viaLocalValid + Logic.localValid_select_collectInvariant`,
but exposes a paper-faithful PaperInfer rule without forcing the user to use
`viaLocalValid` directly. -/
theorem PaperInfer.selectWithInvariant
    {R : LocalRely} {txnId : TxnId} {I : Assertion}
    {Fctxt F : SetExpr} {env : SymEnv}
    {binder source : VarName} {predicate : Expr} {body : Semantics.Program}
    (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
    (hBody :
      ∀ selected,
        Logic.LocalValid R txnId
          (fun ld vd =>
            transformerPre I Fctxt ld vd ∧
              Semantics.collectSelected vd source
                  (instantiateSymExpr env [source] predicate) = some selected)
          (Command.subst binder (.lit (.set selected)) body)
          (transformerPost Fctxt F)) :
    PaperInfer R txnId I Fctxt
      (.select binder source (instantiateSymExpr env [source] predicate) body) F := by
  refine PaperInfer.viaLocalValid ?_
  exact Logic.localValid_select_collectInvariant R txnId _ _ binder source _ body hStable hBody

end Transformer

end DbAppProgramLogic
