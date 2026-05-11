import DbAppProgramLogic.Logic
import DbAppProgramLogic.SetLanguage
import DbAppProgramLogic.Transformer.Basic

namespace DbAppProgramLogic

namespace Transformer

/-!
Stabilization operator `⟦·⟧⟨R,I⟩` from Fig. 8 of `1710.09844v2.pdf` (p. 20).

Paper definition (with `Fctxt[F]` denoting the context-filled transformer `λΔ. Fctxt(Δ) ∪ F(Δ)`):

```
⟦Fctxt[F]⟧⟨R,I⟩ = F                              if stable(R, Fctxt[F])
              = λΔ. ∃Δ'. I(Δ') ∧ F(Δ')         otherwise (Δ' fresh)
```

In our shallow `SetExpr := SetDenotation → SetDenotation → SetDenotation` encoding, "stability" of
a `SetExpr` `F` under a local rely `R` is the statement that `F`'s output rows are unchanged
across `R`-related global databases. We provide two flavours:

* `weakenF I F` — the "always weakened" branch of the wrap. Its output drops global-database
  dependence by existentially quantifying over `I`-satisfying databases.
* `stabilizeWrap R I Fctxt F` — the full paper operator, classically choosing between the
  pass-through and weakening branches.

The non-stable branch is always trivially stable. This is the key property that lets the
SELECT rule produce a uniform `F'` across rely-equivalent global states without the all-rely
quantification headache that motivated `selectLazy`/`localValid_select_false_pinVd` in earlier
attempts.
-/

open SetLanguage

/-- Bidirectional stability for a `SetExpr` under a local rely `R`, taken at the canonical
`localDb := []` interpretation used by `transformerPre`/`transformerPost`. -/
def StableSetExprBi (R : LocalRely) (F : SetExpr) : Prop :=
  ∀ (localDb : Database) (visibleDb visibleDb' : Database),
    R localDb visibleDb visibleDb' →
    ∀ row,
      F (fun r => r ∈ ([] : Database)) (fun r => r ∈ visibleDb) row ↔
        F (fun r => r ∈ ([] : Database)) (fun r => r ∈ visibleDb') row

/-- The "weakened" branch of the paper's `⟦·⟧⟨R,I⟩` operator: replace `F` with the union of all
`F(Δ')` over `I`-satisfying `Δ'`. This drops dependence on the global database entirely. -/
def weakenF (I : Assertion) (F : SetExpr) : SetExpr :=
  fun localDb _globalDb row =>
    ∃ db' : Database, I db' ∧ F localDb (fun r => r ∈ db') row

/-- `weakenF` ignores the global database, so it is trivially stable under any rely. -/
theorem stableSetExprBi_weakenF (R : LocalRely) (I : Assertion) (F : SetExpr) :
    StableSetExprBi R (weakenF I F) := by
  intro _ _ _ _ _
  unfold weakenF
  rfl

/-- Inclusion direction: every concrete denotation of `F` against the current global database lies
inside the weakened form, provided the current global database satisfies `I`. -/
theorem subset_weakenF
    (I : Assertion) (F : SetExpr)
    {localDb : SetDenotation} {db : Database}
    (hI : I db) :
    ∀ row, F localDb (fun r => r ∈ db) row → weakenF I F localDb (fun r => r ∈ db) row := by
  intro row hRow
  exact ⟨db, hI, hRow⟩

/-- The combined stability lemma: if both `Fctxt` and `F` are `StableSetExprBi`, then the joint
post-condition `transformerPost Fctxt F` is `stableBiAssertion`. -/
theorem stableBiAssertion_transformerPost
    (R : LocalRely) (Fctxt F : SetExpr)
    (hStableFctxt : StableSetExprBi R Fctxt)
    (hStableF : StableSetExprBi R F) :
    Logic.stableBiAssertion R (transformerPost Fctxt F) := by
  intro localDb visibleDb visibleDb' hPost hR row
  -- `hPost row`: denote (ofDb visibleDb) (Fctxt ∪ F) row ↔ row ∈ localDb
  -- Want: same at visibleDb'.
  -- Translate via hStableFctxt and hStableF.
  have hRow := hPost row
  simp only [transformerPost, SetLanguage.denote_union, SetLanguage.denote,
    SetLanguage.Env.ofDatabases] at hRow ⊢
  refine ⟨?_, ?_⟩
  · intro hUnion
    rcases hUnion with hCtx | hNew
    · apply hRow.mp
      exact Or.inl ((hStableFctxt _ _ _ hR row).mpr hCtx)
    · apply hRow.mp
      exact Or.inr ((hStableF _ _ _ hR row).mpr hNew)
  · intro hMem
    have hAlt := hRow.mpr hMem
    rcases hAlt with hCtx | hNew
    · exact Or.inl ((hStableFctxt _ _ _ hR row).mp hCtx)
    · exact Or.inr ((hStableF _ _ _ hR row).mp hNew)

/-- The full paper operator `⟦Fctxt[F]⟧⟨R,I⟩`. Classically chooses between the two branches based
on whether `transformerPost Fctxt F` is stable under `R`. -/
noncomputable def stabilizeWrap (R : LocalRely) (I : Assertion) (Fctxt F : SetExpr) : SetExpr := by
  classical
  exact if Logic.stableBiAssertion R (transformerPost Fctxt F) then F else weakenF I F

/-- Inclusion direction for the full wrap operator: every concrete denotation of `F` lies inside
`stabilizeWrap R I Fctxt F`, provided the current global database satisfies `I`. -/
theorem subset_stabilizeWrap
    (R : LocalRely) (I : Assertion) (Fctxt F : SetExpr)
    {localDb : SetDenotation} {db : Database}
    (hI : I db) :
    ∀ row,
      F localDb (fun r => r ∈ db) row →
        stabilizeWrap R I Fctxt F localDb (fun r => r ∈ db) row := by
  classical
  intro row hRow
  unfold stabilizeWrap
  by_cases hStable : Logic.stableBiAssertion R (transformerPost Fctxt F)
  · simp [hStable]; exact hRow
  · simp [hStable]; exact subset_weakenF I F hI row hRow

/-- The wrap is always `StableSetExprBi` provided either branch yields a stable expression. The
stable branch must be re-witnessed by the caller (because the underlying stability is at the
`BiAssertion` level, not the `SetExpr` level). -/
theorem stableSetExprBi_stabilizeWrap
    (R : LocalRely) (I : Assertion) (Fctxt F : SetExpr)
    (hStableF : Logic.stableBiAssertion R (transformerPost Fctxt F) → StableSetExprBi R F) :
    StableSetExprBi R (stabilizeWrap R I Fctxt F) := by
  classical
  unfold stabilizeWrap
  by_cases hStable : Logic.stableBiAssertion R (transformerPost Fctxt F)
  · simp [hStable]
    exact hStableF hStable
  · simp [hStable]
    exact stableSetExprBi_weakenF R I F

/-- Convenient form: the wrapped `transformerPost` is stable, parameterized by stability of
`Fctxt` as a `SetExpr`. -/
theorem stableBiAssertion_transformerPost_stabilizeWrap
    (R : LocalRely) (I : Assertion) (Fctxt F : SetExpr)
    (hStableFctxt : StableSetExprBi R Fctxt) :
    Logic.stableBiAssertion R (transformerPost Fctxt (stabilizeWrap R I Fctxt F)) := by
  classical
  unfold stabilizeWrap
  by_cases hStable : Logic.stableBiAssertion R (transformerPost Fctxt F)
  · simp [hStable]
  · simp [hStable]
    exact stableBiAssertion_transformerPost R Fctxt (weakenF I F) hStableFctxt
      (stableSetExprBi_weakenF R I F)

/-! ## Stability of common set expressions -/

/-- `SetLanguage.empty` is trivially stable under any rely. -/
theorem stableSetExprBi_empty (R : LocalRely) : StableSetExprBi R SetLanguage.empty := by
  intro _ _ _ _ _
  rfl

/-- Union of stable expressions is stable. -/
theorem stableSetExprBi_union (R : LocalRely) (s₁ s₂ : SetExpr)
    (h₁ : StableSetExprBi R s₁) (h₂ : StableSetExprBi R s₂) :
    StableSetExprBi R (SetExpr.union s₁ s₂) := by
  intro localDb visibleDb visibleDb' hR row
  simp only [SetExpr.union]
  rw [h₁ _ _ _ hR row, h₂ _ _ _ hR row]

/-- `singleton row₀` is trivially stable (doesn't depend on either database). -/
theorem stableSetExprBi_singleton (R : LocalRely) (row₀ : Row) :
    StableSetExprBi R (SetLanguage.singleton row₀) := by
  intro _ _ _ _ _
  rfl

/-- `insertedRowSet` is stable under any rely: its denotation depends only on the symbolic
environment and expression, not on the local/global databases. -/
theorem stableSetExprBi_insertedRowSet
    (R : LocalRely) (txnId : TxnId) (env : SymEnv) (expr : Expr) :
    StableSetExprBi R (insertedRowSet txnId env expr) := by
  intro _ _ _ _ _
  rfl

end Transformer

end DbAppProgramLogic
