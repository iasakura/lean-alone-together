import DbAppProgramLogic.Transformer.Basic
import DbAppProgramLogic.Transformer.Stabilize

namespace DbAppProgramLogic

namespace Transformer

/-!
Paper-style inference judgment from Fig. 13 of `1710.09844v2.pdf`.

Each constructor mirrors one rule of the appendix. Side-conditions that the paper writes inside
boxes (e.g. `stable(R, Fctxt)`) become explicit hypotheses on the constructor.

The accompanying soundness theorem (Theorem C.18 in the appendix) is proved in
`Transformer/InferenceSoundness.lean` by induction on this judgment, reusing the per-rule
soundness lemmas in `Transformer/Paper.lean`.

This file deliberately covers the rules already proved sound in `Paper.lean`: SKIP, INSERT,
DELETE, UPDATE, LET, SEQ, IF. The remaining rules (SELECT, FOREACH) are listed at the bottom as
stub constructors taking explicit local soundness witnesses; they will be turned into syntactic
constructors once `Select.lean` and `Foreach.lean` provide the full proof scaffolding.
-/

open SetLanguage

/-- The paper's inference judgment `Fctxt ⊢ c ⟹⟨i, R, I⟩ F`, indexed by the local rely `R`,
transaction id `txnId`, invariant `I`, ambient context effect `Fctxt`, body, and produced
effect `F`. -/
inductive PaperInfer (R : LocalRely) (txnId : TxnId) (I : Assertion) :
    SetExpr → Semantics.Program → SetExpr → Prop where
  /-- SKIP rule: the empty effect is produced for the no-op program, with the post-condition
  required to be stable so that the rule can be composed under `R`. -/
  | skip
      {Fctxt : SetExpr}
      (hPostStable : Logic.stableBiAssertion R (transformerPost Fctxt SetLanguage.empty)) :
      PaperInfer R txnId I Fctxt (.skip : Semantics.Program) SetLanguage.empty
  /-- INSERT rule: the produced effect is the singleton row built from the inserted record. The
  symbolic environment `env` is used to evaluate the record expression. -/
  | insert
      {Fctxt : SetExpr} {env : SymEnv} {expr : Expr}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hClosed :
        ∀ visibleDb row,
          evalExprInSetEnv env
              ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem "_row" row) expr =
            Expr.eval (instantiateSymExpr env [] expr))
      (hFresh :
        ∀ localDb visibleDb record,
          transformerPre I Fctxt localDb visibleDb →
          Expr.eval (instantiateSymExpr env [] expr) = some (.record record) →
          Semantics.insertFresh visibleDb localDb record) :
      PaperInfer R txnId I Fctxt
        (.insert (instantiateSymExpr env [] expr))
        (insertedRowSet txnId env expr)
  /-- DELETE rule: the produced effect is the set of rows the predicate selects from the global
  database. -/
  | delete
      {Fctxt : SetExpr} {env : Env}
      {source : VarName} {predicate : Expr}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
      PaperInfer R txnId I Fctxt
        (.delete source (instantiateExpr env [source] predicate))
        (deleteSetExpr txnId env source predicate)
  /-- UPDATE rule: the produced effect is the set of updated rows. -/
  | update
      {Fctxt : SetExpr} {env : Env}
      {source : VarName} {updateExpr predicate : Expr}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt)) :
      PaperInfer R txnId I Fctxt
        (.update source (instantiateExpr env [source] updateExpr)
          (instantiateExpr env [source] predicate))
        (updateSetExpr txnId env source updateExpr predicate)
  /-- LET rule: the body is verified after substituting the let-bound value. The produced effect
  is whatever effect the body produces. -/
  | letE
      {Fctxt F : SetExpr} {env : SymEnv}
      {x : VarName} {expr : Expr} {body : Semantics.Program} {value : Value}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hEval : Expr.eval (instantiateSymExpr env [] expr) = some value)
      (hBody :
        Logic.LocalValid R txnId (transformerPre I Fctxt)
          (Command.subst x value.toExpr body) (transformerPost Fctxt F)) :
      PaperInfer R txnId I Fctxt
        (.letE x (instantiateSymExpr env [] expr) body) F
  /-- SEQ rule: the second statement is verified under the extended context `Fctxt ⊎ F₁`. The
  combined effect is `F₁ ⊎ F₂`. -/
  | seq
      {Fctxt F₁ F₂ : SetExpr} {left right : Semantics.Program}
      (hLeft : PaperInfer R txnId I Fctxt left F₁)
      (hStableMid : Logic.stableBiAssertion R (transformerPost Fctxt F₁))
      (hRight : PaperInfer R txnId I (.union Fctxt F₁) right F₂) :
      PaperInfer R txnId I Fctxt (.seq left right) (.union F₁ F₂)
  /-- IF rule: each branch is verified under the same context, and the produced effect is the
  symbolic conditional of the two branch effects. -/
  | ite
      {Fctxt FThen FElse : SetExpr} {env : SymEnv} {cond : Expr}
      {thenBranch elseBranch : Semantics.Program}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hThen : PaperInfer R txnId I Fctxt thenBranch FThen)
      (hElse : PaperInfer R txnId I Fctxt elseBranch FElse) :
      PaperInfer R txnId I Fctxt
        (.ite (instantiateSymExpr env [] cond) thenBranch elseBranch)
        (.ite (formulaOfExpr { env with scalarVars := [] } (instantiateSymExpr env [] cond))
          FThen FElse)
  /-- SELECT rule (Fig. 13): the body is verified for each possible selected-set obtained from the
  predicate on the current visible database, via a recursive `PaperInfer` sub-derivation on the
  substituted body. -/
  | select
      {Fctxt F : SetExpr} {env : SymEnv}
      {binder source : VarName} {predicate : Expr} {body : Semantics.Program}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hBody :
        ∀ localDb visibleDb selected,
          transformerPre I Fctxt localDb visibleDb →
          Semantics.collectSelected visibleDb source
              (instantiateSymExpr env [source] predicate) = some selected →
          PaperInfer R txnId I Fctxt
            (Command.subst binder (.lit (.set selected)) body) F) :
      PaperInfer R txnId I Fctxt
        (.select binder source (instantiateSymExpr env [source] predicate) body) F
  /-- FOREACH rule (Fig. 13): the runtime body is verified against every possible evaluation of the
  source expression, via a recursive `PaperInfer` sub-derivation on the runtime-expanded body. -/
  | foreach
      {Fctxt F : SetExpr} {env : SymEnv}
      {source : Expr} {doneVar elemVar : VarName} {body : Semantics.Program}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hBody :
        ∀ records,
          Expr.eval (instantiateSymExpr env [] source) = some (.set records) →
          PaperInfer R txnId I Fctxt
            (.foreachRuntime (Expr.setLit []) (Expr.setLit records) doneVar elemVar body) F) :
      PaperInfer R txnId I Fctxt
        (.foreach (instantiateSymExpr env [] source) doneVar elemVar body) F
  /-- Lazy SELECT rule following the paper's Fig. 8 ST-SELECT formulation
  (`λ(∆). [F'(∆)/y] F(∆)`). The body's `F` is parameterized over the
  collected `selected` (i.e. the y binding), and the resulting top-level
  effect existentially quantifies `selected` against the runtime
  globalDb. This avoids the universal-quantification mismatch caused by
  baking `selected` into the body via `Command.subst` while the outer
  `F` still recomputes the aggregate from globalDb.

  `hFbodyInvariant` accommodates the gap between the paper's
  `Database`-indexed state transformer and our `SetDenotation`-indexed
  `SetExpr`: since `globalDb : Row → Prop` loses list order and
  multiplicity, the existential `∃ visibleDb` lets multiple set-equivalent
  list witnesses — and hence `collectSelected` results that differ as
  `SetLit`s but agree as sets. We require `Fbody` to depend only on the
  set of records in `selected` (not order/multiplicity). -/
  | selectLazy
      {Fctxt : SetExpr} {Fbody : SetLit → SetExpr} {env : SymEnv}
      {binder source : VarName} {predicate : Expr} {body : Semantics.Program}
      (hStable : Logic.stableBiAssertion R (transformerPre I Fctxt))
      (hFbodyInvariant :
        ∀ s₁ s₂ : SetLit,
          (∀ r, r ∈ s₁ ↔ r ∈ s₂) →
          Fbody s₁ = Fbody s₂)
      (hBody :
        ∀ selected,
          PaperInfer R txnId I Fctxt
            (Command.subst binder (.lit (.set selected)) body) (Fbody selected)) :
      PaperInfer R txnId I Fctxt
        (.select binder source (instantiateSymExpr env [source] predicate) body)
        (fun localDb globalDb out =>
          ∃ selected, ∃ visibleDb,
            (∀ row, globalDb row ↔ row ∈ visibleDb) ∧
            Semantics.collectSelected visibleDb source
                (instantiateSymExpr env [source] predicate) = some selected ∧
            Fbody selected localDb globalDb out)
  /-- Escape hatch: an external local-soundness witness. Kept for extensibility and for program
  shapes not yet covered by dedicated constructors. -/
  | viaLocalValid
      {Fctxt F : SetExpr} {body : Semantics.Program}
      (hSound :
        Logic.LocalValid R txnId (transformerPre I Fctxt) body (transformerPost Fctxt F)) :
      PaperInfer R txnId I Fctxt body F

end Transformer

end DbAppProgramLogic
