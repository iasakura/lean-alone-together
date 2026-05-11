import DbAppProgramLogic.Transformer.InferenceSoundness

/-!
Worked examples that use the paper-style inference judgment (`PaperInfer`, Fig. 13 of the arxiv
extended version `1710.09844v2.pdf`) to derive local Hoare triples through `PaperInfer.sound`
(Theorem C.18).

These examples are deliberately tiny: their purpose is to confirm that the paper-aligned nucleus
is usable end-to-end as an API, not to exercise the harder rules (SELECT/FOREACH) — those have
their own targeted sub-example lemmas in `Select.lean` / `Foreach.lean`.
-/

namespace DbAppProgramLogic

namespace Transformer

open SetLanguage

/-- The `PaperInfer` derivation for `skip` yields the empty effect, and `PaperInfer.sound` turns
it into the paper's local soundness statement. -/
theorem paperInfer_skip_sound
    (R : LocalRely) (txnId : TxnId) (I : Assertion) (Fctxt : SetExpr)
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hPostStable : Logic.stableBiAssertion R (transformerPost Fctxt SetLanguage.empty)) :
    paperInferenceSound R txnId I Fctxt .skip SetLanguage.empty :=
  PaperInfer.sound hStableI (.skip hPostStable)

/-- A two-step `skip ; skip` sequence inferred under an empty context produces effect
`empty ∪ empty`. The derivation is assembled from the primitive `skip` and `seq` constructors and
then discharged via `PaperInfer.sound`. -/
theorem paperInfer_skipSeqSkip_sound
    (R : LocalRely) (txnId : TxnId) (I : Assertion)
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hPostStableLeft :
      Logic.stableBiAssertion R (transformerPost SetLanguage.empty SetLanguage.empty))
    (hPostStableRight :
      Logic.stableBiAssertion R
        (transformerPost (SetExpr.union SetLanguage.empty SetLanguage.empty)
          SetLanguage.empty)) :
    paperInferenceSound R txnId I SetLanguage.empty
      (.seq .skip .skip)
      (SetExpr.union SetLanguage.empty SetLanguage.empty) :=
  PaperInfer.sound hStableI
    (.seq
      (.skip hPostStableLeft)
      hPostStableLeft
      (.skip hPostStableRight))

/-- Helper: under the empty symbolic environment, the closure side condition `hClosed` of
`PaperInfer.insert` reduces to "substituting any `_row` in `expr` is a no-op". We package this as
the `Expr.subst` no-op shape that the user can supply with `simp` or `rfl` for closed expressions
built from literals. -/
theorem paperInfer_insert_emptyEnv_hClosed_iff (expr : Expr) :
    (∀ visibleDb (row : Row),
        evalExprInSetEnv ({ scalarVars := [], setVars := [] } : SymEnv)
            ((SetLanguage.Env.ofDatabases [] visibleDb).bindElem "_row" row) expr =
          Expr.eval (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) [] expr))
      ↔
    (∀ row : Row,
        Expr.eval (Expr.subst "_row" (.lit (.record row.visible)) expr) =
          Expr.eval expr) := by
  constructor
  · intro h row
    have := h ([] : Database) row
    simpa [evalExprInSetEnv, instantiateSymExpr_noScalars,
      SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using this
  · intro h visibleDb row
    have := h row
    simpa [evalExprInSetEnv, instantiateSymExpr_noScalars,
      SetLanguage.Env.bindElem, SetLanguage.Env.ofDatabases] using this

/-- Concrete INSERT example using the `PaperInfer.insert` rule on an empty symbolic environment
and an empty context effect, with the inserted row built from a closed record literal of integer
literals. The user supplies only:

* the eval result of the literal,
* the freshness fact for the inserted record under the precondition, and
* the rely-stability of the precondition.

Everything else (closure of the literal, simplification of `instantiateSymExpr`, etc.) is
discharged automatically. -/
theorem paperInfer_insert_closedRecord_sound
    (R : LocalRely) (txnId : TxnId) (I : Assertion)
    (record : RecordLit) (fields : List (FieldName × Expr))
    (hLiterals : ∀ row : Row,
        Expr.eval (Expr.subst "_row" (.lit (.record row.visible)) (.record fields)) =
          Expr.eval (.record fields))
    (hEval : Expr.eval (.record fields) = some (.record record))
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hStablePre :
      Logic.stableBiAssertion R (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb record) :
    paperInferenceSound R txnId I SetLanguage.empty
      (.insert (.record fields))
      (insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.record fields)) := by
  have hInfer :
      PaperInfer R txnId I SetLanguage.empty
        (.insert (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) [] (.record fields)))
        (insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.record fields)) :=
    PaperInfer.insert
      (env := { scalarVars := [], setVars := [] })
      (expr := .record fields)
      hStablePre
      ((paperInfer_insert_emptyEnv_hClosed_iff (.record fields)).mpr hLiterals)
      (by
        intro localDb visibleDb record' hPre hEval'
        have hEq : record' = record := by
          have := hEval.symm.trans hEval'
          simp [instantiateSymExpr_noScalars] at this
          rcases this with rfl
          rfl
        subst hEq
        exact hFresh localDb visibleDb hPre)
  simpa [instantiateSymExpr_noScalars] using PaperInfer.sound hStableI hInfer

/-! ## Wrap-based soundness examples

Demonstrate the paper-faithful `⟦Fctxt[F]⟧⟨R,I⟩` operator's use via `PaperInfer.sound_wrapped`.

The key invariant: for any `PaperInfer` derivation producing some F, we can post-process to a
`LocalValid` triple whose post is a subset-style bound mentioning `stabilizeWrap R I Fctxt F`.
This wrapped post is *always* stable when `Fctxt` is `StableSetExprBi`-stable, regardless of
whether `F` itself is.
-/

/-- The `PaperInfer.skip` derivation, fed through the wrap. The resulting `LocalValid` uses the
subset post-condition with `stabilizeWrap` applied to the empty effect. -/
theorem paperInfer_skip_sound_wrapped
    (R : LocalRely) (txnId : TxnId) (I : Assertion) (Fctxt : SetExpr)
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hPostStable : Logic.stableBiAssertion R (transformerPost Fctxt SetLanguage.empty)) :
    Logic.LocalValid R txnId (transformerPre I Fctxt)
      (.skip : Semantics.Program)
      (transformerPostSubI I Fctxt
        (stabilizeWrap R I Fctxt SetLanguage.empty)) :=
  PaperInfer.sound_wrapped hStableI (.skip hPostStable)

/-- The `PaperInfer.insert` derivation for a closed record literal, fed through the wrap. -/
theorem paperInfer_insert_closedRecord_sound_wrapped
    (R : LocalRely) (txnId : TxnId) (I : Assertion)
    (record : RecordLit) (fields : List (FieldName × Expr))
    (hLiterals : ∀ row : Row,
        Expr.eval (Expr.subst "_row" (.lit (.record row.visible)) (.record fields)) =
          Expr.eval (.record fields))
    (hEval : Expr.eval (.record fields) = some (.record record))
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb))
    (hStablePre :
      Logic.stableBiAssertion R (transformerPre I SetLanguage.empty))
    (hFresh :
      ∀ localDb visibleDb,
        transformerPre I SetLanguage.empty localDb visibleDb →
        Semantics.insertFresh visibleDb localDb record) :
    Logic.LocalValid R txnId (transformerPre I SetLanguage.empty)
      ((.insert (.record fields)) : Semantics.Program)
      (transformerPostSubI I SetLanguage.empty
        (stabilizeWrap R I SetLanguage.empty
          (insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.record fields)))) := by
  have hInfer :
      PaperInfer R txnId I SetLanguage.empty
        (.insert (instantiateSymExpr ({ scalarVars := [], setVars := [] } : SymEnv) [] (.record fields)))
        (insertedRowSet txnId ({ scalarVars := [], setVars := [] } : SymEnv) (.record fields)) :=
    PaperInfer.insert
      (env := { scalarVars := [], setVars := [] })
      (expr := .record fields)
      hStablePre
      ((paperInfer_insert_emptyEnv_hClosed_iff (.record fields)).mpr hLiterals)
      (by
        intro localDb visibleDb record' hPre hEval'
        have hEq : record' = record := by
          have := hEval.symm.trans hEval'
          simp [instantiateSymExpr_noScalars] at this
          rcases this with rfl
          rfl
        subst hEq
        exact hFresh localDb visibleDb hPre)
  simpa [instantiateSymExpr_noScalars] using PaperInfer.sound_wrapped hStableI hInfer

/-- The wrap of an empty effect under empty context is essentially empty (modulo classical
stability check, but the result's denotation either way is trivial). Demonstrates how the
wrapped post-condition reduces in simple cases. -/
theorem stabilizeWrap_empty_empty_denote
    (R : LocalRely) (I : Assertion)
    (localDb : SetDenotation) (globalDb : SetDenotation) (row : Row) :
    stabilizeWrap R I SetLanguage.empty SetLanguage.empty localDb globalDb row →
      False := by
  classical
  intro h
  unfold stabilizeWrap at h
  by_cases hStable : Logic.stableBiAssertion R (transformerPost SetLanguage.empty SetLanguage.empty)
  · -- Stable branch: result is `empty`, which has no rows.
    simp [hStable, SetLanguage.empty] at h
  · -- Unstable branch: result is `weakenF I empty`, also no rows.
    simp [hStable, weakenF, SetLanguage.empty] at h

/-! ## Stability witness for wrap'd post: rely-flexible inserts

The plain `paperInfer_insert_closedRecord_sound` requires the user to discharge stability
of the unwrapped `transformerPost ∅ (insertedRowSet ...)` under R. For the `_wrapped` variant,
the wrap automatically delivers stability (in the weakened branch) and the only remaining
side-condition is `StableSetExprBi`-stability of `Fctxt = ∅` (trivially true).

This is the key payoff: a more permissive rely no longer forces the user to manually re-derive
that `Fctxt ∪ F` is stable — the wrap does it. -/

/-- For any rely `R`, the wrap of the canonical INSERT effect (`insertedRowSet`) under empty
context has `StableSetExprBi` stability automatically. -/
theorem stableSetExprBi_stabilizeWrap_insert
    (R : LocalRely) (I : Assertion) (txnId : TxnId) (env : SymEnv) (expr : Expr) :
    StableSetExprBi R
      (stabilizeWrap R I SetLanguage.empty (insertedRowSet txnId env expr)) := by
  classical
  refine stableSetExprBi_stabilizeWrap R I SetLanguage.empty (insertedRowSet txnId env expr) ?_
  intro _
  exact stableSetExprBi_insertedRowSet R txnId env expr

/-- The wrapped subset-post on `transformerPostSubI I ∅ (stabilizeWrap ...)` is stable, derived
from the trivial stability of `∅` and the auto-stability of the wrap. -/
theorem stable_transformerPostSubI_insert_wrap
    (R : LocalRely) (I : Assertion) (txnId : TxnId) (env : SymEnv) (expr : Expr)
    (hStableI : Logic.stableBiAssertion R (fun _ visibleDb => I visibleDb)) :
    Logic.stableBiAssertion R
      (transformerPostSubI I SetLanguage.empty
        (stabilizeWrap R I SetLanguage.empty (insertedRowSet txnId env expr))) :=
  transformerPostSubI_stable R I SetLanguage.empty
    (stabilizeWrap R I SetLanguage.empty (insertedRowSet txnId env expr))
    (stableSetExprBi_empty R)
    (stableSetExprBi_stabilizeWrap_insert R I txnId env expr)
    hStableI

end Transformer

end DbAppProgramLogic
