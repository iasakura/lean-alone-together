# Paper Alignment Status

Reviewed against `1710.09844v2.pdf`, especially Fig. 8, Fig. 13, Theorem 5.1, Theorem C.18, and
Theorem C.19.

## Restart status (current)

The restart from the paper appendix is in progress and the inference judgment of Fig. 13 is now
formalized as a Lean inductive, with the appendix soundness theorem proved against it. The legacy
"concrete VCG" line of development has been moved under `DbAppProgramLogic/Legacy/` and is no
longer the surface API.

| Concern | Status | Location |
|---|---|---|
| Fig. 13 inference judgment `Fctxt ⊢ c ⟹⟨i,R,I⟩ F` | Formalized as `PaperInfer` | `DbAppProgramLogic/Transformer/Inference.lean` |
| Theorem C.18 (paper inference soundness) | Proved as `PaperInfer.sound` | `DbAppProgramLogic/Transformer/InferenceSoundness.lean` |
| C.18 with `I` carried in the post | Proved as `PaperInfer.sound_with_invariant` | same |
| Stabilization operator `⌊·⌋⟨R,I⟩` | Defined; `subset_stabilize` proved | `DbAppProgramLogic/Transformer/Stabilize.lean` |
| Per-rule local soundness lemmas | `paperInferenceSound_{skip,insert,delete,update,let,seq,ite}` | `DbAppProgramLogic/Transformer/Paper.lean` |
| `SELECT` and `FOREACH` constructors | First-class constructors of `PaperInfer`, plumbed through soundness | `Inference.lean`, `InferenceSoundness.lean`, `Select.lean`, `Foreach.lean` |
| Standard-axiom hygiene | `PaperInfer.sound` and `PaperInfer.sound_with_invariant` depend only on `[propext, Classical.choice, Quot.sound]` | verified via `#print axioms` |

`PaperInfer.sound` has the shape

```
∀ R txnId I Fctxt body F,
  PaperInfer R txnId I Fctxt body F →
  Logic.LocalValid R txnId (transformerPre I Fctxt) body (transformerPost Fctxt F)
```

which matches Theorem C.18 of the appendix once the precondition/postcondition shapes from
Theorem 5.1 are unfolded. `PaperInfer.sound_with_invariant` strengthens the post by additionally
carrying `I` on the visible database — useful as an internal lemma when chaining sequential rules
that each need `I` at the mid-point.

## What is clearly aligned with the paper

- `DbAppProgramLogic/SetLanguage.lean`
  - `SetExpr := localDb -> globalDb -> set of rows` is a shallow encoding of the paper's `S`.
  - This is not a problem by itself. It changes representation, not the intended denotation.
- `DbAppProgramLogic/Transformer/Basic.lean`
  - `transformerPre` matches the precondition shape from Theorem 5.1 / C.18 / C.19.
  - `transformerPost` matches the postcondition shape from Theorem 5.1 / C.18 / C.19.
  - `paperInferenceSound` is the right local-soundness target shape.
- `DbAppProgramLogic/Transformer/Inference.lean`
  - `PaperInfer` is the inductive judgment of Fig. 13 (constructors `skip`, `insert`, `delete`,
    `update`, `letE`, `seq`, `ite`, `select`, `foreach`, plus a `viaLocalValid` escape hatch).
- `DbAppProgramLogic/Transformer/InferenceSoundness.lean`
  - `PaperInfer.sound` (Theorem C.18) and `PaperInfer.sound_with_invariant`.
- `DbAppProgramLogic/Transformer/Stabilize.lean`
  - `stabilize`, `StableSetExpr`, `stableSetExpr_stabilize`, `subset_stabilize`.
- `DbAppProgramLogic/Transformer/Paper.lean`
  - Per-rule local soundness lemmas listed above.
- `DbAppProgramLogic/Transformer/Select.lean`
  - `paperInferenceSound_select` and helpers (`paperInferenceSound_select_of_materializedSet`,
    `paperInferenceSound_select_of_evalEq`, `paperInferenceSound_select_emptyEnv`).
- `DbAppProgramLogic/Transformer/Foreach.lean`
  - `paperInferenceSound_foreach` and helpers.

## What lives under `Legacy/` (not the paper formalization)

These files implement the older "concrete VCG" line: total recursive effect inference over closed
programs and database-indexed weakening lemmas. They are kept because some downstream examples
(`Refinement.lean`, `Examples.lean`, `AppWorkflowExample.lean`, `ReadWriteWorkflowExample.lean`,
`FirstOrder.lean`) still consume them, but new development should not rely on them.

- `DbAppProgramLogic/Legacy/Transformer/Concrete.lean`
- `DbAppProgramLogic/Legacy/Transformer/SetEffect.lean`
- `DbAppProgramLogic/Legacy/Transformer/PaperEffect.lean`
  - Holds `inferPaperEffect`/`inferPaperForeach` and their closed-form lemmas. These were the wrong
    direction for the inference judgment (a total function on closed syntax, instead of the
    relational judgment of Fig. 13).
- `DbAppProgramLogic/Legacy/Transformer/Soundness.lean`
  - Concrete-VCG soundness (`vcg_sound`, `symbolicVcg_*`) and partially-completed
    `paperInferenceSound_all` (still has `sorry`s — superseded by `PaperInfer.sound`).

## What still belongs in `Transformer/Basic.lean` but is not the paper

`Basic.lean` still hosts the symbolic environment machinery and concrete-direction definitions used
by downstream examples. The paper-aligned core (`transformerPre`, `transformerPost`,
`paperInferenceSound`) lives there too.

- Concrete-pipeline declarations still in `Basic.lean` (used by examples):
  - `inferenceSoundEnv`, `inferenceSound`, `TransactionVCG`, `vcg`, `vcgForTxn`,
    `weakenSetEffect`, `effectPost`.
  - These are out of scope for the paper-aligned core. Long-term they should also migrate to
    `Legacy/`, coordinated with rewrites of the consuming examples.

## Bottom line

- The paper-aligned nucleus is now:
  - `SetLanguage`
  - `transformerPre`, `transformerPost`, `paperInferenceSound`
  - the local RG lemmas in `Paper.lean`
  - `Stabilize.lean` (`⌊·⌋⟨R,I⟩`)
  - `Inference.lean` (`PaperInfer`, the Fig. 13 judgment)
  - `InferenceSoundness.lean` (Theorem C.18 as `PaperInfer.sound`)
- The aggregator `DbAppProgramLogic/Transformer.lean` exposes only paper-aligned files. The legacy
  concrete-VCG line is reachable only via `DbAppProgramLogic/Legacy.lean`.
- Remaining cleanup: migrate the still-in-`Basic.lean` concrete pipeline to `Legacy/` once the
  downstream examples are rewritten on top of `PaperInfer`.
