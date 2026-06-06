# Verifying database applications in Lean 4

The goal of this repository is to verify database applications — transactions
running under weakly isolated concurrency — in Lean 4.

It is loosely inspired by the POPL'18 paper *Alone Together: Compositional
Reasoning and Inference for Weak Isolation* (Kaki et al., 2018), but it is not
a mechanization of that paper. The transaction language, small-step semantics,
and rely-guarantee setup follow ideas from the paper; many proof rules, the
set-language encoding, and the inference pipeline differ in shape, and the
`S → FOL` / SMT-integration parts of the paper are not implemented.

## Repository layout

- `DbAppProgramLogic/Syntax.lean` — syntax of the core transaction language
- `DbAppProgramLogic/Semantics.lean` — values, evaluation, the runtime row/database model, isolation specifications, local and top-level small-step semantics
- `DbAppProgramLogic/Logic.lean` — local/global judgments, their semantics, rely-guarantee rules, and soundness
- `DbAppProgramLogic/SetLanguage.lean` — a shallow `SetExpr` type used by the symbolic effect inference, plus `weakenToInvariant` (and a `abstractGlobal` stub)
- `DbAppProgramLogic/Transformer/` — semantic effect inference (`inferEffect`), per-statement symbolic effects, `paperInferenceSound_*` / `inferenceSoundEnv_*`, and a concrete `vcg` returning the side conditions for a transaction body
- `DbAppProgramLogic/FirstOrder.lean` — first-order membership formulas extracted from transaction bodies
- `DbAppProgramLogic/Server.lean` — handler-level refinement (`HandlerRefines`), `ParallelValid`, and request/server specs (`StateSpec`, `RequestSpec`, `CommitSequence`, `CommitLog`) for API-server-shaped parallel handlers
- `DbAppProgramLogic/Refinement.lean` — handler refinement bridging `vcg_sound` into the server layer
- `DbAppProgramLogic/Legacy/` — older "concrete VCG" line (`inferSetEffect`, `vcg_sound`, `symbolicVcg`, …). Despite the directory name, paper-aligned files still depend on building-block lemmas defined here

## Examples

End-to-end:

- `DbAppProgramLogic/Transformer/LogStorageExample/` — **the example to read first.** A log-storage workflow with three transactions (`insertLog`, `archiveLog`, `selectAllLog`) composed in parallel under a rely-guarantee specification. The final theorem `selectAllLog_returnsPrefix_final` (in `Final.lean`) shows that every completed execution leaves the selected result table equal to a prefix of the generated log stream. This is currently the only end-to-end example that exercises the full stack — multiple transactions, non-trivial inter-transaction rely, and a meaningful application-level postcondition.

Smaller / exploratory:

- `DbAppProgramLogic/Examples.lean` — `zeroBalance*` (single-transaction VCG, parallel composition via `GlobalRG.par`) and `addInterest*` (read/write surfaces of the symbolic and first-order layers)
- `DbAppProgramLogic/AppWorkflowExample.lean` — tutorial-style walk-through of "I want to verify my own small application": event-sourced banking ledger, VCG, handler refinement, parallel composition
- `DbAppProgramLogic/ReadWriteWorkflowExample.lean` — VCG walkthrough on read/modify/write handlers; inspects the generated effect rather than proving a parallel server theorem
- `DbAppProgramLogic/Transformer/AuditLogExample.lean` — parallel INSERTs with a meaningful inter-transaction rely
- `DbAppProgramLogic/Transformer/InferenceCapstoneExample.lean` — a concrete INSERT transaction carried through the paper-aligned inference pipeline
- `DbAppProgramLogic/Transformer/InferenceExample.lean` — small `PaperInfer` cases (skip, INSERT)

## Suggested reading order

1. `Syntax.lean`
2. `Semantics.lean`
3. `Logic.lean`
4. `SetLanguage.lean`
5. `Transformer/Basic.lean` (then the rest of `Transformer/`)
6. `Server.lean`
7. `Transformer/LogStorageExample/` — start with `Spec.lean`, then `Final.lean`

## What's missing

- A complete weakening calculus
- Solver-backed obligation discharge / weakest-isolation inference
- An end-to-end VCG-to-SMT pipeline
- Multi-table / typed-schema support
- A general parallel composition rule for handlers (`Server.lean` has the single-handler case and projection lemmas for commit-free steps; sibling-commit projections are still needed)
