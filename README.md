# Lean formalization based on POPL'18 "Alone Together"

A Lean 4 formalization based on the program logic of `popl18.pdf` (Kaki et al., POPL 2018). The development covers:

- The core transaction language `T` (Fig. 5) — close to the paper
- Small-step operational semantics — close to the paper
- A rely-guarantee proof system in the spirit of Sec. 4 — see "Differences from the paper" below
- Inference of transaction effects, based on Sec. 5 — diverges from the paper in several places
- An application-facing wrapper for request/handler/server correctness — not in the paper

For a first pass through the codebase, start with [docs/WALKTHROUGH.md](docs/WALKTHROUGH.md); this README focuses on the paper-to-Lean correspondence. Other entry points:

- [docs/LANDMARKS.md](docs/LANDMARKS.md) — key definitions and theorems only
- [docs/VCG_EXAMPLE.md](docs/VCG_EXAMPLE.md) — what side conditions the VCG emits and how to discharge them
- [docs/EXAMPLES_GUIDE.md](docs/EXAMPLES_GUIDE.md) — where to read in `Examples.lean`
- [docs/APP_PROOF_TEMPLATE.md](docs/APP_PROOF_TEMPLATE.md) — how to verify your own app

This is not an end-to-end mechanization of the paper. In particular: the set language `S` of Fig. 7 is a shallow function-typed embedding rather than a deep syntactic language; Fig. 10's `S → FOL` translation is not implemented; there is no SMT integration; and several proof rules are restated in operationally convenient (but non-identical) forms. See "Differences from the paper" below.

## Repository layout

- `DbAppProgramLogic/Syntax.lean` — syntax of `T` (literals, expressions, commands)
- `DbAppProgramLogic/Semantics.lean` — values, evaluation, the runtime row/database model, isolation specs, local and top-level small-step semantics
- `DbAppProgramLogic/Logic.lean` — local/global judgments and their semantics, rely-guarantee rules, soundness, and a `par` rule (`GlobalRG.par`) drawn from Appendix B
- `DbAppProgramLogic/SetLanguage.lean` — a shallow `SetExpr` type and smart constructors patterned on Fig. 7, plus `weakenToInvariant` (and a currently-stub `abstractGlobal`)
- `DbAppProgramLogic/Transformer/` (re-exported as `DbAppProgramLogic.Transformer`) — paper-aligned semantic effect inference (`inferEffect`), per-statement symbolic constructors (`insertSetExpr`, `deleteSetExpr`, `updateSetExpr`), per-statement soundness (`paperInferenceSound_*`, `inferenceSoundEnv_*`), and a concrete `vcg` returning side conditions for a transaction body
- `DbAppProgramLogic/FirstOrder.lean` — a first-order `MembershipFormula` and a body-directed encoder (`inferMembershipFull*`); this is *not* Fig. 10's `S → FOL`
- `DbAppProgramLogic/Server.lean` — handler-level refinement (`HandlerRefines`), server wrappers using `ProgramDone` / `TxnCommitStep`, `ParallelValid`, and request/server specs (`StateSpec`, `RequestSpec`, `CommitSequence`, `CommitLog`) — not in the paper
- `DbAppProgramLogic/Legacy/` — an older "concrete VCG" line (`inferSetEffect`, `vcg_sound`, `symbolicVcg`, `symbolicPostForTxn`, …). Marked legacy in `DbAppProgramLogic/Legacy.lean`; downstream examples still depend on it, but new work should not
- `DbAppProgramLogic/Examples.lean`, `AppWorkflowExample.lean`, `ReadWriteWorkflowExample.lean` — small worked verifications and tutorial-style examples

## Paper-to-Lean correspondence

| Paper | Lean | Fidelity |
| --- | --- | --- |
| Fig. 5 syntax of `T` | `Syntax.lean` `Command` | Faithful; adds `foreachRuntime` / `txnRuntime` for the small-step semantics |
| Fig. 5 expressions / records | `Syntax.lean` `Expr`, `Literal`, `RecordLit`, `SetLit`; `Semantics.lean` `Value`, `Expr.eval` | Faithful; evaluation is made explicit |
| Fig. 5 local small-step | `Semantics.LocalStep` | Faithful for `let`, `if`, `seq`, `insert`, `delete`, `select`, `update`, `foreach` |
| Fig. 5 top-level small-step | `Semantics.Step` | Faithful for `txnStart`, `txnExec`, `txnCommit`, `par` |
| Hidden fields `txn`, `del` | `Semantics.Row`, `Row.fromInsert` | Faithful; runtime rows carry the metadata that surface records do not |
| Local store δ, global store Δ | `localDb`, `visibleDb`, `globalDb` | Faithful; held explicitly in configurations |
| Commit-time flush `▷` | `Semantics.Database.flush` | Faithful; deletes accumulate as `del = true` rows in δ and are removed on flush |
| Isolation spec | `Semantics.IsolationSpec` | Split into `exec` and `commit` as in §3 |
| `Iid` / `Iww` / `Iss` | `Database.uniqueIds`, `Database.writeWriteConflictFree`, `IsolationSpec.snapshot` | Faithful axiomatization |
| Snapshot isolation | `Database.snapshotIsolation` | Snapshot exec + write-write conflict avoidance |
| Fig. 6 RG rules (overall structure) | `Logic.LocalRG`, `GlobalRG` | Based on Fig. 6 but several rules differ in shape — see below |
| Sec. 4.1.1 stability | `Logic.stableAssertion`, `stableBiAssertion`, `stableIsolation`, `relyMod` | Uses single-step `R` plus a `stableIsolation` reachability condition; the paper uses `R*` (Sec. 4.1.1 also describes this single-step variant) |
| Theorem 4.3 (soundness) | `Logic.localRG_sound`, `globalRG_sound` | Soundness for the Lean rule system above |
| Fig. 7 set language `S` | `SetLanguage.SetExpr` (shallow) | `SetExpr := Database → Database → SetDenotation` — a shallow function-typed encoding with smart constructors named after Fig. 7 (`localDb`, `globalDb`, `comprehension`, `bind`, `ite`, `union`), not a deep inductive syntax |
| Fig. 7 weakening `T·U⟨R, I⟩` | `SetLanguage.weakenToInvariant` (and `abstractGlobal`) | `weakenToInvariant` existentially abstracts the global DB by the invariant; `abstractGlobal` is currently a no-op stub |
| Fig. 8 semantic transformer | `Transformer.inferEffect` | Returns a concrete delta, not a `SetExpr` |
| Fig. 8 symbolic transformer (per statement) | `Transformer.insertSetExpr`, `deleteSetExpr`, `updateSetExpr` and `paperInferenceSound_*` | Per-statement symbolic effects; a top-level `inferSetEffect` over whole bodies exists only in `Legacy/` |
| Theorem 5.1 | `paperInferenceSound_*`, `inferenceSoundEnv_*` (per construct); `Legacy.vcg_sound`, `vcg_sound_false`, `inferenceSound_all` (whole-body, legacy) | The current paper-aligned proofs are per-construct; the whole-body soundness lives in `Legacy/` |
| Concrete VCG | `Transformer.vcg`, `vcgForTxn` | Bundles effect, exec/commit stability, guarantee validity, invariant preservation; obligations are propositions, not solver-discharged |
| Sec. 5.2 `S → FOL` (Fig. 10) | Not implemented | `FirstOrder.encodeSetExprMembership` is a stub returning `none` |
| Membership-style FOL extraction | `FirstOrder.MembershipFormula`, `inferMembershipFull*` | Body-directed encoder that mirrors `inferEffect`; the soundness theorem ties it back to `inferEffect`, not to a generic `S → FOL` step |
| Sec. 5 transaction-level bridge | `Logic.txnGlobalValid_of_localValid` | Lifts `LocalValid` to `GlobalValid` |
| `par` rule | `Logic.GlobalRG.par` | Follows the standard RG `par` rule; Fig. 6 omits it ("illustrative subset") but Appendix B has the analogue |
| Handler specs | `Server.HandlerRefines`, `TxnIndexedRequestSpec`, `RequestSpec.hideTxnIds` | Extension layered above `GlobalValid`; not in the paper |
| Parallel / server quiescent semantics | `Logic.ProgramDone`, `TxnCommitStep`; `Server.ParallelValid` | Designed for API-server-like setups; not in the paper |
| Worked examples | `Examples.zeroBalanceInsert_valid`, `zeroBalanceTxn_parallelValid`, `addInterest*` | Insert-only invariant and a small `select + foreach + update` example |

## Differences from the paper

These are places where the README previously claimed close correspondence but the implementation differs.

**RG-Select shape.** Paper RG-Select introduces an auxiliary assertion P' that constrains the bound set variable, verifies the body under P', and requires `stable(R, P')`. Lean's `LocalRG.select` instead universally quantifies over the selected rows and substitutes them into the body literal — no P' is materialized. The two are equivalent under suitable substitutivity, but the rule shapes differ.

**RG-Foreach shape.** Paper RG-Foreach pivots on an explicit loop invariant ψ with side conditions `P ⇒ [∅/y]ψ`, `[y∪{z}/y]ψ` after one iteration, and `[x/y]ψ ⇒ Q`. Lean's `LocalRG.foreach` delegates to the runtime `foreachRuntime` form and does not surface an explicit ψ; the induction is done at the level of the runtime form's derivation. This works for the examples but is not the paper's rule.

**RG-Conseq scope.** The paper's RG-Conseq also lets you strengthen the isolation specification `ℐ` and shrink the rely `R`. Lean's `GlobalRG.conseq` only weakens `I` and strengthens `G`. Isolation strengthening is not done at the RG level.

**Stability uses single-step `R`, not `R*`.** Paper Sec. 4.1.1 defines `stable(R, φ)` via `R*` and then argues (under the stability-on-`ℐ` condition) that the single-step form suffices. Lean adopts the single-step form directly, with `stableIsolation` carrying the reachability-modulo-`R` premise. The paper itself describes this simplification.

**`SetExpr` is a shallow function encoding.** Fig. 7's `S` is a deep syntactic language (`s ::= x | δ | Δ | {x|φ} | exists(Δ,φ,s) | s₁ ≫= λx.s₂ | …`). Lean's `SetExpr` is `Database → Database → (Row → Prop)` with smart constructors named after the Fig. 7 forms. There is no first-class set variable, no `exists` syntax, and no metatheory over syntactic `S` (e.g. no Fig. 10 translation).

**`abstractGlobal` is a stub.** `SetLanguage.abstractGlobal _x s := s`. The actual existential abstraction is done by `weakenToInvariant` only.

**No `S → FOL`.** `FirstOrder.MembershipFormula` and `inferMembershipFull*` produce row-membership formulas directly from transaction bodies (in parallel with `inferEffect`). They do not implement Fig. 10's encoding of `SetExpr` into FOL — `encodeSetExprMembership` is a stub.

**`inferSetEffect` / `symbolicVcg` are legacy.** Whole-body symbolic inference (`inferSetEffect`), the weakened symbolic VCG (`symbolicVcg`, `symbolicVcgForTxn`, `symbolicPostForTxn`), and `vcg_sound` / `vcg_sound_false` live in `DbAppProgramLogic/Legacy/`. `Legacy.lean` explicitly notes they are *not* the paper-aligned formalization being built around `DbAppProgramLogic/Transformer/`. Downstream examples still consume them.

## Other encoding choices

**Databases as `List Row`.** The paper uses sets; we use `Database := List Row` with `RecordLit` (user-visible) and `Row` (runtime with hidden fields). This eases `flush`, append-based reasoning, and proof engineering, at the cost of list — not set — equality (order matters, e.g. for `foreach` soundness).

**Hidden fields are explicit.** `Row` exposes `visible`, `txn`, `del`. `INSERT` uses `Row.fromInsert`, `DELETE` accumulates `del = true` rows, and `UPDATE` accumulates rows with the new visible record.

**Local and global state are separated.** `LocalConfig` (`cmd`, `localDb`, `visibleDb`) vs `GlobalConfig` (`program`, `globalDb`). Matches the paper's local/global judgment split.

**Machine steps vs interference are distinct.** Real steps are `Semantics.LocalStep` / `Semantics.Step`; rely steps are `Logic.localInterleavedStep` / `globalInterleavedStep`. The rely is `Rely := Database → Database → Prop`; `relyMod` combines the global rely with the isolation guard. Global interleaving is single-track (Appendix C.2): rely steps change only the outer DB, and `txnRuntime`'s cached snapshot is consulted by `Step.txnExec`.

**`foreach` is deterministic.** With `Database = List Row` and list-equality postconditions, a genuinely nondeterministic iteration order makes soundness painful, so `foreachRuntime` runs in a fixed order.

## What is still missing

- Deep syntactic `S` and Fig. 10's `S → FOL` translation
- A general weakening calculus that produces the weakest stable transformer
- Solver-backed obligation discharge and weakest-isolation inference
- An end-to-end VCG-to-SMT pipeline
- Multi-table schemas, typed schemas, per-table invariants
- Realistic examples: a faithful Fig. 9 family, transaction families across endpoints, TPC-C
- A general parallel composition rule for handlers. `Server.lean` has single-handler `HandlerRefines`, quiescent `ParallelValid`, commit-order folding under closed-system assumptions, and projection lemmas for commit-free steps (`globalInterleavedStep_project_left_noncommit` / `..._right_noncommit`). The general `HandlerRefines h₁ → HandlerRefines h₂ → ParallelValid (h₁ ‖ h₂)` rule still requires the sibling-commit projection / simulation lemmas

## Reading order

Implementation order:

1. `Syntax.lean`
2. `Semantics.lean`
3. `Logic.lean`
4. `SetLanguage.lean`
5. `Transformer/Basic.lean` then the rest of `Transformer/`
6. `Server.lean`
7. `Examples.lean`

Paper order:

1. Fig. 5 → `Syntax.lean`, `Semantics.lean`
2. Fig. 6 → `Logic.lean` (with caveats above)
3. Theorem 4.3 → `localRG_sound`, `globalRG_sound`
4. Fig. 7 → `SetLanguage.lean` (shallow encoding)
5. Fig. 8 (semantic side) → `inferEffect`
6. Fig. 8 (symbolic side, per statement) → `paperInferenceSound_*`, `*SetExpr`
7. Theorem 5.1 → `paperInferenceSound_*`, `inferenceSoundEnv_*` (current); `Legacy.inferenceSound_all`, `Legacy.vcg_sound` (whole-body, legacy)
8. Transaction-level bridge → `txnGlobalValid_of_localValid`
9. App-facing wrapper (no paper counterpart) → `Server.lean`
