# Examples Guide

`DbAppProgramLogic/Examples.lean` is not meant to be read top-to-bottom as a linear story. The file
mixes:

- setup definitions,
- small helper lemmas,
- VCG examples,
- direct `GlobalRG` examples,
- server/refinement examples,
- symbolic/FOL examples.

The landmarks below are the intended entry points.

## 1. Smallest VCG proof

Read these declarations in order:

1. [zeroBalanceInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L94)
2. [zeroBalance_effect_defined](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L166)
3. [zeroBalance_guarantee_ok](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L172)
4. [zeroBalance_preserves_invariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L183)
5. [zeroBalanceInsert_valid_via_info](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L198)

What this shows:

- what `Transformer.vcg` returns,
- which obligations `vcg_sound_false` asks for,
- how little proof machinery is needed for a trivial `insert`.

## 2. First rely-aware VCG helper

Read:

1. [zeroBalance_vcg_effect_insert](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L242)
2. [zeroBalance_commitStable_any](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L278)
3. [zeroBalance_localValid_effectPost_readCommitted_of_stable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L303)
4. [zeroBalanceHandler_refines_graph_readCommitted_via_vcg_of_stable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L582)

What this shows:

- where the no-rely story stops being enough,
- the kind of custom helper usually needed before calling `vcg_sound`,
- how a VCG proof feeds into a server-facing handler refinement statement.

## 3. Direct use of the parallel proof rule

Read:

1. [zeroBalanceInsert_rg_readCommitted_of_stable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L375)
2. [zeroBalanceInsertTwo_rg_readCommitted_of_stable](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L424)
3. [zeroBalancePar_rg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L475)
4. [zeroBalancePar_valid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L492)

What this shows:

- how `GlobalRG.par` is actually used,
- what a hand-written parallel proof looks like,
- the proof-rule view before any refinement packaging.

## 4. End-to-end refinement example

Read:

1. [zeroBalanceTxn_parallelValid_exact_via_vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L541)
2. [zeroBalanceTxn_commitLog_via_vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L552)
3. [zeroBalancePar_request_foldl_via_vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L870)

What this shows:

- VCG obligations for each transaction,
- conversion to handler refinement,
- parallel composition,
- request-level `foldl` statement as the final observable result.

If your end goal is API/server correctness, this is the most important path.

## 5. Symbolic and first-order layers

For the simple `insert`, read:

- [zeroBalance_symbolicVcg_shape](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L902)
- [zeroBalance_inferWriteMembership](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L943)

For the read/write example, start from:

- [addInterestInfo](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean#L993)

and then read downward only if you specifically want symbolic `S` or first-order membership
encodings.

## What to skip on a first pass

You can safely skip on first reading:

- most `*_effect_*` helper lemmas,
- `*_flush_*` invariant-preservation lemmas,
- the symbolic/FOL block after `zeroBalancePar_request_foldl_via_vcg`,
- almost all of the `addInterest` section.

Those are support lemmas, not the main story.
