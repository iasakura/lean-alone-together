---
name: lean4-mvcgen
description: Use when proving correctness of imperative Lean do-notation programs with Std.Do.mvcgen, including loop invariants, early return, effectful monads, Hoare triples, exceptions, and custom WP/WPMonad extensions.
---

# Lean4 MVCGen Skill

Use this skill when the task is about verification of imperative Lean programs with `Std.Do` tactics and assertions.

## Procedure

1. Ensure target files import the required module (typically `import Std.Tactic.Do`).
2. For `Id.run do` style correctness proofs:
   - Use `generalize` + `Id.of_wp_run_eq`.
   - Run `mvcgen`.
   - Instantiate loop invariants (`case inv1 => ...`).
   - Simplify VCs with `all_goals mleave`.
   - Discharge with `grind`/`simp`/targeted tactics.
3. For effectful monads (`StateM`, `EStateM`, transformer stacks):
   - Use the matching `of_wp_run...` lemma.
   - Prefer compositional `@[spec]` lemmas over broad unfolding.
4. Keep theorem statements unchanged unless explicitly approved.
5. Read and follow the full reference document before significant edits.

## Full Reference

- `references/mvcgen-verification.md`

This reference is intentionally included in full, without shortening.
