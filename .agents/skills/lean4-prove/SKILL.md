---
name: lean4-prove
description: Use when you want guided, cycle-by-cycle Lean proof development with explicit approvals between cycles and commit decisions.
---

# Lean4 Prove Skill

Codex translation of Claude `/lean4:prove`: guided proving with explicit checkpoints and user control.

## Inputs

- Optional scope (`File.lean`, theorem, or whole project)
- Optional flags: planning, review cadence, deep mode, commit policy
- Current compiler diagnostics and sorry locations

## Procedure

1. Plan cycle:
   - Discover errors/sorries via LSP.
   - Search for candidate lemmas/tactics.
   - Propose work order for current cycle.
2. Work cycle:
   - For each target sorry, produce 2-3 candidates.
   - Test candidates with Lean tools, keep shortest passing version.
   - Validate with diagnostics.
3. Checkpoint cycle:
   - If commit policy allows, stage touched files and commit.
4. Review/replan cycle:
   - Run scoped review on sorry/file boundaries.
   - Replan next cycle from blockers.
5. Ask whether to continue, stop, or adjust settings.

## Safety Constraints

- No statement/type/docstring changes without explicit approval.
- Keep fast-path edits small; avoid cross-file refactors unless explicitly allowed.
- Do not auto-loop forever; stop at cycle boundary for user decision.

## Stop Conditions

- User selects stop.
- Scope is complete (no remaining target sorries/errors).
- Repeated blocker requires escalation strategy decision.

## Deliverables

- Cycle summary: attempted targets, solved count, blockers.
- Committed or staged progress depending on policy.
- Recommended next action (`lean4-golf`, `lean4-checkpoint`, or targeted follow-up).

## References

- `../lean4/references/cycle-engine.md`
- `../lean4/references/sorry-filling.md`
- `../lean4/references/compilation-errors.md`
