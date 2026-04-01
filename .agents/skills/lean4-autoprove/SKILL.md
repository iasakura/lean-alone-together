---
name: lean4-autoprove
description: Use when you want unattended autonomous Lean proving with hard stop rules, periodic review/replan, and a structured final summary.
---

# Lean4 Autoprove Skill

Codex translation of Claude `/lean4:autoprove`: autonomous multi-cycle proving with strict stop conditions.

## Inputs

- Optional scope and runtime limits
- Batch size, review cadence, deep-mode budgets
- Commit mode (default autonomous)

## Procedure

1. Startup discovery (no questionnaire): collect diagnostics, sorry inventory, initial candidates.
2. Run cycle engine repeatedly:
   - Plan -> Work -> Checkpoint -> Review -> Replan -> Continue
3. Apply hard stop conditions each cycle boundary:
   - Completion
   - Max stuck cycles
   - Max cycles
   - Max runtime
   - User interrupt
4. Emit final structured stop summary with handoff recommendations.

## Safety Constraints

- Same proof-safety rules as guided mode: no statement/type/docstring changes without approval.
- Respect deep budgets and rollback on regression.
- Coerce interactive-only options into autonomous-safe behavior.

## Stop Conditions

- First matched hard stop condition.

## Deliverables

- Structured run report (reason stopped, before/after metrics, blockers).
- Clear handoff: either next autonomous run or switch to `lean4-prove`.

## References

- `../lean4/references/cycle-engine.md`
- `../lean4/references/sorry-filling.md`
- `../lean4/references/compiler-guided-repair.md`
