---
name: lean4-golf
description: Use when Lean proofs already compile and you want safe proof simplification/shortening with regression checks.
---

# Lean4 Golf Skill

Codex translation of Claude `/lean4:golf`: optimize proofs for brevity while preserving behavior.

## Inputs

- Target: project, file, or file:line
- Mode: normal or `--dry-run`
- Search depth: `off`, `quick`, or `full`

## Procedure

1. Confirm baseline compiles/diagnostics are stable.
2. Detect golfable patterns.
3. Apply safe rewrites in small batches.
4. Re-run diagnostics after each batch.
5. Revert batch immediately on regression.
6. Summarize applied improvements and skipped risky cases.

## Safety Constraints

- No semantic rewrites without validation.
- Skip broad bulk rewrites in tactic/calc blocks unless explicitly requested.
- Revert any change that increases errors or sorry count.

## Stop Conditions

- No safe opportunities remain.
- User requests stop.
- Regression threshold exceeded.

## Deliverables

- List of optimized proofs with diff metrics.
- Residual optimization opportunities.

## Scripts

- `python3 .agents/skills/lean4/scripts/find_golfable.py <target> --filter-false-positives`
- `python3 .agents/skills/lean4/scripts/analyze_let_usage.py <target>`
