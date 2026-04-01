---
name: lean4-checkpoint
description: Use when you need a verified Lean save point by running build + axiom/sorry checks and then creating a checkpoint commit.
---

# Lean4 Checkpoint Skill

Codex translation of Claude `/lean4:checkpoint`: make a verified checkpoint commit.

## Inputs

- Optional custom commit message suffix
- Target scope (usually current project)

## Procedure

1. Verify project build (`lake build`).
2. Run axiom check script on target Lean files.
3. Run sorry summary script.
4. If checks pass and there is a non-empty diff, stage and commit.
5. Report commit hash, build status, and remaining sorry count.

## Safety Constraints

- Never push or open PR automatically.
- Never create empty commits.
- Abort commit creation if build fails.

## Stop Conditions

- Successful checkpoint created.
- Verification failure with actionable diagnostics.

## Deliverables

- Checkpoint commit metadata or failure report.
- Suggested immediate next step (`lean4-prove` or `lean4-review`).

## Scripts

- `bash .agents/skills/lean4/scripts/check_axioms_inline.sh <target>`
- `python3 .agents/skills/lean4/scripts/sorry_analyzer.py . --format=summary`
