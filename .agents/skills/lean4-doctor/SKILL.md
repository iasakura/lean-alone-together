---
name: lean4-doctor
description: Use when Lean tooling or plugin setup is broken and you need environment diagnostics, migration checks, or safe cleanup guidance.
---

# Lean4 Doctor Skill

Codex translation of Claude `/lean4:doctor`: diagnostics and migration/cleanup support.

## Inputs

- Mode: full, `env`, `migrate`, or `cleanup`
- Optional flags for global scan or apply cleanup

## Procedure

1. Check toolchain availability (`lean`, `lake`, `python3`, `git`, optional `rg`).
2. Check required directory layout and script availability.
3. Check project state (Lean project markers, build, sorry count).
4. For migration mode, detect legacy artifacts and stale env settings.
5. For cleanup mode, report removal commands; apply only with explicit approval.

## Safety Constraints

- Default to read-only diagnostics.
- Never remove files without explicit apply confirmation.
- Never modify Lean source as part of doctor workflow.

## Stop Conditions

- Diagnostic report is complete.
- Missing prerequisites prevent deeper checks.

## Deliverables

- Structured health report with pass/warn/fail markers.
- Concrete remediation commands.

## Scripts

- `python3 .agents/skills/lean4/scripts/sorry_analyzer.py . --format=summary --report-only`
- `bash .agents/skills/lean4/scripts/check_axioms_inline.sh <target> --report-only`
