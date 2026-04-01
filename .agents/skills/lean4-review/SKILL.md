---
name: lean4-review
description: Use when you need a read-only Lean proof quality review (batch or stuck triage) with scoped findings and actionable recommendations.
---

# Lean4 Review Skill

Codex translation of Claude `/lean4:review`: read-only quality review.

## Inputs

- Scope: `sorry`, `deps`, `file`, `changed`, or `project`
- Optional line number for sorry/deps modes
- Mode: `batch` or `stuck`

## Procedure

1. Resolve review scope.
2. Run read-only analysis:
   - Build/diagnostics checks
   - Sorry audit
   - Axiom audit
   - Style and optimization checks (batch mode)
3. Filter findings to requested scope.
4. Return prioritized recommendations.

## Safety Constraints

- Do not modify source files.
- Do not stage/commit.
- Ask confirmation before project-wide review if costly.

## Stop Conditions

- Full report generated for requested scope.
- Scope invalid or missing required context (report precise fix).

## Deliverables

- Review report with severity and file/line references.
- Optional follow-up plan for `lean4-prove`.

## Scripts

- `python3 .agents/skills/lean4/scripts/sorry_analyzer.py <target> --format=json --report-only`
- `bash .agents/skills/lean4/scripts/check_axioms_inline.sh <target> --report-only`
- `python3 .agents/skills/lean4/scripts/find_golfable.py <target> --filter-false-positives`
