---
name: lean4
description: Use when editing Lean 4 files or handling build/proof errors and you need the hub workflow that routes to prove/autoprove/checkpoint/review/golf/doctor skills.
---

# Lean4 Hub Skill

Use this as the default Lean entrypoint. It routes work to focused subskills and keeps safety constraints consistent.

## Inputs

- Target scope: project, file, theorem, or single `sorry`
- Current issue: build error, missing proof, optimization, diagnostics
- Preferred mode: guided or autonomous

## Procedure

1. Classify the request:
   - Fill/fix proofs interactively -> `../lean4-prove/SKILL.md`
   - Fill/fix proofs autonomously -> `../lean4-autoprove/SKILL.md`
   - Create verified savepoint -> `../lean4-checkpoint/SKILL.md`
   - Read-only quality audit -> `../lean4-review/SKILL.md`
   - Proof optimization -> `../lean4-golf/SKILL.md`
   - Environment/plugin troubleshooting -> `../lean4-doctor/SKILL.md`
2. Use LSP-first flow before script fallbacks.
3. Load only needed references from `references/`.
4. Run scripts from `scripts/` using relative paths first.

## Safety Constraints

- Never change theorem/lemma statements, type signatures, or docstrings without explicit user approval.
- Keep edits scoped to requested targets.
- Avoid destructive git operations and avoid amend/push unless explicitly requested.
- Prefer `lean_diagnostic_messages` and file-level checks before project-wide `lake build`.

## Stop Conditions

- Requested issue is resolved in agreed scope.
- Blocking ambiguity requires user decision.
- Tooling/environment prevents progress and doctor guidance is provided.

## Deliverables

- Implemented proof/build fixes or explicit next steps.
- Validation evidence (diagnostics/build status).
- Suggested next skill when a workflow transition is needed.

## Resource Map

- References: `references/*.md`
- Scripts: `scripts/*`
- Key script calls:
  - `python3 .agents/skills/lean4/scripts/sorry_analyzer.py . --format=summary --report-only`
  - `bash .agents/skills/lean4/scripts/check_axioms_inline.sh <target> --report-only`
