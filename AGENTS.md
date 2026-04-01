# Project Instructions

Use Lean skills from `.agents/skills/` for all Lean-related tasks.

## Safety rules

- Do not change theorem/lemma statements, type signatures, or docstrings without explicit user approval.
- Prefer LSP-first verification (`lean_diagnostic_messages`, goal/hover/search) before heavy project-wide checks.
- Build loop order: diagnostics -> `lake env lean <file>` -> `lake build`.
- Avoid destructive git operations (`reset --hard`, `checkout --`, `clean -f`) unless explicitly requested.
- For workflow details, load the relevant skill under `.agents/skills/lean4*`.
