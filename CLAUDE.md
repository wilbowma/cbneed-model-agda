# cbneed-model-agda

Read `SUMMARY.md` first: goals, main findings, file map and open items.

## Working preferences

- Typecheck Agda only via `./check.sh` (Agda 2.7.0.1, stdlib 2.2). It caps
  the heap (`+RTS -M4G -RTS`) and sets a timeout; uncapped Agda once used
  32 GB on a 16 GB machine.
- Build the LaTeX documents with `pdflatex`, run twice.
- Don't use Python for file manipulation. Prefer the Edit tool for exact
  edits; keep shell edits (BSD sed) to mechanical multi-site changes. Never
  use perl `\x{..}` escapes (they corrupted UTF-8 once).
- Write PDF/LaTeX preview images to the session scratchpad and overwrite
  them; don't delete them.
- Derivation trees: don't widen the canvas. If a tree is too wide, split it
  into a named subderivation at a semantically interesting point.
- Don't change a definition's content while keeping an established name
  (e.g. a notion that isn't Felleisen's must not be called
  "macro-expressibility").
- In the LaTeX drafts, flag claims and citations for the author to review
  with `\todo` marginpars.
- Commit only when asked.
