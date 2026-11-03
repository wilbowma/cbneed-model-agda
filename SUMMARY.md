Project summary (for resuming work)
==

Original goal: a total, structurally recursive *shallow* embedding of
call-by-need STLC in Agda whose heap holds semantic values, so that
allocation, sharing and deallocation are modelled. The heap is unobservable;
it matters for cost (sharing).

Main findings
--

- A shallow semantic heap is impossible for all of call-by-need STLC in
  predicative type theory. The heap-of-thunks circularity *is* the
  type-world circularity (Ahmed; Koronkevich & Bowman 2025), with the heap
  type as semantic world.
- Witness: `P = λg. g (λn. g (λm. m))`. Translated naively into λPR it needs
  `c ≥ a+1 ≥ d+1 ≥ b+2 ≥ c+2`; untranslated (CBV) it types at level 0. P
  defeats every well-founded stratification, not just λPR levels.
- Level-free promises have a logical relation (worlds = histories of
  *syntactic* stores), which proves termination but puts syntax in the heap.
- Expressiveness framing: **heap-adequate expressibility** = typed +
  compositional (fixed context per construct, never subterm syntax; pure
  constructs may be reinterpreted, so store-passing is allowed) +
  heap-adequate (at every evaluation boundary: related results; injective
  target→source cell map with related contents, memoized↔memoized; every
  live source cell is in the image). Deliberately *not* called
  macro-expressibility: Felleisen's notion (macro-local) and feature-local
  both forbid store-passing. Compositionality is what excludes codes; without
  it the syntactic model would refute part 2 of the conjecture.
- Conjecture: (1) λPR is heap-adequately expressible in predicative TT —
  **proved in Agda**; (2) call-by-need STLC is not — open (proof idea: from
  heap adequacy at P extract one type D(g) for g's cell, which must occur
  negatively in the heap type). Evidence: Q_k family (sharing vs per-use
  copying, 2^k).
- Time/cost bounds were dropped from the definition in favour of heap
  adequacy ("sharing is the feature; time is the consequence").

Files
--

- `counterexample.tex/pdf` — derivations for P (λPR kinding/typing, invalid
  tree), heap diagrams, CBV version (§7), logical relation for promises (§8),
  obstruction (§9), worlds compared with L3 / full ground refs (§10),
  related work.
- `expressiveness.tex/pdf` — the expressiveness paper draft (definition,
  conjecture, theorem, design decisions, related work). Contains many
  `\todo` marginpars for the author to review claims/citations.
- `Stratified.agda` (+ `STRATIFIED.md`) — stratified shallow model for a
  fragment of call-by-need STLC.
- `Promises.agda` — mechanized LR for level-free promises (deep syntax,
  history worlds).
- `LambdaPR.agda` — λPR typing derivations (FV-restricted λ rule via
  thinning) and their shallow model into Agda: stratified worlds, semantic
  heap, region deallocation of function-local layers.
- `LambdaPRTests.agda` — refl tests of the model (result, final cell count).
- `LambdaPRAdequacy.agda` — operational semantics with flat heap, simulation
  (`fundamental`, `simulation`, `termination`, `adequacy`), space
  (`live-in-image`), and `boundary` (heap adequacy at every evaluation
  boundary).
- `ErasureProbe.agda` — feasibility probe for an erased (@0) representation
  that would make the shallow model's run time faithful. Porting is optional.
- `model.agda`, `README.md` — the original (non-terminating) attempt.
- `notes.md` — the author's own review notes.
- `check.sh` — typechecks all Agda files with a heap cap and timeout.

Practicalities
--

- Always typecheck via `./check.sh` (Agda 2.7.0.1, stdlib 2.2). Uncapped
  Agda once used 32 GB; the script uses `+RTS -M4G -RTS` and a timeout.
- Build docs with `pdflatex` (run twice).

Open items
--

- Review `\todo`s in `expressiveness.tex` (citations: Felleisen,
  Forster et al., Pippenger, Bird–Jones–de Moor, Hillerström et al.;
  source of the macro-local/feature-local terminology quoted in `notes.md`;
  strength of the heap-adequacy condition; design decisions; Q_k check).
- `notes.md` questions: motivating λPR + promises as a study of sharing;
  whether λPR is macro-expressible in TT via store-passing (it is not
  feature-local — see §6 of `expressiveness.tex`).
- Conjecture part 2 (negative result) unproved.
