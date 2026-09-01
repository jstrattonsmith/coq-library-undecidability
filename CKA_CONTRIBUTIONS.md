# About this branch (`enable-L-nix-9.0`)

This branch (on `jstrattonsmith/coq-library-undecidability`, a fork of
`uds-psl/coq-library-undecidability`) bundles two genuinely separate
contributions, both built on top of an otherwise-unmodified `rocq-9.0`:

1. **A Nix build-wiring fix** (the branch's original purpose, commit
   `71c9f210`): `theories/_CoqProject` comments out most of `theories/L/`
   (including `Functions/{Encoding,Eval}.v`), which is needed by
   `coq-synthetic-computability`'s `Models/CT.v`. This turned out to be a
   build-wiring gap, not a real Rocq-9 incompatibility -- all 69 `L/` files
   compile cleanly under Rocq 9.0.1 once the right MetaRocq sub-packages
   and the `equations` OCaml plugin are on the loadpath (see the added
   `flake.nix`). This part is a candidate to eventually propose upstream as
   its own PR.

2. **New MM2 (two-counter machine) content** (added 2026-08-31, commits
   `61894f09` onward), migrated from a separate downstream project
   (`commutative-kleene-algebra`, a sibling repo under the same parent
   directory), where it had been custom-built but turned out to be
   genuinely reusable, general-purpose MM2 machinery with zero content
   specific to that project:
   - `theories/MinskyMachines/Util/MM2_stepper.v`: a computable, total
     step function for MM2, proved equivalent to the existing relational
     `mm2_atom`/`mm2_step` in `Util/MM2_facts.v` (which has a rich
     relational theory of stepping but no computable step function -- the
     gap this fills).
   - `theories/MinskyMachines/Util/MM2_embed_nat.v`: a small,
     self-contained Cantor-pairing bijection `nat * nat <-> nat` (no
     general-purpose one existed elsewhere in this library).
   - `theories/MinskyMachines/Util/MM2_simulator.v`: Gödel-coding of MM2
     programs as naturals (`progOf`/`codeOf`), a total step-indexed
     evaluator built on `MM2_stepper.v`, and MetaRocq-driven
     L-extractability instances for all of it.
   - `theories/MinskyMachines/Reductions/FRACTRAN_computable_to_MM2_computable.v`:
     compiles a FRACTRAN-computable relation to `MM2_computable` via
     `MMA2_computable`, using a divisibility-encoded output convention.
   - `theories/MinskyMachines/Reductions/MM2_Splice.v`: a pinned-stop-
     position variant of the FRACTRAN-to-MMA2 compilation (needed so code
     can be reliably appended right after a compiled program), plus a
     concrete program-splicing construction (`Psplice`) built on it.

   This second part is a separate, independent candidate for an eventual
   upstream PR from the Nix fix above -- they touch unrelated parts of the
   library and don't depend on each other.

Neither has been proposed upstream yet; this branch exists to keep both
verified and available. See each file's own header comment for full
technical detail, and `commutative-kleene-algebra`'s
`RESTRUCTURE_SCRATCHPAD.md` (in the shared parent directory) for the
complete migration history.
