# Machine-checked proofs (Lean 4 + Mathlib)

This directory holds Lean 4 formalizations of results of [THEORY.md](../THEORY.md) and of the paper
([paper/](../paper/)). Each file in `SymbolicIV/` is self-contained (it imports only Mathlib), states one
result or one group of lemmas with explicit hypotheses, and proves it without `sorry`. What is
formalized, what is assumed as a hypothesis, and what was found is summarized in
[REPORT.md](REPORT.md) and in the status table below.

The probabilistic ingredients that Mathlib does not provide (matrix Bernstein, the Hsu–Kakade–Zhang
quadratic-form inequality, McDiarmid's inequality, the central limit theorem and Slutsky's lemma) are
not re-proved here. Where a result needs them, the Lean statement takes their conclusions as named
hypotheses, so that what Lean checks is the paper's own reasoning from those tools onward. Every file
ends with `#print axioms` on its main theorems; the expected output lists only `propext`,
`Classical.choice` and `Quot.sound`.

## Setup

- Install [elan](https://github.com/leanprover/elan) (the Lean version manager). The toolchain is pinned
  in `lean-toolchain` and is installed on first use.
- From this directory: `lake exe cache get` downloads the prebuilt Mathlib (about 7 GB under `.lake/`,
  which is git-ignored).
- Check one file: `lake env lean SymbolicIV/Prop21.lean` (the first run after a cache download takes
  a minute or two while Mathlib is loaded; later runs are faster). Check everything: `lake build`.

## Working in this directory (for contributors and for the agents that wrote the first version)

- One result or one coherent group of lemmas per file; `import Mathlib` only; no imports between the
  files, so that each can be checked alone. Duplicate a short definition rather than import it.
- No `sorry`, no `axiom`, no `native_decide`, no `unsafe`. If a step cannot be proved in the time
  available, state it as an explicit hypothesis of the theorem (a named `(h : ...)` argument) and say so
  in REPORT.md; a hypothesis is visible, a `sorry` is not.
- Keep the Lean statement as close to the paper's as possible. Extra hypotheses must be listed in the
  file's header comment and in REPORT.md. Weakening a conclusion to make it provable must be reported
  as such, never silently.
- Compile with `lake env lean <file>`; do not run `lake build` while others may be editing other files.
- Finding Mathlib lemmas: `grep -rn "theorem name_fragment" .lake/packages/mathlib/Mathlib`, the
  `exact?`, `apply?`, `rw?` and `simp?` tactics inside the file (their suggestions appear in the compile
  output), `#check`, and https://loogle.lean-lang.org (`https://loogle.lean-lang.org/json?q=<query>`).

## Status (first run 2026-10-15, second run 2026-10-16; details in [REPORT.md](REPORT.md))

`lake build` succeeds for all fifteen modules (Lean 4.35.0, Mathlib v4.35.0); every file is free of
`sorry`, and all 110 `#print axioms` lines (100 in the first run; U15 and the two restated Proposition 4(b) lemmas add ten) list only `propext`, `Classical.choice`, `Quot.sound`.

| Unit | File | Result | Verdict of the independent check |
|---|---|---|---|
| U01 | `Prop21.lean` | Proposition 2.1 (deterministic core) | faithful |
| U02 | `Prop24.lean` | Proposition 2.4 (perturbed weights) | faithful |
| U03 | `Thm2Assembly.lean` | Theorem 2, assembly of the five events | faithful |
| U04 | `Cor22.lean` | Corollary 2.2 algebra, tree-count arithmetic | faithful |
| U05 | `Lemma1.lean` | Lemma 1 | faithful |
| U06 | `Thm1.lean` | Theorem 1 | faithful, with the extra hypotheses κ_n ≥ 0, Q_n ≥ 0, m ≥ 1 |
| U07 | `Thm3a.lean` | Theorem 3(a) | faithful |
| U08 | `Thm3b.lean` | Theorem 3(b), Steps 1, 3, 4 and the Step 2 algebra | faithful |
| U09 | `Lemma4a.lean` | Lemma 4(a) | faithful |
| U10 | `Prop4.lean` | Proposition 4 | faithful, with the paper's (b) restated so that it is not vacuous |
| U11 | `Prop33Prop5.lean` | Proposition 3.3; Proposition 5 event logic and (c) | faithful |
| U12 | `TreeCount.lean` | Tree count | faithful |
| U13 | `Lemma3Algebra.lean` | Lemma 3 constants; Corollary 2.5 sandwich | faithful |
| U14 | `Thm1iiiSelected.lean` | Theorem 1(iii), selected-tree step | faithful |
| U15 | `Thm2Conditioning.lean` | Theorem 2, conditioning clause (added 2026-10-16) | faithful, with measurability and the a.e. form of the conditional bound as hypotheses |

What the check found in the paper, and what changed as a result, is in REPORT.md and in THEORY.md §9
(fourth pass).
