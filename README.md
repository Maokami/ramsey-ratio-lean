# ramsey-ratio-lean

[![Pages](https://img.shields.io/badge/proof%20tour-maokami.github.io%2Framsey--ratio--lean-blue)](https://maokami.github.io/ramsey-ratio-lean/)

A Lean 4 formalization of the asymptotic identity

> **Theorem** (Erdős; proved by an internal OpenAI model, 2026).
> For every fixed integer `k ≥ 2`,
> `lim_{ℓ → ∞} R(k, ℓ + 1) / R(k, ℓ) = 1`,
> where `R(k, ℓ)` is the off-diagonal Ramsey number — the smallest
> `N` for which every graph on `N` vertices contains either a `K_k`
> or an independent set of size `ℓ`.

The proof is the three-page argument from the OpenAI write-up
[`docs/openai-ramsey-ratio.pdf`](./docs/openai-ramsey-ratio.pdf): the
Erdős–Szekeres upper bound, a probabilistic lower bound via the
Erdős deletion method, and Fox–Sudakov dependent random choice are
combined on a critical graph for `R(k, ℓ + 1)`, after which the
minimum-degree estimate is closed by taking `q`-th roots with
`q = k²`.

Every step is closed in Lean 4 against `mathlib v4.28.0-rc1` with
no `sorry`. The headline theorem depends only on the standard
kernel axioms:

```
'RamseyRatio.ramsey_ratio_tendsto_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Build

The Lean toolchain (`v4.28.0-rc1`) is pinned in
[`lean-toolchain`](./lean-toolchain) and Mathlib in
[`lake-manifest.json`](./lake-manifest.json), so a fresh checkout
reproduces the development byte-for-byte:

```sh
# Optional but recommended: pull pre-built Mathlib oleans
lake exe cache get

lake build
```

The full library compiles in one to two minutes after the cache
fetch. The last line of [`RamseyRatio/MainTheorem.lean`](./RamseyRatio/MainTheorem.lean)
runs

```lean
#print axioms RamseyRatio.ramsey_ratio_tendsto_one
```

at build time, so a green build is itself a proof certificate.

## Reading

The development is organized so that the proof can be followed
either by file or by commit:

- **[Proof tour](https://maokami.github.io/ramsey-ratio-lean/)** —
  a long-form, hover-to-elaborate-the-Lean walkthrough rendered
  with [Verso](https://github.com/leanprover/verso) and deployed
  via GitHub Pages.
- **[`PROOF_OUTLINE.md`](./PROOF_OUTLINE.md)** — every paper
  section, displayed equation, and lemma mapped to its Lean
  counterpart.
- **[`ROADMAP.md`](./ROADMAP.md)** — module map, signature-change
  log, and milestone history.
- **[`docs/openai-ramsey-ratio.pdf`](./docs/openai-ramsey-ratio.pdf)** —
  the original three-page paper this development reproduces.
- **`git log --reverse --oneline`** — the formalization is split
  into nine paper-aligned commits (definition → Erdős–Szekeres →
  critical graph → linear lower bound → polynomial lower bound →
  DRC → eq. (1) → eqs. (2) and (3) and the q-th-root step →
  Theorem 1). Each commit is self-contained, compiles, and is
  `sorry`-free.

## Layout

```
RamseyRatio/
  Basic.lean           definitions, R(2, ℓ) = ℓ, critical-graph extractor
  ErdosSzekeres.lean   Lemma 1 — R(k, ℓ) ≤ C(k+ℓ-2, k-1)
  LowerBound.lean      Lemma 2 — R(k, ℓ+1) ≥ C · ℓ^(k/2 − 1/4)
  DRC.lean             Lemma 3 — Fox–Sudakov dependent random choice
  MainTheorem.lean     paper eq. (1), DRC ratio estimate, Theorem 1
Manual.lean            Verso source for the published proof tour
PROOF_OUTLINE.md       paper-to-Lean cross-reference
ROADMAP.md             milestone and signature-change log
```

Module dependency graph:

```
                Basic
              /      \
   ErdosSzekeres      DRC
        |              |
   LowerBound          |
          \            /
           MainTheorem
```

## License

The Lean source code, build configuration, and documentation in
this repository are released under the [MIT License](./LICENSE).
The bundled paper PDFs ([`docs/openai-ramsey-ratio.pdf`](./docs/openai-ramsey-ratio.pdf),
[`docs/erdos-1971.pdf`](./docs/erdos-1971.pdf)) are reproduced for
reference and are *not* covered by this license; their copyrights
remain with their original authors.

The development depends on
[mathlib4](https://github.com/leanprover-community/mathlib4) (Apache-2.0)
and [Verso](https://github.com/leanprover/verso) (Apache-2.0) via Lake.
