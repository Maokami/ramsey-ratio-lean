# ramsey-ratio-lean

[![Pages](https://img.shields.io/badge/proof%20tour-maokami.github.io%2Framsey--ratio--lean-blue)](https://maokami.github.io/ramsey-ratio-lean/)

Lean 4 formalization of

> **Theorem (Erdős, proved by an internal OpenAI model, 2026).**
> For every fixed integer `k ≥ 2`,
> `lim_{ℓ → ∞} R(k, ℓ + 1) / R(k, ℓ) = 1`,
> where `R(k, ℓ)` is the off-diagonal Ramsey number.

The Lean development closes every step against `mathlib v4.28.0-rc1`,
with no `sorry` and the standard kernel axioms only.

```
'RamseyRatio.ramsey_ratio_tendsto_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Reading

* **Proof tour** — a long-form, hover-to-elaborate-the-Lean walkthrough
  is published at <https://maokami.github.io/ramsey-ratio-lean/>.
* **`PROOF_OUTLINE.md`** — paper sections mapped to Lean theorem names.
* **`ROADMAP.md`** — module map and signature-change log.
* **`docs/openai-ramsey-ratio.pdf`** — the original 3-page proof.

## Build

```
lake update
lake build
```

Toolchain: `leanprover/lean4:v4.28.0-rc1`. The first build pulls
Mathlib's pre-built oleans from the public cache (`lake exe cache get`
is invoked automatically by the GitHub Pages workflow; locally it's
optional but speeds things up).

## License

MIT — see [`LICENSE`](./LICENSE). The included
`docs/openai-ramsey-ratio.pdf` belongs to its original authors and is *not*
covered by this license.

## Layout

```
RamseyRatio/
  Basic.lean           definitions, R(2, ℓ) = ℓ, critical-graph extraction
  ErdosSzekeres.lean   Lemma 1 (R(k, ℓ) ≤ C(k+ℓ-2, k-1))
  LowerBound.lean      Lemma 2 (R(k, ℓ) ≥ C · ℓ^(k/2 - 1/4))
  DRC.lean             Lemma 3 (Fox–Sudakov dependent random choice)
  MainTheorem.lean     critical_min_degree → quantitative → Tendsto
Manual.lean            Verso source for the proof tour
PROOF_OUTLINE.md       paper-to-Lean cross-reference
ROADMAP.md             milestone log + signature-change log
```

The dependency graph is

```
                Basic
              /      \
   ErdosSzekeres      DRC
        |              |
   LowerBound          |
          \            /
           MainTheorem
```
