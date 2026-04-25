# ramsey-ratio-lean

Lean 4 formalization of

> **Theorem (Erdős, proved by an internal OpenAI model, 2026).**
> For every fixed integer `k ≥ 2`,
> `lim_{ℓ → ∞} R(k, ℓ + 1) / R(k, ℓ) = 1`,
> where `R(k, ℓ)` is the off-diagonal Ramsey number.

Source paper: `docs/openai-ramsey-ratio.pdf`. Proof outline (paper steps
mapped to Lean theorems): [`PROOF_OUTLINE.md`](./PROOF_OUTLINE.md).
Module map and signature-change log: [`ROADMAP.md`](./ROADMAP.md).

## Build

```sh
lake update    # first time only
lake build
```

Toolchain: `leanprover/lean4:v4.28.0-rc1`, mathlib `v4.28.0-rc1`.

## Status

**Complete.** All milestones M1–M6 closed; `lake build` passes with axioms
`[propext, Classical.choice, Quot.sound]` only — no `sorry`, no custom
axioms. The main theorem is `RamseyRatio.ramsey_ratio_tendsto_one`; the
quantitative form is `RamseyRatio.ramsey_ratio_quantitative`. See
[`ROADMAP.md`](./ROADMAP.md) for the proof sketch and module map.

Quick check:

```sh
lake env lean -- -e "import RamseyRatio; #print axioms RamseyRatio.ramsey_ratio_tendsto_one"
# 'RamseyRatio.ramsey_ratio_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```
