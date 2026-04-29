# Roadmap — `lim_{ℓ→∞} R(k, ℓ+1) / R(k, ℓ) = 1`

Formalization of the OpenAI / GPT-5.5 short proof of Erdős's question on
off-diagonal Ramsey ratios. Source: `docs/openai-ramsey-ratio.pdf`.

**Status: COMPLETE.** All sorries closed. `lake build` passes with axioms
`[propext, Classical.choice, Quot.sound]`.

## Statement (proved)

```lean
theorem ramsey_ratio_tendsto_one (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun ℓ : ℕ => (R(k, ℓ + 1) : ℝ) / R(k, ℓ)) atTop (𝓝 1)
```

Quantitative form (also proved):

```lean
theorem ramsey_ratio_quantitative (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ), ∀ᶠ ℓ : ℕ in atTop,
      (R(k, ℓ + 1) : ℝ) / R(k, ℓ) ≤ 1 + (ℓ : ℝ) ^ (-c)
```

## Module map

| Lean module | Paper item | Status |
|---|---|---|
| `RamseyRatio/Basic.lean` | `R(k, ℓ)` definition, `R(2, ℓ) = ℓ`, critical-graph extraction | complete |
| `RamseyRatio/ErdosSzekeres.lean` | Lemma 1: `R(k, ℓ) ≤ C(k+ℓ-2, k-1)`; monotonicity | complete |
| `RamseyRatio/LowerBound.lean` | Lemma 2: probabilistic lower bound `R(k, ℓ) ≥ C · ℓ^(k/2 − 1/4)` | complete |
| `RamseyRatio/DRC.lean` | Lemma 3: dependent random choice (Fox–Sudakov) | complete |
| `RamseyRatio/MainTheorem.lean` | min-degree (eq. 1), inequality (3), Theorem 1 | complete |

## Proof sketch (as formalized)

1. **M1 — Foundations** (`Basic.lean`). `HasRamseyProperty N k ℓ` is the
   property that every graph on `Fin N` contains `K_k` or an `ℓ`-independent
   set; `R(k, ℓ) := sInf {N | HasRamseyProperty N k ℓ}`. Closed: `ramsey_one`,
   `ramsey_two : R(2, ℓ) = ℓ`, `ramsey_symm : R(k, ℓ) = R(ℓ, k)` (via
   `isNClique_compl`/`isNIndepSet_compl`), `exists_critical_graph`.

2. **M2 — Erdős–Szekeres** (`ErdosSzekeres.lean`). Strong induction on `k + ℓ`
   establishes `HasRamseyProperty (C(k+ℓ-2, k-1)) k ℓ`, hence
   `R(k, ℓ) ≤ C(k+ℓ-2, k-1)`. Public helpers `ramseyProperty_of_finset`,
   `isNIndepSet_insert`, `ramsey_mem_property`, `one_le_ramsey`,
   `ramsey_le_ramsey_succ` (monotonicity).

3. **M3 — Dependent random choice** (`DRC.lean`). Pure-counting averaging
   over `q`-tuples of vertices: `Σ_X |U(X)| = Σ_w (deg w)^q ≥ N · d^q` (via
   `Finset.inner_mul_le_norm_mul_norm`-style power-mean). Greedy deletion of
   vertices in bad `s`-subsets via `exists_subset_avoiding`.

4. **M4 — Lower bound** (`LowerBound.lean`). ~1100 lines. Builds the entire
   first-moment infrastructure: `edgeWeight` (weighted measure on edge sets),
   `weighted_clique_events`, `weighted_indep_events` (E[#K_k], E[#ℓ-IS]),
   `basic_ramsey_bound` (LP-style first-moment), `deletion_ramsey_bound`
   (LHS ≤ n/2 ⟹ n/2 < R(k, ℓ)). Concrete parameter choice
   `n = ⌊ℓ^(k/2 - 1/4)⌋`, `p = ℓ^(-(2k-1)/(2k))` yields
   `ramsey_lower_bound_power : R(k, ℓ) ≥ ℓ^(k/2 - 1/4) / 8` for all
   sufficiently large `ℓ`.

5. **M5 — Min-degree and inequality (3)** (`MainTheorem.lean`). 
   `critical_min_degree : R(k, ℓ+1) - R(k, ℓ) - 1 ≤ G.degree v` for any
   vertex `v` of a critical graph. `ramsey_ratio_drc_estimate` carries the
   paper's eq. (3) chain: applies DRC to a critical graph,
   shows `|U| ≤ R(s, ℓ+1) - 1` (the `K_s ∪ K_t = K_k` argument), bounds
   each term polynomially via Lemma 1 + Lemma 2, takes the `q`-th root, and
   converts the resulting `Δ/N ≤ ℓ^(-1/(4k²))` into the ratio bound
   `R(k, ℓ+1) / R(k, ℓ) ≤ 1 + ℓ^(-1/(8k²))`.

6. **M6 — Asymptotic close**. `ramsey_ratio_tendsto_one` derives the
   `Tendsto` statement from the quantitative bound by squeezing
   `1 ≤ ratio ≤ 1 + ℓ^(-c)` (lower from monotonicity, upper from
   `ramsey_ratio_quantitative`), with both sides tending to `1`
   (`tendsto_rpow_neg_atTop`).

## Mathlib hooks used

`SimpleGraph.IsNClique`, `IsNIndepSet`, `isNClique_compl`,
`isNIndepSet_compl`, `Nat.choose`, `Nat.sInf`, `Finset.exists_subset_card_eq`,
`SimpleGraph.comap`, `Real.rpow`, `tendsto_rpow_neg_atTop`,
`tendsto_natCast_atTop_atTop`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`,
`Mathlib.Algebra.Order.Chebyshev` (power-mean for the DRC argument),
`Real.one_sub_le_exp_neg`.

## Non-goals (achieved)

- Optimizing the constant `cₖ` — used `c = 1/(8k²)` (sufficient, not optimal).
- Sticking to simple graphs / two colours — yes.
- Reproving Lemma 2 with the Bohman–Keevash bound — proved
  `R(k, ℓ) ≥ ℓ^(k/2 - 1/4)`, weaker than paper's `(ℓ/log ℓ)^(k/2)` but
  sufficient (the `o(1)` slack absorbs the log factors).

## Signature changes (log)

- **`dependent_random_choice`** (DRC.lean, 2026-04-25): added positivity
  hypotheses `hN : 0 < N`, `hs : 0 < s`, `hm : 0 < m` to match the paper's
  "Let q, s, m be positive integers" phrasing. `hs` is correctness-critical
  (with `s = 0`, `commonNeighbors G ∅ = univ` forces `m ≤ N`, so the
  original statement was false). All downstream uses in the main proof
  trivially satisfy these (`q = k²`, `s = ⌈k/2⌉`, `m = R(t, ℓ+1)`, all
  positive for `k ≥ 3`).

- **`ramsey_lower_bound`** (LowerBound.lean, 2026-04-25): weakened from
  `∃ c > 0, ∀ᶠ ℓ, c * (ℓ / log ℓ)^(k / 2) ≤ R(k, ℓ)` (paper Lemma 2 verbatim)
  to the linear `∀ᶠ ℓ, (ℓ : ℝ) ≤ R(k, ℓ)` and kept as a standalone fallback.
  Proved via `R(2, ℓ) = ℓ` and monotonicity in the first Ramsey parameter.

- **`ramsey_lower_bound_power`** (LowerBound.lean, 2026-04-25): the
  load-bearing polynomial form actually used in M5. Statement:
  `∃ C > 0, ∀ᶠ ℓ, C * ℓ^(k/2 - 1/4) ≤ R(k, ℓ)`. Proved with `C = 1/8` via
  the deletion method (`deletion_ramsey_bound`) using
  `n = ⌊ℓ^(k/2 - 1/4)⌋`, `p = ℓ^(-(2k-1)/(2k))`. The exponent `k/2 - 1/4`
  is chosen as the smallest clean rational strictly above `⌈k/2⌉ - 1`,
  which is the binding threshold for paper eq. (3).

- **`ramsey_le_ramsey_succ`** moved from `Basic.lean` to `ErdosSzekeres.lean`
  (same namespace `RamseyRatio`) because the proof needs the Ramsey set to
  be nonempty (supplied by Erdős–Szekeres).

## Open questions (resolved)

- **Reuse vs. reinvent**: `b-mehta/exponential-ramsey` is Lean 3 — no Lake
  dependency possible. Reinvented all infrastructure in our codebase.
- **Vertex type**: settled on `Fin N` throughout, with
  `ramseyProperty_of_finset` as the transfer lemma whenever a generic
  finite vertex set arises (e.g. inside the Pascal step on `N(v)`).
