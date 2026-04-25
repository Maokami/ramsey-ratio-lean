# Proof outline — `R(k, ℓ+1) / R(k, ℓ) → 1`

This document walks through the paper's three-page proof
(`docs/openai-ramsey-ratio.pdf`) alongside the Lean 4 formalization,
so a reader who knows the paper can find the corresponding Lean theorem
in seconds, and a reader who knows the Lean code can locate the
mathematical step in the paper.

> **Theorem 1.** *For every fixed integer `k ≥ 2`,*
> `lim_{ℓ → ∞} R(k, ℓ + 1) / R(k, ℓ) = 1`.

In Lean: `RamseyRatio.ramsey_ratio_tendsto_one : ∀ (k : ℕ), 2 ≤ k →
Tendsto (fun ℓ : ℕ => (R(k, ℓ + 1) : ℝ) / R(k, ℓ)) atTop (𝓝 1)`.

The Lean proof is in `RamseyRatio/MainTheorem.lean`, line ≈ 822.

## Off-diagonal Ramsey number

> *"`R(k, ℓ)` is the smallest `N` such that every `N`-vertex graph
> contains a `K_k` or an independent set of order `ℓ`."*

```lean
def HasRamseyProperty (N k ℓ : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), (∃ s : Finset (Fin N), G.IsNClique k s) ∨
    (∃ s : Finset (Fin N), G.IsNIndepSet ℓ s)

noncomputable def ramsey (k ℓ : ℕ) : ℕ := sInf { N | HasRamseyProperty N k ℓ }
notation "R(" k ", " ℓ ")" => ramsey k ℓ
```

Both in `RamseyRatio/Basic.lean`. Triviality: `ramsey_two : R(2, ℓ) = ℓ`,
proved by checking `ℓ` satisfies the property (any edgeless graph on
`Fin ℓ` has the entire vertex set as an independent set) and no smaller
`N` does (the empty graph on `Fin N` for `N < ℓ` has no edge and only
`N < ℓ` vertices).

## The three external inputs

| Paper item | Lean name | Module |
|---|---|---|
| Lemma 1 (Erdős–Szekeres `R(k,ℓ) ≤ C(k+ℓ-2, k-1)`) | `ramsey_le_choose` | `ErdosSzekeres.lean` |
| Lemma 2 (probabilistic lower bound) | `ramsey_lower_bound_power` | `LowerBound.lean` |
| Lemma 3 (dependent random choice) | `dependent_random_choice` | `DRC.lean` |

### Lemma 1 — Erdős–Szekeres

Strong induction on `k + ℓ`, base cases `R(2, ℓ) = ℓ` (paper `R(k, ℓ)` = `R(ℓ, k)` for `R(k, 2)`).
The key recurrence `R(k, ℓ) ≤ R(k - 1, ℓ) + R(k, ℓ - 1)` is encoded as
`hasRamseyProperty_add` (private), and the binomial closure follows
`Nat.choose_succ_succ'`.

### Lemma 2 — Lower bound (Erdős deletion)

The paper states `R(k, ℓ) ≫_k (ℓ / log ℓ)^(k/2)`. Our formalization
proves the slightly weaker `R(k, ℓ) ≥ ℓ^(k/2 - 1/4) / 8` (no log factor),
which is sufficient because Theorem 1's proof uses Lemma 2 only as
`R(k, ℓ+1) - 1 ≫ ℓ^(k/2 − o(1))` and Remark 1 explicitly permits
weakened constants.

The proof (in `LowerBound.lean`, ~1100 lines) is the standard Erdős
deletion method, formalized via pure finite counting (no measure theory):

1. **§1** Define a `p`-weighted measure on edge subsets `A ⊆ Sym2 (Fin n)`,
   verify `Σ_A edgeWeight A = 1` (`sum_edgeWeight`).
2. **§2** Compute the expected number of `k`-cliques and `ℓ`-independent
   sets: `Σ_A w(A) · #K_k(A) = (n choose k) · p^C(k,2)`
   (`weighted_clique_events`, `weighted_indep_events`).
3. **§3** Averaging + greedy deletion (`deletion_ramsey_bound`): if
   `(n choose k) p^C(k,2) + (n choose ℓ) (1-p)^C(ℓ,2) ≤ n/2`,
   some edge set `A` realizes few bad cliques/IS; remove one vertex per
   bad set, surviving graph has `≥ n/2` vertices and avoids both, so
   `n/2 < R(k, ℓ)`.
4. **§4** Plug in `n = ⌊ℓ^(k/2 - 1/4)⌋`, `p = ℓ^(-(2k-1)/(2k))` and
   verify the deletion hypothesis for `ℓ` large (`ramsey_lower_bound_power`).

### Lemma 3 — Dependent random choice

```
∀ G : SimpleGraph (Fin N) of average degree d,
∀ q s m : ℕ⁺, ∃ U ⊆ V(G), every s-subset of U has ≥ m common neighbors,
                            and |U| ≥ d^q / N^(q-1) - (N choose s) ((m-1)/N)^q.
```

Lean: `dependent_random_choice` in `DRC.lean`, ~239. Proof: average
`|U(X)|` and `Bad(X)` over `q`-tuples `X`, where `U(X)` is the common
neighborhood and `Bad(X)` counts `s`-subsets of `U(X)` with too few
common neighbors.

* `Σ_X |U(X)| = Σ_w (deg w)^q ≥ N · d^q` (Jensen / power-mean,
  `sum_card_tuple_commonNeighborhood` + Mathlib's
  `Finset.inner_mul_le_norm_mul_norm`).
* `Σ_X Bad(X) ≤ (N choose s) · (m-1)^q` (`sum_bad_tuple_sets_le`).
* Some tuple `X` achieves at least the average difference; greedy
  deletion of a vertex per bad `s`-subset yields the claimed `U`
  (`exists_subset_avoiding`).

The added hypotheses `0 < N`, `0 < q`, `0 < s`, `0 < m` match the
paper's "Let q, s, m be positive integers" phrasing; `0 < s` is
correctness-critical (with `s = 0`, common neighbors of the empty set
is the universe, forcing `m ≤ N`).

## The main argument (paper §2)

The proof of Theorem 1 lives in `MainTheorem.lean`.

* **Case `k = 2`** (line ≈ 800): direct, `R(2, ℓ) = ℓ` gives ratio
  `(ℓ + 1)/ℓ = 1 + ℓ^(-1)`. Witness `c = 1`.

* **Case `k ≥ 3`** (line ≈ 190, `ramsey_ratio_drc_estimate`): set
  `s = ⌈k/2⌉`, `t = ⌊k/2⌋`, `q = k²`. Take a critical graph `G` on
  `N = R(k, ℓ + 1) - 1` vertices (`exists_critical_graph`).

  **§2 critical_min_degree**: every vertex `v` has degree
  `≥ R(k, ℓ + 1) - R(k, ℓ) - 1`, because the non-neighborhood of `v`
  cannot contain an `ℓ`-IS (else, with `v`, an `(ℓ+1)`-IS) nor a `K_k`
  (criticality), so it has `≤ R(k, ℓ) - 1` vertices.

  **§3 ramsey_ratio_drc_estimate**: apply DRC with `m = R(t, ℓ + 1)`,
  obtain `U` with each `s`-subset having `≥ R(t, ℓ + 1)` common
  neighbors and `|U|` lower-bounded by the DRC inequality.

  Show `|U| ≤ R(s, ℓ + 1) - 1`: otherwise apply Ramsey on `G[U]`,
  either get `K_s` whose common neighborhood (of size `≥ R(t, ℓ + 1)`)
  contains a `K_t` — combining with `K_s` gives a `K_k`, contradicting
  `h_no_clique` — or get `(ℓ+1)`-IS, contradicting `h_indep`. (Lean
  uses `ramseyProperty_of_finset` + the disjoint-union K_s ∪ K_t = K_k
  argument.)

  Combining the bounds yields paper's eq. (3):

  ```
  ((R(k, ℓ+1) - R(k, ℓ) - 1) / N)^q ≤
      (R(s, ℓ+1) - 1) / N + (N choose s) · (R(t, ℓ+1) - 1)^q / N^(q+1).
  ```

  Bound the RHS via Lemma 1 (`ramsey_le_choose` gives polynomial upper
  bounds on `R(s, ·)` and `R(t, ·)`) and Lemma 2 (lower bound on `N`).
  Both terms are `o(1)`; specifically `RHS ≤ const · ℓ^(-1/4)` for our
  parameter choices, so the q-th root gives
  `(R(k,ℓ+1) - R(k,ℓ) - 1)/N ≤ ℓ^(-1/(4k²))`, and the final algebra
  yields `R(k,ℓ+1)/R(k,ℓ) ≤ 1 + ℓ^(-1/(8k²))`. Witness `c = 1/(8k²)`.

* **§4 ramsey_ratio_tendsto_one**: derive the `Tendsto` form by
  squeezing `1 ≤ ratio ≤ 1 + ℓ^(-c)` and using
  `tendsto_rpow_neg_atTop`.

## Reading the code

* Modules in dependency order:
  `Basic` → `ErdosSzekeres` → `{LowerBound, DRC}` → `MainTheorem`.
* Each module begins with a `/-! # Title ... -/` block summarizing its
  contribution, followed by `/-! ### §N. ... -/` section markers.
* Public theorems carry full docstrings; private helpers are commented
  in line where the math is non-obvious.

## What's not optimized

* `cₖ`: we used `1/(8k²)`, well below paper's claimed bound. The proof
  doesn't depend on the specific value.
* The constant in Lemma 2: ours is `1/8`, paper's is unspecified.
* The exponent `k/2 - 1/4` in Lemma 2: any `α > ⌈k/2⌉ - 1` works for
  Theorem 1; we picked the smallest clean rational.
