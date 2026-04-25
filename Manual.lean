/-
Verso documentation for ramsey-ratio-lean.

Build with:
  lake build manual
The HTML output is written under `_out/html-multi/`.
-/

import VersoManual

import RamseyRatio

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open RamseyRatio

set_option pp.rawOnError true

#doc (Manual) "Erdős's Ramsey-ratio theorem in Lean 4" =>
%%%
authors := ["ramsey-ratio-lean"]
shortTitle := "ramsey-ratio-lean"
%%%

This document accompanies the Lean 4 formalization of the OpenAI / GPT-5.5
short proof of Erdős's question:

{lean}`@RamseyRatio.ramsey_ratio_tendsto_one`

For every fixed `k ≥ 2`, the off-diagonal Ramsey ratio
`R(k, ℓ + 1) / R(k, ℓ)` tends to 1 as `ℓ → ∞`.

# The setting

`R(k, ℓ)` is the off-diagonal Ramsey number: the smallest `N` such that
every graph on `N` vertices contains either a `K_k` clique or an
independent set of size `ℓ`. The base case `R(2, ℓ) = ℓ` is captured by

{lean}`@RamseyRatio.ramsey_two`

# The three external inputs

The proof relies on three classical ingredients.

## Lemma 1 — Erdős–Szekeres upper bound

{lean}`@RamseyRatio.ramsey_le_choose`

Proof: strong induction on `k + ℓ` via the Pascal recurrence
`R(k, ℓ) ≤ R(k - 1, ℓ) + R(k, ℓ - 1)`.

## Lemma 2 — Polynomial lower bound

{lean}`@RamseyRatio.ramsey_lower_bound_power`

Proof: Erdős's deletion method on a `p`-weighted random edge set,
`p = ℓ^(-(2k-1)/(2k))`, `n ≈ ℓ^(k/2 - 1/4)`. Pure finite counting,
no measure theory.

## Lemma 3 — Dependent random choice

{lean}`@RamseyRatio.dependent_random_choice`

Proof: average over `q`-tuples of vertices, lower-bound the expected
common-neighborhood size via Jensen, count bad `s`-subsets, greedy
deletion.

# The main argument

The min-degree bound (paper eq. (1)):

{lean}`@RamseyRatio.critical_min_degree`

Combined with DRC, ES, and the polynomial lower bound, this yields the
quantitative estimate (paper Remark 1):

{lean}`@RamseyRatio.ramsey_ratio_quantitative`

with `c = 1 / (8 k²)`. Squeezing then gives the limit:

{lean}`@RamseyRatio.ramsey_ratio_tendsto_one`

# Source files

Modules in dependency order:
* `RamseyRatio/Basic.lean` — definition of `R(k, ℓ)`, base cases, symmetry.
* `RamseyRatio/ErdosSzekeres.lean` — Lemma 1 and monotonicity.
* `RamseyRatio/LowerBound.lean` — Lemma 2 (~1100 lines, 4 sections).
* `RamseyRatio/DRC.lean` — Lemma 3.
* `RamseyRatio/MainTheorem.lean` — the theorem.
