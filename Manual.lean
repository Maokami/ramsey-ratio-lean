/-
Verso documentation for ramsey-ratio-lean.

Build with:
  lake build manual && .lake/build/bin/manual
The HTML output is written under `_out/html-single/`.
-/

import VersoManual

import RamseyRatio

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open RamseyRatio

set_option pp.rawOnError true

#doc (Manual) "Reproducing OpenAI's Erdős proof in Lean 4" =>
%%%
authors := ["ramsey-ratio-lean"]
shortTitle := "Ramsey ratio in Lean"
%%%

# A puzzle about parties

Six people walk into a room. They either know each other or they don't —
no half-acquaintances, no edge cases. Then no matter how the social graph
turns out, one of two things happens: either three of the six are
pairwise acquainted (a clique) or three of them are pairwise strangers
(an *anti*-clique). With five people, the puzzle has counter-examples;
with six, it doesn't.

That's the 1947 *party problem*, and the smallest number that forces
the dichotomy is called a Ramsey number. In notation:
{lean}`@RamseyRatio.ramsey` `R(3, 3) = 6`. The story generalizes: for
any `k` and `ℓ`, `R(k, ℓ)` is the smallest `N` such that every graph on
`N` vertices contains either a `k`-clique or an `ℓ`-vertex independent
set. Whatever the graph — friend network, web of citations, the dating
preferences of mathematicians — once the population hits `R(k, ℓ)`, you
*cannot* avoid both structures simultaneously.

The catch: actually computing `R(k, ℓ)` is, in nearly all cases,
*impossibly hard*. We do not know `R(5, 5)`. We will likely never know
`R(10, 10)`. Our best estimates are exponential gaps between lower and
upper bounds. Erdős famously joked that if aliens demanded the value of
`R(5, 5)` or they would destroy Earth, we should mobilize all our
computers and mathematicians and try to compute it; if they demanded
`R(6, 6)`, we should try to destroy the aliens first.

# A 60-year-old question about ratios

So instead of computing Ramsey numbers exactly, we study *how they
grow*. Erdős asked, in 1971: how does the ratio of consecutive
off-diagonal Ramsey numbers behave? That is, fix `k`, and look at

```
              R(k, ℓ + 1)
              -----------     as ℓ → ∞.
                R(k, ℓ)
```

A naïve guess is "no idea — the function `R(k, ·)` could oscillate
wildly." Erdős conjectured the answer is *just `1`* — the ratio
tends to one, no matter how complicated the underlying numbers are.

This question sat open for over half a century. The classical bounds
say `R(k, ℓ) ≪ ℓ^(k-1)` (Erdős–Szekeres 1935) and
`R(k, ℓ) ≫ (ℓ / log ℓ)^(k/2)` (Erdős 1961). Both polynomial; the
exponents differ. There's a wide gap between the bounds, and the
conjecture asks for a ratio bound that holds *despite* the gap.

# 2026: a 3-page proof from OpenAI — and no artifact

In April 2026, an internal model at OpenAI produced a proof. The
write-up is three pages long and lives in
[`docs/openai-ramsey-ratio.pdf`](https://github.com/) of this
repository. It uses three classical inputs (Erdős–Szekeres, the
probabilistic lower bound, and Fox–Sudakov's *dependent random choice*)
and a clever observation: if the ratio failed to tend to 1, a
"critical" graph for `R(k, ℓ + 1)` would have very high minimum degree —
which is at odds with the sparseness one expects of optimal
Ramsey-extremal graphs. Dependent random choice exploits the tension.

But — and this is why this repository exists — *the proof artifact was
not released*. We have the paper. We do not have a Lean file, a Coq
script, or any other independently verifiable rendering of the
argument. For a result of this importance, that's an unusually
fragile state of affairs.

So this project is a reproduction. We took the three-page proof and,
over the course of one extended pair-programming session with Anthropic's
Claude and OpenAI's Codex CLI, encoded it in Lean 4 against
`mathlib v4.28.0-rc1`. The final declaration is

{lean}`@RamseyRatio.ramsey_ratio_tendsto_one`

— machine-checked, depending only on Lean's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`). Zero `sorry`. Zero custom
axioms. The whole repository is on GitHub; this document is the
narrative companion.

## What this post covers

The rest of this page walks through the proof at three altitudes:

1. *Bird's-eye* — the shape of the argument, and why it is
   surprisingly hard to formalize despite being only three pages.
2. *Building blocks* — the three classical lemmas, with the Lean
   statements and a few key tactics.
3. *The main combine* — how the lemmas fit together to force the
   ratio to 1, and the asymptotic algebra at the end.

You don't need to know any Lean to follow the prose. If you do, every
named theorem in the post is a clickable hyperlink to the actual
declaration. Hover over the inline references to see Lean's full
statement and type, courtesy of Verso.

# Background: Ramsey numbers, formalized

We model finite simple graphs on the type `Fin N` (`{0, 1, ..., N-1}`).
A graph `G : SimpleGraph (Fin N)` is a relation on vertices. A
`k`-clique is a `Finset` of vertices of cardinality `k` whose pairwise
adjacencies are all "yes"; a `ℓ`-independent set is the dual. Mathlib
encodes these as {lean}`SimpleGraph.IsNClique` and
{lean}`SimpleGraph.IsNIndepSet`.

The off-diagonal Ramsey property and number are then a one-liner:

```
def HasRamseyProperty (N k ℓ : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique k s) ∨
    (∃ s : Finset (Fin N), G.IsNIndepSet ℓ s)

noncomputable def ramsey (k ℓ : ℕ) : ℕ :=
  sInf { N | HasRamseyProperty N k ℓ }

notation "R(" k ", " ℓ ")" => ramsey k ℓ
```

Two early sanity checks: {lean}`@RamseyRatio.ramsey_one` proves
`R(1, ℓ) = 1` (any single vertex is a 1-clique), and
{lean}`@RamseyRatio.ramsey_two` proves `R(2, ℓ) = ℓ` (the empty graph
on `ℓ` vertices is the only obstruction). The `R(2, ·)` case is doubly
useful: it gives us the trivial limit `(ℓ + 1) / ℓ → 1` for the
`k = 2` branch of the main theorem, and it furnishes the simplest
non-trivial lower bound `R(k, ℓ) ≥ ℓ` for all `k ≥ 2` (via the obvious
monotonicity in the first index, encoded as
{lean}`@RamseyRatio.ramsey_lower_bound`).

Verso elaborates Lean code blocks against the imported project, so the
following snippet is *checked* every time this page is built. If we
ever break `ramsey_two`'s signature, the page fails to build:

```lean
-- Concrete instance: R(2, 5) = 5.
example : R(2, 5) = 5 :=
  RamseyRatio.ramsey_two 5 (by norm_num)
```

There is one wrinkle worth pointing out. `Nat.sInf` returns `0` on the
empty set, so a-priori `R(k, ℓ)` could be `0` if the underlying set
has no elements. To exclude this — and to use `R(k, ℓ)` in any proof
that takes its definition seriously — we need to know the set is
non-empty, i.e., that some `N` exists with the Ramsey property. The
classical Erdős–Szekeres bound supplies one: for any `k, ℓ ≥ 1`,
`Nat.choose (k + ℓ - 2) (k - 1)` is in the set. We re-discover this
chicken-and-egg flavour several times below.

# The shape of the proof

Theorem 1 of the paper has two cases.

*Case `k = 2`.* From {lean}`@RamseyRatio.ramsey_two`, the ratio is
`(ℓ + 1) / ℓ = 1 + 1/ℓ`. Tends to 1 immediately. In Lean, the witness
constant is `c = 1` and the bound is exact (not just eventually):

```
(R(2, ℓ + 1) : ℝ) / R(2, ℓ) = 1 + (ℓ : ℝ) ^ (-(1 : ℝ))
```

*Case `k ≥ 3`.* This is the interesting one. Set
`s := ⌈k/2⌉`, `t := ⌊k/2⌋`, `q := k²`. Take a graph `G` that witnesses
the value `R(k, ℓ + 1) - 1`: a graph on `R(k, ℓ + 1) - 1` vertices
with no `K_k` and no `(ℓ + 1)`-independent set. Such a graph exists
by definition of `sInf`, and we extract it as
{lean}`@RamseyRatio.exists_critical_graph`.

The paper's argument has four moves:

1. *(Min-degree.)* Every vertex of `G` has degree at least
   `R(k, ℓ + 1) - R(k, ℓ) - 1`. If the ratio doesn't tend to 1, this
   forces `G` to be dense. Lean: {lean}`@RamseyRatio.critical_min_degree`.

2. *(Apply DRC.)* Feed `G`'s average degree into Fox–Sudakov's
   dependent-random-choice lemma with parameters `(q, s, m := R(t, ℓ + 1))`.
   It produces a vertex set `U ⊆ V(G)` with two key features: every
   `s`-subset of `U` has at least `R(t, ℓ + 1)` common neighbours, and
   `|U|` is bounded below by an explicit DRC inequality.
   Lean: {lean}`@RamseyRatio.dependent_random_choice`.

3. *(Squeeze `U` from above.)* On the *other* hand, `|U|` cannot exceed
   `R(s, ℓ + 1) - 1`. If it did, `G[U]` would have either a
   `(ℓ + 1)`-IS (impossible, since `G` has none) or a `K_s` —
   whose `R(t, ℓ + 1)` common neighbours then contain a `K_t`,
   completing a `K_k` (also impossible). The lemma
   {lean}`@RamseyRatio.ramseyProperty_of_finset` does the heavy
   lifting on `G[U]`.

4. *(Combine and take the q-th root.)* The two `|U|` bounds collide
   into the paper's equation (3):

   ```
   ((R(k, ℓ+1) - R(k, ℓ) - 1) / N)^q
        ≤  (R(s, ℓ+1) - 1) / N
        +  (N choose s) · ((R(t, ℓ+1) - 1) / N)^q.
   ```

   The right-hand side is `o(1)` — for instance, the first term is at
   most `ℓ^(s-1) / N`, and `N` itself is `≫ ℓ^(k/2 - o(1))` by the
   probabilistic lower bound. After taking the `q`-th root, the
   `R(k, ℓ+1) / R(k, ℓ)` ratio drops to `1 + ℓ^(-c)` for some `c > 0`.

Combining all of this is the contents of
{lean}`@RamseyRatio.ramsey_ratio_quantitative` (Lean), and squeezing
to the actual `Tendsto` statement is one short top-up
{lean}`@RamseyRatio.ramsey_ratio_tendsto_one`.

# Why three pages take 2 700 lines

A reader who has seen Lean before may now want to ask: *why does a
three-page proof balloon by three orders of magnitude?* Three reasons:

*(1) Common neighbourhoods are sneaky.* `commonNeighbors G T` is
defined naturally as a `Set V`, but to take its cardinality one wants
either `Set.ncard` or its `Finset` shadow, depending on the lemma.
We carry both, with a short bridge lemma:

```
private lemma commonNeighbors_ncard (G : SimpleGraph V) (s : Finset V) :
    (commonNeighbors G s).ncard = (commonNeighborFinset G s).card
```

*(2) The probabilistic argument has no probability theory.* Erdős's
deletion method conventionally lives in `MeasureTheory`. We sidestep
that by working with weighted sums over the *finite* set of edge
subsets: we define {lean}`@RamseyRatio.commonNeighbors` and then a
weighted measure

```
private def edgeWeight (E A : Finset α) (p : ℝ) : ℝ :=
  p ^ A.card * (1 - p) ^ (E.card - A.card)
```

with `Σ_{A ⊆ E} edgeWeight E A p = 1` (a finitary version of "this is
a probability distribution"), then proceed with Markov / averaging
arguments at the level of finite sums. About 1 100 lines of `LowerBound.lean`
are this scaffolding.

*(3) Asymptotic algebra is fiddly.* The final stretch — going from
"each summand is `o(1)`" to "and therefore the ratio is at most
`1 + ℓ^(-c)`" — is where most of `MainTheorem.lean` lives. It is the
combinatorial-asymptotic equivalent of "a few lines of routine
algebra in the paper." We wrote about 600 lines of
`calc … _ ≤ … by gcongr` chains.

These three observations cover the bulk of the size gap. The
argument's *structure* is faithful to the paper, modulo a couple of
deliberate signature changes documented in `ROADMAP.md`.

# Lemma 1 — Erdős–Szekeres `R(k, ℓ) ≤ C(k+ℓ-2, k-1)`

The classical proof is by induction on `k + ℓ`. Take a graph on
`R(k - 1, ℓ) + R(k, ℓ - 1)` vertices, fix a vertex `v`, partition the
rest by adjacency to `v`: either `|N(v)| ≥ R(k - 1, ℓ)` (and we
recurse) or `|V \ N[v]| ≥ R(k, ℓ - 1)` (and we recurse the other way),
by pigeonhole. Add `v` back to whichever side gave a clique or
independent set.

In Lean we phrase this not as a recurrence on `R(k, ℓ)` but on the
property itself:

```
private lemma hasRamseyProperty_add (a b k ℓ : ℕ)
    (ha : HasRamseyProperty a (k - 1) ℓ)
    (hb : HasRamseyProperty b k (ℓ - 1)) :
    HasRamseyProperty (a + b) k ℓ
```

This is cleaner because it never asks "is the underlying `sInf` set
non-empty?" — the hypotheses already supply concrete witnesses.

For example, this concrete bound elaborates against our development:

```lean
-- R(3, 5) ≤ Nat.choose 6 2 = 15.
example : R(3, 5) ≤ Nat.choose (3 + 5 - 2) (3 - 1) :=
  RamseyRatio.ramsey_le_choose 3 5
    (by norm_num) (by norm_num)
```

The closure into the binomial bound,
{lean}`@RamseyRatio.ramsey_le_choose`, is `Nat.choose_succ_succ'`
(Pascal's rule for `Nat.choose`) applied to a strong induction on
`k + ℓ`. As a side benefit, the induction also gives us a *concrete*
witness in the Ramsey set, so we can finally show non-emptiness:
{lean}`@RamseyRatio.ramseySet_nonempty`. Now `Nat.sInf_mem` gives
{lean}`@RamseyRatio.ramsey_mem_property`, which says
`HasRamseyProperty R(k, ℓ) k ℓ` — the foundational tool we leaned on
all over the rest of the project.

(Why was monotonicity in the second argument tricky? We wanted to
write `ramsey_le_ramsey_succ : R(k, ℓ) ≤ R(k, ℓ + 1)` in `Basic.lean`,
but `Nat.sInf` of an empty set is `0`, so without a non-emptiness
witness the inequality can fail formally even when it holds
mathematically. So `ramsey_le_ramsey_succ` lives in `ErdosSzekeres.lean`,
*after* we have the witness.)

# Lemma 2 — the probabilistic lower bound

We need to know that `R(k, ℓ)` is "polynomially big" in `ℓ`.
Specifically, the paper invokes
`R(k, ℓ) ≫ (ℓ / log ℓ)^(k / 2)`, but its proof of Theorem 1 only
uses the consequence `R(k, ℓ + 1) - 1 ≫ ℓ^(k/2 − o(1))` — and Remark 1
of the paper *explicitly* permits weakened constants ("we do not
attempt to optimize cₖ"). So we proved a slightly weaker but cleaner
statement and saved a few hundred lines of log-Stirling arithmetic:

{lean}`@RamseyRatio.ramsey_lower_bound_power`

```
∃ C > (0 : ℝ), ∀ᶠ ℓ : ℕ in atTop,
    C * (ℓ : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) ≤ (R(k, ℓ) : ℝ)
```

The exponent `k/2 − 1/4` is the smallest clean rational *strictly
above* `⌈k/2⌉ - 1`, which turns out to be the binding threshold in
the main argument's eq. (3).

The proof is the standard *deletion method* on a `p`-weighted random
graph, refactored to avoid `MeasureTheory`. Four sections in
`LowerBound.lean`:

* *§1.* Define the "edge universe" `edgeUniverse n :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset` and the `p`-weighted measure
  `edgeWeight`. Prove `Σ_A edgeWeight E A p = 1`.
* *§2.* Compute weighted clique and independent-set counts:

  ```
  private lemma weighted_clique_events (n k : ℕ) (p : ℝ) :
      (∑ A ∈ (edgeUniverse n).powerset,
          edgeWeight (edgeUniverse n) A p *
          (((Finset.univ : Finset (Fin n)).powersetCard k).filter
              (fun s => edgesOn s ⊆ A)).card)
        = (Nat.choose n k : ℝ) * p ^ Nat.choose k 2
  ```

  i.e., the expected number of `k`-cliques is `C(n, k) · p^C(k,2)`.
  Same shape for independent sets, with `p` replaced by `1 - p`.
* *§3.* Two averaging lemmas:

  - `basic_ramsey_bound` (private): if
    `C(n, k) p^C(k,2) + C(n, ℓ) (1-p)^C(ℓ,2) < 1`, then the
    expected number of bad events is below 1, so some realization is
    *clean* (no clique, no IS), and `n < R(k, ℓ)`.
  - `deletion_ramsey_bound` (private): if the same
    sum is `≤ n / 2`, average + greedy-deletion still leave a graph on
    at least `n / 2` vertices that is clean — so `n / 2 < R(k, ℓ)`. The
    deletion variant gives a stronger polynomial degree.
* *§4.* Plug in `n := ⌊ℓ ^ (k / 2 - 1/4)⌋` and
  `p := ℓ ^ (-(2k - 1) / (2k))` and show the deletion hypothesis holds
  for `ℓ` large.

The reason we got away without `MeasureTheory.Probability` is that
all *finite* probabilistic arguments are equivalent to weighted
finite sums; the weights here are
`p^|A| * (1 - p)^(|edgeUniverse| - |A|)`. Mathlib makes this
shockingly painless once you set up the edge-weight identity, because
all the algebra is just `Finset.sum_comm`, `pow_add`, and friends.

# Lemma 3 — dependent random choice

This is Fox–Sudakov, formalized in {lean}`@RamseyRatio.dependent_random_choice`:

```
∃ U : Finset (Fin N),
    (∀ T : Finset (Fin N), T ⊆ U → T.card = s →
        m ≤ (commonNeighbors G T).ncard) ∧
    (d ^ q / (N : ℝ) ^ (q - 1) -
        (Nat.choose N s : ℝ) * ((m - 1 : ℝ) / N) ^ q ≤ (U.card : ℝ))
```

The setup: pick a random `q`-tuple of vertices uniformly, define
`U(X) := ⋂_i N(X_i)` (the common neighbourhood of the tuple). On
average, `|U(X)|` is large by Jensen / power-mean — that gives the
first term of the lower bound. To control "bad" `s`-subsets of `U(X)`
(those with too few common neighbours), count them: any bad `A`
appears in `U(X)` iff `X ⊆ N(A)`, contributing at most
`|N(A)|^q ≤ (m-1)^q` tuples; summed over all `s`-subsets, that is
the second term. Subtracting, some realization of `X` achieves the
average difference, then a greedy deletion removes one vertex per
bad subset.

Two technical notes on the Lean version:

* We added positivity hypotheses `0 < N`, `0 < q`, `0 < s`, `0 < m`
  to match the paper's "let `q, s, m` be positive integers." The
  `0 < s` constraint is *necessary*: if `s = 0`, then `commonNeighbors G ∅`
  is the universe (vacuous quantifier), and the first conjunct would
  force `m ≤ N`, which can fail. ROADMAP records this as a deliberate
  signature refinement.
* The greedy-deletion step is general enough to extract:

  ```
  private lemma exists_subset_avoiding (A : Finset α) (bad : Finset (Finset α))
      (hbad_sub : ∀ T ∈ bad, T ⊆ A) (hbad_nonempty : ∀ T ∈ bad, T.Nonempty) :
      ∃ U ⊆ A, (∀ T ∈ bad, ¬ T ⊆ U) ∧ A.card - bad.card ≤ U.card
  ```

  We use `Classical.choose` to pick a sacrificial vertex per bad set
  and remove the union. No surprises.

# Putting it together

Once Lemmas 1–3 are in hand, the main argument unfolds as four
calc blocks in {lean}`@RamseyRatio.ramsey_ratio_drc_estimate`. Let's
look at each piece.

*Min-degree.* {lean}`@RamseyRatio.critical_min_degree` is a clean
combinatorial argument — the only Lean subtlety is that `Fin
(R(k, ℓ + 1) - 1)` is the carrier type, so `R(k, ℓ + 1) - 1` had
better be positive (otherwise the type is empty and there's nothing
to prove). Helpfully, `R(k, ℓ + 1) ≥ 2` for `k ≥ 2, ℓ ≥ 1`, so we
have it.

*`|U| ≤ R(s, ℓ + 1) - 1`.* We assume for contradiction that
`R(s, ℓ + 1) ≤ |U|`, take a sub-finset `U' ⊆ U` of cardinality
`R(s, ℓ + 1)`, and apply
{lean}`@RamseyRatio.ramseyProperty_of_finset` to `G[U']` with
`s, ℓ + 1`. There are two branches:

* `K_s` in `G[U']`: by DRC's first conjunct, the common neighbourhood
  of this `K_s` has at least `R(t, ℓ + 1)` vertices. Apply
  `ramseyProperty_of_finset` *again* with parameters `t, ℓ + 1`. If we
  find a `K_t`, then together with the `K_s` we have a `K_(s + t) =
  K_k` in `G` — contradicting `h_no_clique`. If we find a
  `(ℓ + 1)`-IS, contradiction with `h_indep`.
* `(ℓ + 1)`-IS in `G[U']`: contradicts `h_indep` directly.

The construction of the `K_k` from the `K_s` and the common-neighborhood
`K_t` requires an `IsNClique.insert`-style splice. We push all of it
through a private helper.

*Eq. (3) and the q-th root.* With `|U| ≤ R(s, ℓ + 1) - 1` in hand,
DRC's second conjunct rearranges into

```
((R(k, ℓ+1) - R(k, ℓ) - 1) / N) ^ q
   ≤  (R(s, ℓ + 1) - 1) / N
   +  (N choose s) · ((R(t, ℓ + 1) - 1) / N) ^ q
```

We then bound each summand using Erdős–Szekeres (upper bounds on
`R(s, ℓ + 1)` and `R(t, ℓ + 1)` are polynomial in `ℓ`) and our
polynomial lower bound on `N` (which is essentially `R(k, ℓ + 1) - 1`).
The exponent gymnastics turns out to give

```
RHS  ≤  C · ℓ ^ (-1/4)
```

uniformly in `k ≥ 3`. Taking the `q`-th root:

```
(R(k, ℓ+1) - R(k, ℓ) - 1) / N  ≤  C^(1/q) · ℓ ^ (-1/(4 q))
```

and `q = k²`, so the exponent is `1 / (4 k²)`. Multiplying by `N`,
adding `R(k, ℓ)` and dividing through, we get

```
R(k, ℓ + 1) / R(k, ℓ)  ≤  1  +  ℓ ^ (-1/(8 k²))
```

for `ℓ` large. We actually pick `c := 1 / (8 k²)` to give ourselves a
safety margin.

# The squeeze: from quantitative to `Tendsto`

`ramsey_ratio_quantitative` gives an explicit bound, but the headline
statement is an `atTop` filter limit. We close the gap with the
sandwich theorem
({lean}`@RamseyRatio.ramsey_ratio_tendsto_one` again):

* *Lower bound.* `R(k, ℓ + 1) ≥ R(k, ℓ)` by monotonicity, so
  `R(k, ℓ + 1) / R(k, ℓ) ≥ 1`.
* *Upper bound.* From the quantitative result,
  `R(k, ℓ + 1) / R(k, ℓ) ≤ 1 + ℓ^(-c)` eventually.
* Both bounds tend to `1` (the upper one via
  `tendsto_rpow_neg_atTop`).
* By Mathlib's
  `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, the ratio tends to
  `1`.

That's the entire proof of Theorem 1, formalized.

# What I learned

*Working with Codex.* The hardest stretches — Erdős–Szekeres'
bookkeeping induction, the 1 100-line `LowerBound.lean`, the eq. (3)
asymptotic algebra — were drafted by Codex (OpenAI's CLI agent) under
my orchestration. Pattern that worked: I'd describe the goal, the
relevant Mathlib API (sometimes the wrong one, which Codex would
correct), and an explicit parameter choice. Codex would produce a
~80% correct draft; I'd compile it, point at errors, and Codex would
patch. About four delegation rounds total.

Patterns that didn't work as well: asking Codex to "write the proof"
without anchoring to a specific Mathlib lemma name. The model will
happily produce a plausible-looking proof using a non-existent lemma.
Always check `lake build` after every patch.

*Paper deviations as a feature.* We deviated from the paper twice:
weakening Lemma 2 (no log factor; smaller exponent), and adding
positivity hypotheses to dependent random choice. Both deviations
are recorded in `ROADMAP.md` under "Signature changes." Both, in
hindsight, made the formalization *cleaner* than a literal
transcription would have been. The paper's `(ℓ / log ℓ)^(k/2)` form
adds 200+ lines of `Real.log` arithmetic for no gain in the main
argument, and the paper's "Let `q, s, m` be positive integers" was
already there — our literal transcription missed it.

*The chicken-and-egg of `Nat.sInf`.* Several proofs needed
`HasRamseyProperty R(k, ℓ) k ℓ`, which needs the Ramsey set to be
non-empty, which needs Erdős–Szekeres. We learned to thread through
{lean}`@RamseyRatio.ramsey_mem_property` and to defer monotonicity
into `ErdosSzekeres.lean`. A small architectural lesson: when your
definition involves `sInf`, expose a "non-emptiness witness" lemma
*early* in the file hierarchy, even if proving it requires a
forward-reference comment.

# Capstone: the headline statement, type-checked here

The following block is elaborated by Verso during the build of this
page. It restates Theorem 1 verbatim against our development:

```lean
open Filter Topology in
example (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun ℓ : ℕ => (R(k, ℓ + 1) : ℝ) / R(k, ℓ))
      atTop (𝓝 1) :=
  RamseyRatio.ramsey_ratio_tendsto_one k hk
```

If Lean ever rejects this elaboration, the page fails to build.
That is the whole point: documentation that cannot drift from the
underlying proof.

# Reproduce it

```
git clone https://github.com/<you>/ramsey-ratio-lean
cd ramsey-ratio-lean
lake exe cache get      # mathlib pre-built oleans
lake build              # ~2 minutes warm cache
lake env lean -- -e \
    "import RamseyRatio; #print axioms RamseyRatio.ramsey_ratio_tendsto_one"
# → [propext, Classical.choice, Quot.sound]
```

To rebuild this very document:

```
lake build manual
.lake/build/bin/manual
python3 -m http.server 8000 --directory _out/html-single
```

The repository is structured as five Lean modules in dependency
order — `RamseyRatio.Basic`, `RamseyRatio.ErdosSzekeres`,
`RamseyRatio.LowerBound`, `RamseyRatio.DRC`,
`RamseyRatio.MainTheorem` — plus this Verso doc. Each module
opens with a `## §N. ...` table of contents. `PROOF_OUTLINE.md`
maps every paper step to a Lean theorem name. `ROADMAP.md` records
signature changes from the original sketch.

If you want to chase a specific step of the paper, the fastest path
is: read `PROOF_OUTLINE.md` first, then the corresponding section of
this post, then the Lean file.

# Acknowledgements & references

* P. Erdős. *Some unsolved problems in graph theory and combinatorial
  analysis.* Combinatorial Mathematics and its Applications,
  Academic Press, 1971.
* P. Erdős and G. Szekeres. *A combinatorial problem in geometry.*
  Compositio Math. 2, 1935.
* J. Fox and B. Sudakov. *Dependent random choice.*
  Random Structures Algorithms 38, 2011.
* OpenAI internal model. *On the ratio of `R(k, ℓ)` and `R(k, ℓ + 1)`.*
  2026 (the artifact under reproduction).
* Y. Zhao. *Graph theory and additive combinatorics: exploring
  structure and randomness.* Cambridge University Press, 2023.

The Lean infrastructure stands on `mathlib v4.28.0-rc1`. Verso, the
documentation system rendering this page, is by David Thrane
Christiansen at the Lean FRO. Codex CLI is OpenAI's. Claude is
Anthropic's. The `b-mehta/exponential-ramsey` project (Lean 3,
incompatible with our toolchain) was a source of inspiration even
though we couldn't depend on it.
