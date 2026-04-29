import RamseyRatio.Basic
import RamseyRatio.ErdosSzekeres
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast

/-!
# Lemma 2 — Off-diagonal probabilistic lower bound

For every fixed `k ≥ 3`, as `ℓ → ∞`, the off-diagonal Ramsey number
satisfies a polynomial lower bound. The headline result is

```
ramsey_lower_bound_power : ∃ C > 0, ∀ᶠ ℓ, C * ℓ^(k/2 - 1/4) ≤ R(k, ℓ)
```

with witness `C = 1/8`.

The paper's Lemma 2 states the slightly stronger `R(k, ℓ) ≫_k (ℓ / log ℓ)^(k/2)`,
but the proof of Theorem 1 (paper §2) uses Lemma 2 only as
`R(k, ℓ+1) - 1 ≫_k ℓ^(k/2 − o(1))`, and Remark 1 explicitly permits
weakened constants ("we do not attempt to optimize cₖ"). Our exponent
`k/2 - 1/4` is the smallest clean rational strictly above `⌈k/2⌉ - 1`,
which is the binding threshold for paper eq. (3).

## Proof structure (Erdős deletion method)

The argument averages over subsets `A ⊆ Sym2 (Fin n)` ("edge sets"),
each weighted by `p^|A| · (1-p)^(|edgeUniverse| - |A|)` for parameters
`n, p` to be chosen. The four sections build up to the main bound.

* §1 **Edge weights** (`edgeUniverse`, `edgesOn`, `edgeWeight`): the
  partition function `Σ_A edgeWeight A = 1`, plus disjoint/superset
  decomposition lemmas.
* §2 **Weighted clique/indep events** (`weighted_clique_events`,
  `weighted_indep_events`): the expected number of `k`-cliques /
  `ℓ`-independent sets in a `p`-weighted random graph,
  `Σ_A w(A) · #K_k(A) = (n choose k) · p^C(k,2)` and analogue.
* §3 **Ramsey bounds** (`basic_ramsey_bound`, `deletion_ramsey_bound`):
  averaging gives a single edge set realizing `≤ avg` clique/indep counts;
  the deletion variant produces a graph on `n/2` vertices avoiding both,
  hence `n/2 < R(k, ℓ)`.
* §4 **Concrete application** (`ramsey_lower_bound`,
  `ramsey_lower_bound_power`): plug `n ≈ ℓ^(k/2 - 1/4)`,
  `p ≈ ℓ^(-(2k-1)/(2k))`, verify the deletion hypothesis for `ℓ` large,
  and conclude.
-/

open Filter Asymptotics
open scoped BigOperators

namespace RamseyRatio

open SimpleGraph

/-! ### §1. Edge-set universe and the `p`-weighted partition function -/

private def edgeUniverse (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset

private def edgesOn {n : ℕ} (s : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((⊤ : SimpleGraph ({v // v ∈ (s : Set (Fin n))})).edgeFinset).map
    (Function.Embedding.subtype (fun v : Fin n => v ∈ (s : Set (Fin n)))).sym2Map

private lemma edgesOn_card {n : ℕ} (s : Finset (Fin n)) :
    (edgesOn s).card = Nat.choose s.card 2 := by
  classical
  rw [edgesOn, Finset.card_map, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  congr 1
  exact Fintype.card_coe s

private lemma mk_mem_edgesOn {n : ℕ} {s : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    Sym2.mk (a, b) ∈ edgesOn s := by
  classical
  rw [edgesOn, Finset.mem_map]
  refine ⟨Sym2.mk (⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
  · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [SimpleGraph.top_adj] using
      (show (⟨a, ha⟩ : {v // v ∈ (s : Set (Fin n))}) ≠ ⟨b, hb⟩ from by
        intro h
        exact hab (Subtype.ext_iff.mp h))
  · change Sym2.map (Function.Embedding.subtype (fun v : Fin n => v ∈ (s : Set (Fin n))))
        (Sym2.mk (⟨a, ha⟩, ⟨b, hb⟩)) = Sym2.mk (a, b)
    rfl

private lemma edgesOn_subset_universe {n : ℕ} (s : Finset (Fin n)) :
    edgesOn s ⊆ edgeUniverse n := by
  classical
  intro e he
  rw [edgeUniverse, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
  rw [edgesOn, Finset.mem_map] at he
  rcases he with ⟨e', he', rfl⟩
  rw [Set.mem_compl_iff, Sym2.mem_diagSet]
  change ¬(Sym2.map (Function.Embedding.subtype (fun v : Fin n => v ∈ (s : Set (Fin n)))) e').IsDiag
  rw [Sym2.isDiag_map
    (Function.Embedding.subtype (fun v : Fin n => v ∈ (s : Set (Fin n)))).injective]
  exact SimpleGraph.not_isDiag_of_mem_edgeFinset he'

private def edgeWeight {α : Type*} (E A : Finset α) (p : ℝ) : ℝ :=
  p ^ A.card * (1 - p) ^ (E.card - A.card)

private lemma sum_edgeWeight {α : Type*} (E : Finset α) (p : ℝ) :
    (∑ A ∈ E.powerset, edgeWeight E A p) = 1 := by
  classical
  simp_rw [edgeWeight]
  rw [Finset.sum_pow_mul_eq_add_pow]
  ring

private lemma sum_edgeWeight_superset {α : Type*} [DecidableEq α]
    (E T : Finset α) (hTE : T ⊆ E) (p : ℝ) :
    (∑ A ∈ E.powerset.filter (fun A => T ⊆ A), edgeWeight E A p) = p ^ T.card := by
  classical
  let D : Finset (Finset α) := (E \ T).powerset
  let F : Finset (Finset α) := E.powerset.filter (fun A => T ⊆ A)
  have hbij :
      (∑ U ∈ D, edgeWeight E (T ∪ U) p) =
        ∑ A ∈ F, edgeWeight E A p := by
    refine Finset.sum_bij (fun U _ => T ∪ U) ?hi ?hinj ?hsurj ?hval
    · intro U hU
      dsimp [F]
      rw [Finset.mem_filter, Finset.mem_powerset]
      have hUs : U ⊆ E \ T := by
        simpa [D] using Finset.mem_powerset.mp hU
      exact ⟨Finset.union_subset hTE
          (hUs.trans Finset.sdiff_subset),
        Finset.subset_union_left⟩
    · intro U hU V hV hUV
      change T ∪ U = T ∪ V at hUV
      have hUs : U ⊆ E \ T := by
        simpa [D] using Finset.mem_powerset.mp hU
      have hVs : V ⊆ E \ T := by
        simpa [D] using Finset.mem_powerset.mp hV
      ext x
      constructor <;> intro hx
      · have hxU : x ∈ T ∪ U := Finset.mem_union.mpr (Or.inr hx)
        rw [hUV] at hxU
        rcases Finset.mem_union.mp hxU with hxT | hxV
        · exact False.elim ((Finset.mem_sdiff.mp (hUs hx)).2 hxT)
        · exact hxV
      · have hxV : x ∈ T ∪ V := Finset.mem_union.mpr (Or.inr hx)
        rw [← hUV] at hxV
        rcases Finset.mem_union.mp hxV with hxT | hxU
        · exact False.elim ((Finset.mem_sdiff.mp (hVs hx)).2 hxT)
        · exact hxU
    · intro A hA
      have hAF : A ∈ E.powerset.filter (fun A => T ⊆ A) := by
        simpa [F] using hA
      have hApow : A ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hAF).1
      have hTA : T ⊆ A := (Finset.mem_filter.mp hAF).2
      refine ⟨A \ T, ?_, ?_⟩
      · dsimp [D]
        rw [Finset.mem_powerset]
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hApow (Finset.mem_sdiff.mp hx).1,
          (Finset.mem_sdiff.mp hx).2⟩
      · ext x
        constructor <;> intro hx
        · rcases Finset.mem_union.mp hx with hxT | hxAT
          · exact hTA hxT
          · exact (Finset.mem_sdiff.mp hxAT).1
        · by_cases hxT : x ∈ T
          · exact Finset.mem_union.mpr (Or.inl hxT)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
    · intro U hU
      rfl
  rw [← hbij]
  calc
    (∑ U ∈ D, edgeWeight E (T ∪ U) p)
        = ∑ U ∈ D, p ^ T.card *
            (p ^ U.card * (1 - p) ^ ((E \ T).card - U.card)) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUs : U ⊆ E \ T := Finset.mem_powerset.mp hU
            have hdisj : Disjoint T U := by
              rw [Finset.disjoint_left]
              intro x hxT hxU
              exact (Finset.mem_sdiff.mp (hUs hxU)).2 hxT
            have hcard_union : (T ∪ U).card = T.card + U.card :=
              Finset.card_union_of_disjoint hdisj
            have hcard_sdiff : (E \ T).card = E.card - T.card :=
              Finset.card_sdiff_of_subset hTE
            have hcard_diff :
                E.card - (T.card + U.card) = (E \ T).card - U.card := by
              rw [hcard_sdiff]
              omega
            simp [edgeWeight, hcard_union, hcard_diff]
            rw [pow_add]
            ring
    _ = p ^ T.card *
          (∑ U ∈ D, p ^ U.card * (1 - p) ^ ((E \ T).card - U.card)) := by
            rw [Finset.mul_sum]
    _ = p ^ T.card := by
            dsimp [D]
            rw [Finset.sum_pow_mul_eq_add_pow]
            ring

private lemma sum_edgeWeight_disjoint {α : Type*} [DecidableEq α]
    (E T : Finset α) (hTE : T ⊆ E) (p : ℝ) :
    (∑ A ∈ (E \ T).powerset, edgeWeight E A p) = (1 - p) ^ T.card := by
  classical
  calc
    (∑ A ∈ (E \ T).powerset, edgeWeight E A p)
        = ∑ A ∈ (E \ T).powerset,
            (1 - p) ^ T.card *
              (p ^ A.card * (1 - p) ^ ((E \ T).card - A.card)) := by
          refine Finset.sum_congr rfl ?_
          intro A hA
          have hAs : A ⊆ E \ T := Finset.mem_powerset.mp hA
          have hcard_sdiff : (E \ T).card = E.card - T.card :=
            Finset.card_sdiff_of_subset hTE
          have hcardA : A.card ≤ (E \ T).card := Finset.card_le_card hAs
          have hcardT : T.card ≤ E.card := Finset.card_le_card hTE
          have hcard_diff : E.card - A.card = T.card + ((E \ T).card - A.card) := by
            rw [hcard_sdiff]
            omega
          simp [edgeWeight, hcard_diff]
          rw [pow_add]
          ring
    _ = (1 - p) ^ T.card *
          (∑ A ∈ (E \ T).powerset,
            p ^ A.card * (1 - p) ^ ((E \ T).card - A.card)) := by
          rw [Finset.mul_sum]
    _ = (1 - p) ^ T.card := by
          rw [Finset.sum_pow_mul_eq_add_pow]
          ring

/-! ### §2. Weighted clique and independent-set events -/

private lemma weighted_clique_events (n k : ℕ) (p : ℝ) :
    (∑ A ∈ (edgeUniverse n).powerset,
      edgeWeight (edgeUniverse n) A p *
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun s => edgesOn s ⊆ A)).card) =
      ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 := by
  classical
  let E := edgeUniverse n
  let K : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
  calc
    (∑ A ∈ E.powerset, edgeWeight E A p *
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun s => edgesOn s ⊆ A)).card)
        = ∑ A ∈ E.powerset, edgeWeight E A p *
            (∑ s ∈ K, if edgesOn s ⊆ A then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro A hA
            congr 1
            rw [Finset.card_eq_sum_ones]
            simp [K]
    _ = ∑ s ∈ K, ∑ A ∈ E.powerset,
          edgeWeight E A p * (if edgesOn s ⊆ A then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            congr with A
            rw [Finset.mul_sum]
    _ = ∑ s ∈ K, p ^ Nat.choose k 2 := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hs_card : s.card = k := (Finset.mem_powersetCard.mp hs).2
            have hsum := sum_edgeWeight_superset E (edgesOn s) (edgesOn_subset_universe s) p
            rw [edgesOn_card, hs_card] at hsum
            rw [← hsum]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro A hA
            by_cases h : edgesOn s ⊆ A <;> simp [h]
    _ = ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
              Finset.card_univ, Fintype.card_fin]

private lemma weighted_indep_events (n l : ℕ) (p : ℝ) :
    (∑ A ∈ (edgeUniverse n).powerset,
      edgeWeight (edgeUniverse n) A p *
        (((Finset.univ : Finset (Fin n)).powersetCard l).filter
          (fun s => A ⊆ edgeUniverse n \ edgesOn s)).card) =
      ((Nat.choose n l : ℕ) : ℝ) * (1 - p) ^ Nat.choose l 2 := by
  classical
  let E := edgeUniverse n
  let L : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard l
  calc
    (∑ A ∈ E.powerset, edgeWeight E A p *
        (((Finset.univ : Finset (Fin n)).powersetCard l).filter
          (fun s => A ⊆ E \ edgesOn s)).card)
        = ∑ A ∈ E.powerset, edgeWeight E A p *
            (∑ s ∈ L, if A ⊆ E \ edgesOn s then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro A hA
            congr 1
            rw [Finset.card_eq_sum_ones]
            simp [L]
    _ = ∑ s ∈ L, ∑ A ∈ E.powerset,
          edgeWeight E A p * (if A ⊆ E \ edgesOn s then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            congr with A
            rw [Finset.mul_sum]
    _ = ∑ s ∈ L, (1 - p) ^ Nat.choose l 2 := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hs_card : s.card = l := (Finset.mem_powersetCard.mp hs).2
            have hsum := sum_edgeWeight_disjoint E (edgesOn s) (edgesOn_subset_universe s) p
            rw [edgesOn_card, hs_card] at hsum
            rw [← hsum]
            have hfilter :
                E.powerset.filter (fun A => A ⊆ E \ edgesOn s) =
                  (E \ edgesOn s).powerset := by
              ext A
              rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powerset]
              constructor
              · intro h
                exact h.2
              · intro h
                exact ⟨h.trans Finset.sdiff_subset, h⟩
            rw [← hfilter]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro A hA
            by_cases h : A ⊆ E \ edgesOn s <;> simp [h]
    _ = ((Nat.choose n l : ℕ) : ℝ) * (1 - p) ^ Nat.choose l 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
              Finset.card_univ, Fintype.card_fin]

private lemma edgeWeight_nonneg {α : Type*} {E A : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ edgeWeight E A p := by
  dsimp [edgeWeight]
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

private lemma edgeWeight_pos {α : Type*} {E A : Finset α} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < edgeWeight E A p := by
  dsimp [edgeWeight]
  exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

private lemma edgesOn_subset_of_isNClique {n k : ℕ}
    {A : Finset (Sym2 (Fin n))} {s : Finset (Fin n)}
    (h : (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).IsNClique k s) :
    edgesOn s ⊆ A := by
  classical
  intro e he
  rw [edgesOn, Finset.mem_map] at he
  rcases he with ⟨e', he', rfl⟩
  induction e' using Sym2.inductionOn with
  | hf x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      have hxy_ne_sub : x ≠ y := by simpa [SimpleGraph.top_adj] using he'
      have hxy_ne : x.1 ≠ y.1 := by
        intro hval
        exact hxy_ne_sub (Subtype.ext hval)
      have hadj : (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).Adj x.1 y.1 :=
        h.isClique x.2 y.2 hxy_ne
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      have hmem : Sym2.mk (x.1, y.1) ∈ (A : Set (Sym2 (Fin n))) :=
        hadj.1
      simpa using hmem

private lemma subset_sdiff_edgesOn_of_isNIndepSet {n l : ℕ}
    {A : Finset (Sym2 (Fin n))} {s : Finset (Fin n)}
    (hA : A ⊆ edgeUniverse n)
    (h : (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).IsNIndepSet l s) :
    A ⊆ edgeUniverse n \ edgesOn s := by
  classical
  intro e heA
  refine Finset.mem_sdiff.mpr ⟨hA heA, ?_⟩
  intro heS
  rw [edgesOn, Finset.mem_map] at heS
  rcases heS with ⟨e', he', heq⟩
  induction e' using Sym2.inductionOn with
  | hf x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      have hxy_ne_sub : x ≠ y := by simpa [SimpleGraph.top_adj] using he'
      have hxy_ne : x.1 ≠ y.1 := by
        intro hval
        exact hxy_ne_sub (Subtype.ext hval)
      have heq' : e = Sym2.mk (x.1, y.1) := by
        rw [← heq]
        rfl
      have hadj : (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).Adj x.1 y.1 := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨by simpa [heq'] using heA, hxy_ne⟩
      exact h.isIndepSet x.2 y.2 hxy_ne hadj

private lemma hasRamseyProperty_mono_vertices {N M k ℓ : ℕ}
    (hNM : N ≤ M) (hN : HasRamseyProperty N k ℓ) : HasRamseyProperty M k ℓ := by
  classical
  intro G
  have hcard : N ≤ (Finset.univ : Finset (Fin M)).card := by
    simpa using hNM
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcard
  rcases ramseyProperty_of_finset G hs_card hN with
    ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact Or.inl ⟨t, ht⟩
  · exact Or.inr ⟨t, ht⟩

/-! ### §3. First-moment and deletion Ramsey bounds -/

private lemma basic_ramsey_bound {k ℓ n : ℕ} {p : ℝ}
    (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hp0 : 0 < p) (hp1 : p < 1)
    (hV : ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
        ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 < 1) :
    n < R(k, ℓ) := by
  classical
  by_contra hnlt
  push_neg at hnlt
  let E := edgeUniverse n
  let K : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
  let L : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard ℓ
  have hpropR : HasRamseyProperty R(k, ℓ) k ℓ :=
    ramsey_mem_property k ℓ hk hℓ
  have hpropn : HasRamseyProperty n k ℓ :=
    hasRamseyProperty_mono_vertices hnlt hpropR
  have hpoint : ∀ A ∈ E.powerset,
      edgeWeight E A p ≤
        edgeWeight E A p *
          (((K.filter (fun s => edgesOn s ⊆ A)).card : ℝ) +
            ((L.filter (fun s => A ⊆ E \ edgesOn s)).card : ℝ)) := by
    intro A hA
    have hAsub : A ⊆ E := Finset.mem_powerset.mp hA
    have hweight : 0 ≤ edgeWeight E A p :=
      edgeWeight_nonneg hp0.le hp1.le
    have hbad :
        1 ≤ (K.filter (fun s => edgesOn s ⊆ A)).card +
          (L.filter (fun s => A ⊆ E \ edgesOn s)).card := by
      rcases hpropn (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))) with
        ⟨s, hs⟩ | ⟨s, hs⟩
      · have hsK : s ∈ K := by
          dsimp [K]
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ s, hs.card_eq⟩
        have hsEvent : edgesOn s ⊆ A := edgesOn_subset_of_isNClique hs
        have hmem : s ∈ K.filter (fun s => edgesOn s ⊆ A) := by
          rw [Finset.mem_filter]
          exact ⟨hsK, hsEvent⟩
        have hpos : 0 < (K.filter (fun s => edgesOn s ⊆ A)).card :=
          Finset.card_pos.mpr ⟨s, hmem⟩
        omega
      · have hsL : s ∈ L := by
          dsimp [L]
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ s, hs.card_eq⟩
        have hsEvent : A ⊆ E \ edgesOn s :=
          subset_sdiff_edgesOn_of_isNIndepSet hAsub hs
        have hmem : s ∈ L.filter (fun s => A ⊆ E \ edgesOn s) := by
          rw [Finset.mem_filter]
          exact ⟨hsL, hsEvent⟩
        have hpos : 0 < (L.filter (fun s => A ⊆ E \ edgesOn s)).card :=
          Finset.card_pos.mpr ⟨s, hmem⟩
        omega
    have hbadR :
        (1 : ℝ) ≤
          (((K.filter (fun s => edgesOn s ⊆ A)).card : ℝ) +
            ((L.filter (fun s => A ⊆ E \ edgesOn s)).card : ℝ)) := by
      exact_mod_cast hbad
    calc
      edgeWeight E A p = edgeWeight E A p * 1 := by ring
      _ ≤ edgeWeight E A p *
          (((K.filter (fun s => edgesOn s ⊆ A)).card : ℝ) +
            ((L.filter (fun s => A ⊆ E \ edgesOn s)).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbadR hweight
  have hsum_le :
      (∑ A ∈ E.powerset, edgeWeight E A p) ≤
        ∑ A ∈ E.powerset,
          edgeWeight E A p *
            (((K.filter (fun s => edgesOn s ⊆ A)).card : ℝ) +
              ((L.filter (fun s => A ⊆ E \ edgesOn s)).card : ℝ)) :=
    Finset.sum_le_sum fun A hA => hpoint A hA
  have hright :
      (∑ A ∈ E.powerset,
          edgeWeight E A p *
            (((K.filter (fun s => edgesOn s ⊆ A)).card : ℝ) +
              ((L.filter (fun s => A ⊆ E \ edgesOn s)).card : ℝ))) =
        ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
          ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    dsimp [E, K, L]
    rw [weighted_clique_events, weighted_indep_events]
  have hone :
      (∑ A ∈ E.powerset, edgeWeight E A p) = 1 := sum_edgeWeight E p
  have : (1 : ℝ) ≤
      ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
        ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 := by
    rw [← hright, ← hone]
    exact hsum_le
  linarith

private lemma deletion_ramsey_bound {k ℓ n : ℕ} {p : ℝ}
    (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n)
    (hV : ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
        ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤ (n : ℝ) / 2) :
    n / 2 < R(k, ℓ) := by
  classical
  by_contra hnlt
  push_neg at hnlt
  let E := edgeUniverse n
  let K : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
  let L : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard ℓ
  let badCount : Finset (Sym2 (Fin n)) → ℕ :=
    fun A => (K.filter (fun s => edgesOn s ⊆ A)).card +
      (L.filter (fun s => A ⊆ E \ edgesOn s)).card
  have hexists :
      ∃ A ∈ E.powerset, ((badCount A : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    by_contra hnone
    push_neg at hnone
    have hstrict : (n : ℝ) / 2 <
        ∑ A ∈ E.powerset, edgeWeight E A p * ((badCount A : ℕ) : ℝ) := by
      have hsum_left :
          (∑ A ∈ E.powerset, edgeWeight E A p * ((n : ℝ) / 2)) = (n : ℝ) / 2 := by
        calc
          (∑ A ∈ E.powerset, edgeWeight E A p * ((n : ℝ) / 2)) =
              (∑ A ∈ E.powerset, edgeWeight E A p) * ((n : ℝ) / 2) := by
                rw [Finset.sum_mul]
          _ = (n : ℝ) / 2 := by
                rw [sum_edgeWeight E p]
                ring
      rw [← hsum_left]
      refine Finset.sum_lt_sum_of_nonempty ?_ ?_
      · exact ⟨∅, by simp [E]⟩
      · intro A hA
        exact mul_lt_mul_of_pos_left (hnone A hA) (edgeWeight_pos hp0 hp1)
    have hright :
        (∑ A ∈ E.powerset, edgeWeight E A p * ((badCount A : ℕ) : ℝ)) =
          ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
            ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 := by
      dsimp [badCount]
      simp_rw [Nat.cast_add, mul_add]
      rw [Finset.sum_add_distrib]
      dsimp [E, K, L]
      rw [weighted_clique_events, weighted_indep_events]
    linarith
  obtain ⟨A, hA_pow, hA_bad⟩ := hexists
  have hAsub : A ⊆ E := Finset.mem_powerset.mp hA_pow
  let G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))
  let Kbad : Finset (Finset (Fin n)) := K.filter (fun s => edgesOn s ⊆ A)
  let Lbad : Finset (Finset (Fin n)) := L.filter (fun s => A ⊆ E \ edgesOn s)
  let pickK : (s : Finset (Fin n)) → s ∈ Kbad → Fin n :=
    fun s hs =>
      Classical.choose (Finset.card_pos.mp (by
        have hsK : s ∈ K := (Finset.mem_filter.mp hs).1
        have hcard : s.card = k := (Finset.mem_powersetCard.mp hsK).2
        rw [hcard]
        exact hk))
  let pickL : (s : Finset (Fin n)) → s ∈ Lbad → Fin n :=
    fun s hs =>
      Classical.choose (Finset.card_pos.mp (by
        have hsL : s ∈ L := (Finset.mem_filter.mp hs).1
        have hcard : s.card = ℓ := (Finset.mem_powersetCard.mp hsL).2
        rw [hcard]
        exact hℓ))
  let DK : Finset (Fin n) := Kbad.attach.image fun s => pickK s.1 s.2
  let DL : Finset (Fin n) := Lbad.attach.image fun s => pickL s.1 s.2
  let D : Finset (Fin n) := DK ∪ DL
  have hD_card_le : D.card ≤ Kbad.card + Lbad.card := by
    calc
      D.card ≤ DK.card + DL.card := Finset.card_union_le DK DL
      _ ≤ Kbad.card + Lbad.card := by
        have hDK : DK.card ≤ Kbad.card := by
          dsimp [DK]
          calc
            (Kbad.attach.image fun s => pickK s.1 s.2).card ≤ Kbad.attach.card :=
              Finset.card_image_le
            _ = Kbad.card := by simp
        have hDL : DL.card ≤ Lbad.card := by
          dsimp [DL]
          calc
            (Lbad.attach.image fun s => pickL s.1 s.2).card ≤ Lbad.attach.card :=
              Finset.card_image_le
            _ = Lbad.card := by simp
        exact Nat.add_le_add hDK hDL
  let W : Finset (Fin n) := Finset.univ \ D
  have hD_le_half : D.card ≤ n / 2 := by
    have hbad_nat : Kbad.card + Lbad.card ≤ n / 2 := by
      have hbad_cast : ((Kbad.card + Lbad.card : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
        simpa [badCount, Kbad, Lbad] using hA_bad
      have htwice_cast : (((Kbad.card + Lbad.card : ℕ) : ℝ) * 2) ≤ (n : ℝ) := by
        nlinarith
      have htwice_nat : (Kbad.card + Lbad.card) * 2 ≤ n := by
        exact_mod_cast htwice_cast
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      simpa [mul_comm] using htwice_nat
    exact hD_card_le.trans hbad_nat
  have hW_large : n / 2 ≤ W.card := by
    have hD_univ : D ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ D
    have hW_card : W.card = n - D.card := by
      dsimp [W]
      rw [Finset.card_sdiff_of_subset hD_univ, Finset.card_univ, Fintype.card_fin]
    rw [hW_card]
    omega
  obtain ⟨W', hW'_sub, hW'_card⟩ := Finset.exists_subset_card_eq hW_large
  have hpropR : HasRamseyProperty R(k, ℓ) k ℓ :=
    ramsey_mem_property k ℓ hk hℓ
  have hprop_half : HasRamseyProperty (n / 2) k ℓ :=
    hasRamseyProperty_mono_vertices hnlt hpropR
  rcases ramseyProperty_of_finset G hW'_card hprop_half with
    ⟨T, hT_sub, hT_clique⟩ | ⟨T, hT_sub, hT_indep⟩
  · have hTK : T ∈ K := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ T, hT_clique.card_eq⟩
    have hTEvent : edgesOn T ⊆ A := edgesOn_subset_of_isNClique hT_clique
    have hTbad : T ∈ Kbad := by
      rw [Finset.mem_filter]
      exact ⟨hTK, hTEvent⟩
    have hpick_mem_T : pickK T hTbad ∈ T :=
      Classical.choose_spec (Finset.card_pos.mp (by
        have hcard : T.card = k := (Finset.mem_powersetCard.mp hTK).2
        rw [hcard]
        exact hk))
    have hpick_D : pickK T hTbad ∈ D := by
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨T, hTbad⟩, Finset.mem_attach _ _, rfl⟩
    have hpick_W : pickK T hTbad ∈ W := hW'_sub (hT_sub hpick_mem_T)
    exact (Finset.mem_sdiff.mp hpick_W).2 hpick_D
  · have hTL : T ∈ L := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ T, hT_indep.card_eq⟩
    have hTEvent : A ⊆ E \ edgesOn T :=
      subset_sdiff_edgesOn_of_isNIndepSet hAsub hT_indep
    have hTbad : T ∈ Lbad := by
      rw [Finset.mem_filter]
      exact ⟨hTL, hTEvent⟩
    have hpick_mem_T : pickL T hTbad ∈ T :=
      Classical.choose_spec (Finset.card_pos.mp (by
        have hcard : T.card = ℓ := (Finset.mem_powersetCard.mp hTL).2
        rw [hcard]
        exact hℓ))
    have hpick_D : pickL T hTbad ∈ D := by
      refine Finset.mem_union.mpr (Or.inr ?_)
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨T, hTbad⟩, Finset.mem_attach _ _, rfl⟩
    have hpick_W : pickL T hTbad ∈ W := hW'_sub (hT_sub hpick_mem_T)
    exact (Finset.mem_sdiff.mp hpick_W).2 hpick_D

private lemma basic_ramsey_bound_pow {k ℓ n : ℕ} {p : ℝ}
    (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hp0 : 0 < p) (hp1 : p < 1)
    (hV : (n : ℝ) ^ k * p ^ Nat.choose k 2 +
        (n : ℝ) ^ ℓ * (1 - p) ^ Nat.choose ℓ 2 < 1) :
    n < R(k, ℓ) := by
  have hchoose_k : ((Nat.choose n k : ℕ) : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.choose_le_pow n k
  have hchoose_l : ((Nat.choose n ℓ : ℕ) : ℝ) ≤ (n : ℝ) ^ ℓ := by
    exact_mod_cast Nat.choose_le_pow n ℓ
  have hpk_nonneg : 0 ≤ p ^ Nat.choose k 2 := pow_nonneg hp0.le _
  have hpl_nonneg : 0 ≤ (1 - p) ^ Nat.choose ℓ 2 :=
    pow_nonneg (sub_nonneg.mpr hp1.le) _
  exact basic_ramsey_bound hk hℓ hp0 hp1 (by
    nlinarith [mul_le_mul_of_nonneg_right hchoose_k hpk_nonneg,
      mul_le_mul_of_nonneg_right hchoose_l hpl_nonneg])

private lemma choose_two_ge_sq_div_four {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ((ℓ : ℝ) ^ 2) / 4 ≤ (Nat.choose ℓ 2 : ℝ) := by
  rw [Nat.cast_choose_two ℝ]
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  nlinarith [sq_nonneg ((ℓ : ℝ) - 2)]

private lemma eventually_ceil_rpow_le_two_mul {α : ℝ} (hα : 0 < α) :
    ∀ᶠ ℓ : ℕ in atTop, (Nat.ceil ((ℓ : ℝ) ^ α) : ℝ) ≤ 2 * (ℓ : ℝ) ^ α := by
  have htend : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [htend.eventually_ge_atTop ((2 : ℝ)⁻¹)] with ℓ hℓ
  exact Nat.ceil_le_two_mul hℓ

private lemma tendsto_const_mul_log_div_nat (A : ℝ) :
    Tendsto (fun ℓ : ℕ => A * Real.log (ℓ : ℝ) / (ℓ : ℝ)) atTop (nhds 0) := by
  have hlogO : (fun ℓ : ℕ => Real.log (ℓ : ℝ)) =o[atTop] fun ℓ : ℕ => (ℓ : ℝ) := by
    simpa using (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv : Tendsto (fun ℓ : ℕ => Real.log (ℓ : ℝ) / (ℓ : ℝ)) atTop (nhds 0) :=
    hlogO.tendsto_div_nhds_zero
  have hmul := (tendsto_const_nhds (x := A)).mul hdiv
  simpa [mul_div_assoc] using hmul

private lemma tendsto_const_mul_rpow_neg_nat {C s : ℝ} (hs : 0 < s) :
    Tendsto (fun ℓ : ℕ => C * (ℓ : ℝ) ^ (-s)) atTop (nhds 0) := by
  have hpow : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ (-s)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using (tendsto_const_nhds (x := C)).mul hpow

private lemma tendsto_self_mul_log_nat_atTop :
    Tendsto (fun ℓ : ℕ => (ℓ : ℝ) * Real.log (ℓ : ℝ)) atTop atTop := by
  have hx : Tendsto (fun ℓ : ℕ => (ℓ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Tendsto (fun ℓ : ℕ => Real.log (ℓ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  refine Filter.tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [Filter.eventually_ge_atTop 1] with ℓ hℓ
  have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlog_nonneg : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg hx1
  nlinarith [mul_le_mul_of_nonneg_right hx1 hlog_nonneg]

private lemma tendsto_exp_neg_const_mul_self_log_nat {B : ℝ} (hB : 0 < B) :
    Tendsto (fun ℓ : ℕ => Real.exp (-(B * ((ℓ : ℝ) * Real.log (ℓ : ℝ)))))
      atTop (nhds 0) := by
  have hxlog : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) * Real.log (ℓ : ℝ)) atTop atTop :=
    tendsto_self_mul_log_nat_atTop
  have hBtop : Tendsto (fun ℓ : ℕ => B * ((ℓ : ℝ) * Real.log (ℓ : ℝ))) atTop atTop := by
    exact hxlog.const_mul_atTop hB
  have hbot : Tendsto (fun ℓ : ℕ => -(B * ((ℓ : ℝ) * Real.log (ℓ : ℝ)))) atTop atBot := by
    exact Filter.tendsto_neg_atTop_atBot.comp hBtop
  exact Real.tendsto_exp_atBot.comp hbot

private lemma eventually_log_rpow_le_rpow_nat (r k : ℕ) (hk : 0 < k) :
    ∀ᶠ ℓ : ℕ in atTop,
      Real.log (ℓ : ℝ) ^ (r : ℝ) ≤ (ℓ : ℝ) ^ ((k : ℝ) / 8) := by
  have hk8 : (0 : ℝ) < (k : ℝ) / 8 := by positivity
  have hO : (fun ℓ : ℕ => Real.log (ℓ : ℝ) ^ (r : ℝ)) =o[atTop]
      fun ℓ : ℕ => (ℓ : ℝ) ^ ((k : ℝ) / 8) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (r : ℝ) hk8).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hO.eventuallyLE, Filter.eventually_ge_atTop 1] with ℓ hle hℓ
  have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hx0 : (0 : ℝ) ≤ ℓ := by positivity
  have hlog_nonneg : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg hx1
  have hleft_nonneg : 0 ≤ Real.log (ℓ : ℝ) ^ (r : ℝ) :=
    Real.rpow_nonneg hlog_nonneg _
  have hright_nonneg : 0 ≤ (ℓ : ℝ) ^ ((k : ℝ) / 8) :=
    Real.rpow_nonneg hx0 _
  have hleft_abs : ‖Real.log (ℓ : ℝ) ^ (r : ℝ)‖ = Real.log (ℓ : ℝ) ^ (r : ℝ) := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hleft_nonneg
  have hright_abs : ‖(ℓ : ℝ) ^ ((k : ℝ) / 8)‖ = (ℓ : ℝ) ^ ((k : ℝ) / 8) := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hright_nonneg
  simpa [hleft_abs, hright_abs, abs_of_nonneg hlog_nonneg] using hle

private lemma clique_term_bound {k n ℓ : ℕ} {α A : ℝ}
    (hα : α = (k : ℝ) / 2 - 3 / 4)
    (hA0 : 0 ≤ A) (hn : (n : ℝ) ≤ 2 * (ℓ : ℝ) ^ α)
    (hℓ1 : 1 ≤ (ℓ : ℝ))
    (hlog : Real.log (ℓ : ℝ) ^ (Nat.choose k 2 : ℝ) ≤ (ℓ : ℝ) ^ ((k : ℝ) / 8)) :
    (n : ℝ) ^ k * (A * Real.log (ℓ : ℝ) / (ℓ : ℝ)) ^ Nat.choose k 2 ≤
      (2 : ℝ) ^ k * A ^ Nat.choose k 2 * (ℓ : ℝ) ^ (-((k : ℝ) / 8)) := by
  let x : ℝ := ℓ
  have hx0 : 0 < x := by dsimp [x]; nlinarith
  have hx0le : 0 ≤ x := hx0.le
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hℓ1
  have hn_pow : (n : ℝ) ^ k ≤ (2 * x ^ α) ^ k := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by simpa [x] using hn) k
  have hp_eq : (A * Real.log x / x) ^ Nat.choose k 2 =
      A ^ Nat.choose k 2 * Real.log x ^ Nat.choose k 2 / x ^ Nat.choose k 2 := by
    ring
  have hlog_nat : Real.log x ^ Nat.choose k 2 ≤ x ^ ((k : ℝ) / 8) := by
    rw [← Real.rpow_natCast (Real.log x) (Nat.choose k 2)]
    simpa [x] using hlog
  have hA_pow_nonneg : 0 ≤ A ^ Nat.choose k 2 := pow_nonneg hA0 _
  calc
    (n : ℝ) ^ k * (A * Real.log (ℓ : ℝ) / (ℓ : ℝ)) ^ Nat.choose k 2
        = (n : ℝ) ^ k * (A * Real.log x / x) ^ Nat.choose k 2 := by simp [x]
    _ ≤ (2 * x ^ α) ^ k * (A * Real.log x / x) ^ Nat.choose k 2 := by
      exact mul_le_mul_of_nonneg_right hn_pow (pow_nonneg (by positivity) _)
    _ = (2 * x ^ α) ^ k * (A ^ Nat.choose k 2 * Real.log x ^ Nat.choose k 2 /
        x ^ Nat.choose k 2) := by
      rw [hp_eq]
    _ ≤ (2 * x ^ α) ^ k * (A ^ Nat.choose k 2 * x ^ ((k : ℝ) / 8) /
        x ^ Nat.choose k 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog_nat hA_pow_nonneg) (pow_nonneg hx0le _)
    _ = (2 : ℝ) ^ k * A ^ Nat.choose k 2 * x ^ (-((k : ℝ) / 8)) := by
      have hxalg : x ^ (α * (k : ℝ)) * x ^ ((k : ℝ) / 8) / x ^ Nat.choose k 2 =
          x ^ (-((k : ℝ) / 8)) := by
        have hchoose : ((Nat.choose k 2 : ℕ) : ℝ) =
            (k : ℝ) * ((k : ℝ) - 1) / 2 := by
          rw [Nat.cast_choose_two ℝ]
        rw [← Real.rpow_natCast x (Nat.choose k 2)]
        rw [← Real.rpow_add hx0]
        rw [← Real.rpow_sub hx0]
        congr 1
        rw [hchoose, hα]
        ring
      rw [show (2 * x ^ α) ^ k = (2 : ℝ) ^ k * (x ^ α) ^ k by ring]
      rw [show (x ^ α) ^ k = x ^ (α * (k : ℝ)) by
        rw [← Real.rpow_natCast (x ^ α) k, ← Real.rpow_mul hx0le α (k : ℝ)]]
      rw [← hxalg]
      ring
    _ = (2 : ℝ) ^ k * A ^ Nat.choose k 2 * (ℓ : ℝ) ^ (-((k : ℝ) / 8)) := by
      simp [x]

private lemma indep_term_bound {n ℓ : ℕ} {α A p : ℝ}
    (hp : p = A * Real.log (ℓ : ℝ) / (ℓ : ℝ))
    (hA0 : 0 ≤ A) (hp1 : p < 1)
    (hn : (n : ℝ) ≤ (ℓ : ℝ) ^ (α + 1))
    (hℓ : 2 ≤ ℓ) :
    (n : ℝ) ^ ℓ * (1 - p) ^ Nat.choose ℓ 2 ≤
      Real.exp (-((A / 4 - (α + 1)) * ((ℓ : ℝ) * Real.log (ℓ : ℝ)))) := by
  let x : ℝ := ℓ
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hℓ
  have hx0 : 0 < x := by nlinarith
  have hx0le : 0 ≤ x := hx0.le
  have hx1 : 1 ≤ x := by nlinarith
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hchoose : x ^ 2 / 4 ≤ (Nat.choose ℓ 2 : ℝ) := by
    simpa [x] using choose_two_ge_sq_div_four hℓ
  have hpm_nonneg : 0 ≤ A * Real.log x / x :=
    div_nonneg (mul_nonneg hA0 hlog_nonneg) hx0le
  have hn_pow : (n : ℝ) ^ ℓ ≤ (x ^ (α + 1)) ^ ℓ := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by simpa [x] using hn) ℓ
  have hn_exp : (x ^ (α + 1)) ^ ℓ = Real.exp ((α + 1) * (x * Real.log x)) := by
    rw [← Real.rpow_natCast (x ^ (α + 1)) ℓ]
    rw [← Real.rpow_mul hx0le (α + 1) (ℓ : ℝ)]
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [x]
    ring
  have hbase : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have hpow_exp : (1 - p) ^ Nat.choose ℓ 2 ≤ Real.exp (-(A / 4) * (x * Real.log x)) := by
    have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp1.le) hbase (Nat.choose ℓ 2)
    refine hpow.trans ?_
    rw [← Real.exp_nat_mul]
    rw [Real.exp_le_exp]
    have hp_choose : (A / 4) * (x * Real.log x) ≤ p * (Nat.choose ℓ 2 : ℝ) := by
      calc
        (A / 4) * (x * Real.log x)
            = (A * Real.log x / x) * (x ^ 2 / 4) := by
                field_simp [hx0.ne']
        _ ≤ (A * Real.log x / x) * (Nat.choose ℓ 2 : ℝ) := by
                exact mul_le_mul_of_nonneg_left hchoose hpm_nonneg
        _ = p * (Nat.choose ℓ 2 : ℝ) := by
                simp [hp, x]
    nlinarith
  calc
    (n : ℝ) ^ ℓ * (1 - p) ^ Nat.choose ℓ 2
        ≤ (x ^ (α + 1)) ^ ℓ * Real.exp (-(A / 4) * (x * Real.log x)) := by
          exact mul_le_mul hn_pow hpow_exp (pow_nonneg (sub_nonneg.mpr hp1.le) _)
            (pow_nonneg (Real.rpow_nonneg hx0le _) _)
    _ = Real.exp (-((A / 4 - (α + 1)) * (x * Real.log x))) := by
      rw [hn_exp, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-((A / 4 - (α + 1)) * ((ℓ : ℝ) * Real.log (ℓ : ℝ)))) := by
      simp [x]

/-! ### §4. Concrete lower bounds — linear and polynomial -/

private lemma hasRamseyProperty_two_of_le_left {N k ℓ : ℕ} (hk : 2 ≤ k)
    (h : HasRamseyProperty N k ℓ) : HasRamseyProperty N 2 ℓ := by
  classical
  intro G
  rcases h G with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hcard : 2 ≤ s.card := by
      rw [hs.card_eq]
      exact hk
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
    refine Or.inl ⟨t, ?_, htcard⟩
    intro a ha b hb hab
    exact hs.isClique (htsub ha) (htsub hb) hab
  · exact Or.inr ⟨s, hs⟩

/-- **Lemma 2 (weakened).** For each fixed `k ≥ 3`, the off-diagonal Ramsey
number has the eventual linear lower bound `R(k, ℓ) ≥ ℓ`. -/
theorem ramsey_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ ℓ : ℕ in atTop, (ℓ : ℝ) ≤ (R(k, ℓ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 2] with ℓ hℓ
  have hmem : HasRamseyProperty R(k, ℓ) k ℓ :=
    ramsey_mem_property k ℓ (by omega) (by omega)
  have htwo : HasRamseyProperty R(k, ℓ) 2 ℓ :=
    hasRamseyProperty_two_of_le_left (by omega : 2 ≤ k) hmem
  have hle : R(2, ℓ) ≤ R(k, ℓ) :=
    Nat.sInf_le (show R(k, ℓ) ∈ {N | HasRamseyProperty N 2 ℓ} from htwo)
  have hℓ_le : ℓ ≤ R(k, ℓ) := by
    simpa [ramsey_two ℓ hℓ] using hle
  exact_mod_cast hℓ_le

private lemma eventually_four_mul_const_log_le_rpow_nat {A γ : ℝ}
    (hA0 : 0 ≤ A) (hγ : 0 < γ) :
    ∀ᶠ ℓ : ℕ in atTop, 4 * A * Real.log (ℓ : ℝ) ≤ (ℓ : ℝ) ^ γ := by
  have hO : (fun ℓ : ℕ => 4 * A * Real.log (ℓ : ℝ)) =o[atTop]
      fun ℓ : ℕ => (ℓ : ℝ) ^ γ := by
    simpa [mul_assoc] using
      ((isLittleO_log_rpow_atTop hγ).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_left (4 * A)
  filter_upwards [hO.eventuallyLE, Filter.eventually_ge_atTop 1] with ℓ hle hℓ
  have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hx0 : (0 : ℝ) ≤ ℓ := by positivity
  have hlog_nonneg : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg hx1
  have hleft_nonneg : 0 ≤ 4 * A * Real.log (ℓ : ℝ) := by positivity
  have hright_nonneg : 0 ≤ (ℓ : ℝ) ^ γ := Real.rpow_nonneg hx0 _
  have hleft_abs : ‖4 * A * Real.log (ℓ : ℝ)‖ = 4 * A * Real.log (ℓ : ℝ) := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hleft_nonneg
  have hright_abs : ‖(ℓ : ℝ) ^ γ‖ = (ℓ : ℝ) ^ γ := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hright_nonneg
  simpa [hleft_abs, hright_abs] using hle

private lemma poly_clique_term_bound {k n ℓ : ℕ} {α β p : ℝ}
    (hk : 0 < k)
    (hα : α = (k : ℝ) / 2 - 1 / 4)
    (hβ : β = 1 - 1 / (2 * (k : ℝ)))
    (hp : p = (ℓ : ℝ) ^ (-β))
    (hn : (n : ℝ) ≤ (ℓ : ℝ) ^ α)
    (hℓpos : 0 < (ℓ : ℝ)) :
    ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 ≤
      (ℓ : ℝ) ^ α / (Nat.factorial k : ℝ) := by
  have hchoose : ((Nat.choose n k : ℕ) : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) k n)
  have hfac_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hℓnonneg : 0 ≤ (ℓ : ℝ) := hℓpos.le
  have hn_pow : (n : ℝ) ^ k ≤ ((ℓ : ℝ) ^ α) ^ k := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) hn k
  have hp_pow_eq : p ^ Nat.choose k 2 = (ℓ : ℝ) ^ (-(β * (Nat.choose k 2 : ℝ))) := by
    rw [hp]
    rw [← Real.rpow_natCast ((ℓ : ℝ) ^ (-β)) (Nat.choose k 2)]
    rw [← Real.rpow_mul hℓnonneg (-β) (Nat.choose k 2 : ℝ)]
    ring_nf
  have hpow_mul_eq : ((ℓ : ℝ) ^ α) ^ k * p ^ Nat.choose k 2 = (ℓ : ℝ) ^ α := by
    rw [hp_pow_eq]
    rw [← Real.rpow_natCast ((ℓ : ℝ) ^ α) k]
    rw [← Real.rpow_mul hℓnonneg α (k : ℝ)]
    rw [← Real.rpow_add hℓpos]
    congr 1
    rw [Nat.cast_choose_two ℝ]
    rw [hα, hβ]
    have hkR : (k : ℝ) ≠ 0 := by positivity
    field_simp [hkR]
    ring
  have hp_pow_nonneg : 0 ≤ p ^ Nat.choose k 2 := pow_nonneg (by rw [hp]; positivity) _
  calc
    ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2
        ≤ ((n : ℝ) ^ k / (Nat.factorial k : ℝ)) * p ^ Nat.choose k 2 := by
          exact mul_le_mul_of_nonneg_right hchoose hp_pow_nonneg
    _ ≤ (((ℓ : ℝ) ^ α) ^ k / (Nat.factorial k : ℝ)) * p ^ Nat.choose k 2 := by
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hn_pow hfac_pos.le) hp_pow_nonneg
    _ = (ℓ : ℝ) ^ α / (Nat.factorial k : ℝ) := by
          rw [div_mul_eq_mul_div, hpow_mul_eq]

private lemma poly_indep_term_bound {n ℓ : ℕ} {α β p : ℝ}
    (hp : p = (ℓ : ℝ) ^ (-β))
    (hp0 : 0 < p) (hp1 : p < 1)
    (hn : (n : ℝ) ≤ (ℓ : ℝ) ^ α)
    (hℓ : 2 ≤ ℓ) :
    ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤
      Real.exp (α * ((ℓ : ℝ) * Real.log (ℓ : ℝ)) - ((ℓ : ℝ) ^ (2 - β)) / 4) := by
  let x : ℝ := ℓ
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hℓ
  have hx0 : 0 < x := by nlinarith
  have hx0le : 0 ≤ x := hx0.le
  have hchoose : ((Nat.choose n ℓ : ℕ) : ℝ) ≤ (n : ℝ) ^ ℓ := by
    exact_mod_cast Nat.choose_le_pow n ℓ
  have hn_pow : (n : ℝ) ^ ℓ ≤ (x ^ α) ^ ℓ := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by simpa [x] using hn) ℓ
  have hn_exp : (x ^ α) ^ ℓ = Real.exp (α * (x * Real.log x)) := by
    rw [← Real.rpow_natCast (x ^ α) ℓ]
    rw [← Real.rpow_mul hx0le α (ℓ : ℝ)]
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [x]
    ring
  have hpm_nonneg : 0 ≤ p := hp0.le
  have hchoose_lower : x ^ 2 / 4 ≤ (Nat.choose ℓ 2 : ℝ) := by
    simpa [x] using choose_two_ge_sq_div_four hℓ
  have hp_sq : p * (x ^ 2 / 4) = x ^ (2 - β) / 4 := by
    rw [hp]
    change x ^ (-β) * (x ^ 2 / 4) = x ^ (2 - β) / 4
    calc
      x ^ (-β) * (x ^ 2 / 4) = (x ^ (-β) * x ^ 2) / 4 := by ring
      _ = x ^ (2 - β) / 4 := by
          congr 1
          rw [show x ^ 2 = x ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
          rw [← Real.rpow_add hx0]
          ring_nf
  have hpow_exp : (1 - p) ^ Nat.choose ℓ 2 ≤ Real.exp (-(x ^ (2 - β) / 4)) := by
    have hbase : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
    have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp1.le) hbase (Nat.choose ℓ 2)
    refine hpow.trans ?_
    rw [← Real.exp_nat_mul]
    rw [Real.exp_le_exp]
    have hp_choose : x ^ (2 - β) / 4 ≤ p * (Nat.choose ℓ 2 : ℝ) := by
      rw [← hp_sq]
      exact mul_le_mul_of_nonneg_left hchoose_lower hpm_nonneg
    nlinarith
  calc
    ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2
        ≤ (x ^ α) ^ ℓ * Real.exp (-(x ^ (2 - β) / 4)) := by
          exact mul_le_mul (hchoose.trans hn_pow) hpow_exp
            (pow_nonneg (sub_nonneg.mpr hp1.le) _) (pow_nonneg (Real.rpow_nonneg hx0le _) _)
    _ = Real.exp (α * (x * Real.log x) - x ^ (2 - β) / 4) := by
      rw [hn_exp, ← Real.exp_add]
      ring_nf

private lemma nat_div_two_cast_ge_third {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) / 3) ≤ ((n / 2 : ℕ) : ℝ) := by
  have hnat : n ≤ 3 * (n / 2) := by omega
  have hreal : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
  nlinarith

lemma poly_lowerBound_setup (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ ℓ : ℕ in atTop,
      ∃ n : ℕ, ∃ p : ℝ,
        n = Nat.floor ((ℓ : ℝ) ^ ((k : ℝ) / 2 - 1 / 4)) ∧
        p = (ℓ : ℝ) ^ (-(1 - 1 / (2 * (k : ℝ)))) ∧
        0 < p ∧ p < 1 ∧ 0 < n ∧
          ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 +
            ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤ (n : ℝ) / 2 := by
  let α : ℝ := (k : ℝ) / 2 - 1 / 4
  let γ : ℝ := 1 / (2 * (k : ℝ))
  let β : ℝ := 1 - γ
  have hkpos : 0 < k := by omega
  have hαpos : 0 < α := by
    dsimp [α]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hα0 : 0 ≤ α := hαpos.le
  have hγpos : 0 < γ := by
    dsimp [γ]
    positivity
  have hβpos : 0 < β := by
    dsimp [β, γ]
    rw [sub_pos]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hxLargeEv :
      ∀ᶠ ℓ : ℕ in atTop, (4 : ℝ) ≤ (ℓ : ℝ) ^ α :=
    ((tendsto_rpow_atTop hαpos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 4
  have hlogEv := eventually_four_mul_const_log_le_rpow_nat (A := α) (γ := γ) hα0 hγpos
  filter_upwards [hxLargeEv, hlogEv, Filter.eventually_ge_atTop 2] with
    ℓ hxLarge hlog hℓ2
  let n : ℕ := Nat.floor ((ℓ : ℝ) ^ α)
  let p : ℝ := (ℓ : ℝ) ^ (-β)
  have hℓpos : 0 < (ℓ : ℝ) := by positivity
  have hℓnonneg : 0 ≤ (ℓ : ℝ) := hℓpos.le
  have hℓgt1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hp0 : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p < 1 := by
    dsimp [p]
    exact Real.rpow_lt_one_of_one_lt_of_neg hℓgt1 (by linarith)
  have hn_ge_four : 4 ≤ n := by
    dsimp [n]
    exact Nat.le_floor hxLarge
  have hnpos : 0 < n := by omega
  have hn_le_x : (n : ℝ) ≤ (ℓ : ℝ) ^ α := by
    dsimp [n]
    exact Nat.floor_le (Real.rpow_nonneg hℓnonneg _)
  refine ⟨n, p, ?_, ?_, hp0, hp1, hnpos, ?_⟩
  · dsimp [n, α]
  · dsimp [p, β, γ]
  have hterm1_raw :
      ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 ≤
        (ℓ : ℝ) ^ α / (Nat.factorial k : ℝ) := by
    exact poly_clique_term_bound (k := k) (n := n) (ℓ := ℓ) (α := α) (β := β) (p := p)
      hkpos rfl rfl rfl hn_le_x hℓpos
  have hfac_ge_nat : 6 ≤ Nat.factorial k := by
    simpa using (Nat.factorial_le hk : Nat.factorial 3 ≤ Nat.factorial k)
  have hfac_ge : (6 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast hfac_ge_nat
  have hfac_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hx_nonneg : 0 ≤ (ℓ : ℝ) ^ α := Real.rpow_nonneg hℓnonneg _
  have hterm1_to_n :
      (ℓ : ℝ) ^ α / (Nat.factorial k : ℝ) ≤ (n : ℝ) / 4 := by
    have hn_floor : (2 * ((ℓ : ℝ) ^ α)) / 3 ≤ (n : ℝ) := by
      have hsub : (ℓ : ℝ) ^ α - 1 < (n : ℝ) := by
        simpa [n] using Nat.sub_one_lt_floor ((ℓ : ℝ) ^ α)
      nlinarith
    have hx_div_fac_le : (ℓ : ℝ) ^ α / (Nat.factorial k : ℝ) ≤ (ℓ : ℝ) ^ α / 6 := by
      exact div_le_div_of_nonneg_left hx_nonneg (by norm_num : (0 : ℝ) < 6) hfac_ge
    nlinarith
  have hterm1 :
      ((Nat.choose n k : ℕ) : ℝ) * p ^ Nat.choose k 2 ≤ (n : ℝ) / 4 :=
    hterm1_raw.trans hterm1_to_n
  have hterm2_exp :
      ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤
        Real.exp (α * ((ℓ : ℝ) * Real.log (ℓ : ℝ)) - ((ℓ : ℝ) ^ (2 - β)) / 4) := by
    exact poly_indep_term_bound (n := n) (ℓ := ℓ) (α := α) (β := β) (p := p)
      rfl hp0 hp1 hn_le_x hℓ2
  have hpower_mul : (ℓ : ℝ) * (ℓ : ℝ) ^ γ = (ℓ : ℝ) ^ (2 - β) := by
    calc
      (ℓ : ℝ) * (ℓ : ℝ) ^ γ = (ℓ : ℝ) ^ (1 : ℝ) * (ℓ : ℝ) ^ γ := by
        rw [Real.rpow_one]
      _ = (ℓ : ℝ) ^ (1 + γ) := by
        rw [← Real.rpow_add hℓpos]
      _ = (ℓ : ℝ) ^ (2 - β) := by
        congr 1
        dsimp [β, γ]
        ring
  have hlog_scaled :
      4 * (α * ((ℓ : ℝ) * Real.log (ℓ : ℝ))) ≤ (ℓ : ℝ) ^ (2 - β) := by
    calc
      4 * (α * ((ℓ : ℝ) * Real.log (ℓ : ℝ))) =
          (ℓ : ℝ) * (4 * α * Real.log (ℓ : ℝ)) := by ring
      _ ≤ (ℓ : ℝ) * (ℓ : ℝ) ^ γ := by
          exact mul_le_mul_of_nonneg_left hlog hℓnonneg
      _ = (ℓ : ℝ) ^ (2 - β) := hpower_mul
  have harg_nonpos :
      α * ((ℓ : ℝ) * Real.log (ℓ : ℝ)) - ((ℓ : ℝ) ^ (2 - β)) / 4 ≤ 0 := by
    nlinarith
  have hterm2_le_one :
      ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤ 1 :=
    hterm2_exp.trans (Real.exp_le_one_iff.mpr harg_nonpos)
  have hterm2 :
      ((Nat.choose n ℓ : ℕ) : ℝ) * (1 - p) ^ Nat.choose ℓ 2 ≤ (n : ℝ) / 4 := by
    have hn_ge_four_R : (4 : ℝ) ≤ n := by exact_mod_cast hn_ge_four
    nlinarith
  nlinarith

/-- **Lemma 2 (polynomial lower bound).** For each fixed `k ≥ 3`, the
off-diagonal Ramsey number has the eventual lower bound
`R(k, ℓ) ≥ C * ℓ ^ (k / 2 - 1 / 4)`. -/
theorem ramsey_lower_bound_power (k : ℕ) (hk : 3 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ ℓ : ℕ in atTop,
      C * (ℓ : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) ≤ (R(k, ℓ) : ℝ) := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  let α : ℝ := (k : ℝ) / 2 - 1 / 4
  have hαpos : 0 < α := by
    dsimp [α]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hxLargeEv :
      ∀ᶠ ℓ : ℕ in atTop, (4 : ℝ) ≤ (ℓ : ℝ) ^ α :=
    ((tendsto_rpow_atTop hαpos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 4
  filter_upwards [poly_lowerBound_setup k hk, hxLargeEv, Filter.eventually_ge_atTop 2] with
    ℓ hsetup hxLarge hℓ2
  obtain ⟨n, p, hn_def, hp_def, hp0, hp1, hnpos, hV⟩ := hsetup
  have hdel : n / 2 < R(k, ℓ) := by
    exact deletion_ramsey_bound (k := k) (ℓ := ℓ) (n := n) (p := p)
      (by omega) (by omega) hp0 hp1 hnpos hV
  have hn_floor_lower : (2 * ((ℓ : ℝ) ^ α)) / 3 ≤ (n : ℝ) := by
    have hsub : (ℓ : ℝ) ^ α - 1 < (n : ℝ) := by
      simpa [hn_def, α] using Nat.sub_one_lt_floor ((ℓ : ℝ) ^ α)
    nlinarith
  have hn_ge_four : 4 ≤ n := by
    rw [hn_def]
    exact Nat.le_floor (by simpa [α] using hxLarge)
  have hdiv_lower : (1 / 8 : ℝ) * (ℓ : ℝ) ^ α ≤ ((n / 2 : ℕ) : ℝ) := by
    have hthird : (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) :=
      nat_div_two_cast_ge_third (by omega : 2 ≤ n)
    nlinarith
  have hR_from_del : ((n / 2 : ℕ) : ℝ) ≤ (R(k, ℓ) : ℝ) := by
    exact_mod_cast Nat.le_of_lt hdel
  calc
    (1 / 8 : ℝ) * (ℓ : ℝ) ^ ((k : ℝ) / 2 - 1 / 4)
        = (1 / 8 : ℝ) * (ℓ : ℝ) ^ α := by simp [α]
    _ ≤ ((n / 2 : ℕ) : ℝ) := hdiv_lower
    _ ≤ (R(k, ℓ) : ℝ) := hR_from_del


end RamseyRatio
