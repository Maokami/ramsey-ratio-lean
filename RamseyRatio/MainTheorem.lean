import RamseyRatio.Basic
import RamseyRatio.ErdosSzekeres
import RamseyRatio.LowerBound
import RamseyRatio.DRC
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Main theorem

For every fixed `k ≥ 2`,
  `lim_{ℓ → ∞} R(k, ℓ + 1) / R(k, ℓ) = 1`.

Proof outline (paper §2):
* `k = 2`: `R(2, ℓ) = ℓ`, so the ratio is `(ℓ + 1) / ℓ → 1`.
* `k ≥ 3`: set `s = ⌈k/2⌉`, `t = ⌊k/2⌋`, `q = k²`. Take a critical graph `G` on
  `N = R(k, ℓ + 1) - 1` vertices. From `α(G) ≤ ℓ` we get
    `δ(G) ≥ R(k, ℓ + 1) - R(k, ℓ) - 1`.
  Apply DRC with `m = R(t, ℓ + 1)` to extract `U ⊆ V(G)` with `|U| ≤ R(s, ℓ + 1) - 1`
  (else we get a `K_s` whose common neighbourhood contains a `K_t`, building a `K_k`).
  Combine with the bounds from Lemmas 1 & 2 and take `q`-th roots.
-/

open Filter Topology

namespace RamseyRatio
/-! ### §2. Min-degree estimate on a critical graph (paper eq. (1)) -/

/-- For `k, ℓ ≥ 2`, one vertex is not enough to force either alternative. -/
lemma two_le_ramsey (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ) : 2 ≤ R(k, ℓ) := by
  have hone : 1 ≤ R(k, ℓ) := one_le_ramsey k ℓ (by omega) (by omega)
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Nat.succ_le_iff]
  refine lt_of_le_of_ne hone ?_
  intro hR
  have hR1 : R(k, ℓ) = 1 := hR.symm
  have hmem : HasRamseyProperty 1 k ℓ := hR1 ▸ ramsey_mem_property k ℓ (by omega) (by omega)
  rcases hmem (⊥ : SimpleGraph (Fin 1)) with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hcard := hs.card_eq
    have hle : s.card ≤ 1 := by
      simpa using Finset.card_le_univ s
    omega
  · have hcard := hs.card_eq
    have hle : s.card ≤ 1 := by
      simpa using Finset.card_le_univ s
    omega

set_option maxHeartbeats 400000 in
/-- Min-degree bound on a critical graph (paper eq. (1)). -/
theorem critical_min_degree
    {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ)
    (G : SimpleGraph (Fin (R(k, ℓ + 1) - 1))) [DecidableRel G.Adj]
    (h_no_clique : ¬ ∃ s : Finset _, G.IsNClique k s)
    (h_indep : ¬ ∃ s : Finset _, G.IsNIndepSet (ℓ + 1) s)
    (v : Fin (R(k, ℓ + 1) - 1)) :
    R(k, ℓ + 1) - R(k, ℓ) - 1 ≤ G.degree v := by
  classical
  let A : Finset (Fin (R(k, ℓ + 1) - 1)) :=
    Finset.univ \ insert v (G.neighborFinset v)
  have hv_notin_N : v ∉ G.neighborFinset v := by
    intro h
    exact G.loopless v ((G.mem_neighborFinset v v).mp h)
  have hinsert_card : (insert v (G.neighborFinset v)).card = G.degree v + 1 := by
    rw [Finset.card_insert_of_notMem hv_notin_N]
    rfl
  have hA_card : A.card = (R(k, ℓ + 1) - 1) - (G.degree v + 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hinsert_card]
  by_contra hlt
  push_neg at hlt
  have hA_large : R(k, ℓ) ≤ A.card := by rw [hA_card]; omega
  obtain ⟨A', hA'_sub, hA'_card⟩ := Finset.exists_subset_card_eq hA_large
  have hR : HasRamseyProperty (R(k, ℓ)) k ℓ :=
    ramsey_mem_property k ℓ (by omega) hℓ
  rcases ramseyProperty_of_finset G hA'_card hR with
    ⟨t, _, ht⟩ | ⟨t, ht_sub, ht⟩
  · exact h_no_clique ⟨t, ht⟩
  · apply h_indep
    have hv_notin_t : v ∉ t := by
      intro hv
      have hvA : v ∈ A := hA'_sub (ht_sub hv)
      have : v ∉ insert v (G.neighborFinset v) := (Finset.mem_sdiff.mp hvA).2
      exact this (Finset.mem_insert_self v _)
    have hnonadj : ∀ b ∈ t, ¬ G.Adj v b := by
      intro b hb hadj
      have hbA : b ∈ A := hA'_sub (ht_sub hb)
      have hbnotin : b ∉ insert v (G.neighborFinset v) := (Finset.mem_sdiff.mp hbA).2
      exact hbnotin (Finset.mem_insert_of_mem ((G.mem_neighborFinset v b).mpr hadj))
    exact ⟨insert v t, isNIndepSet_insert ht hv_notin_t hnonadj⟩

end RamseyRatio
