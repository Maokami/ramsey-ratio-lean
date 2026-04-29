import RamseyRatio.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Lemma 1 — Erdős–Szekeres upper bound

`R(k, ℓ) ≤ C(k + ℓ - 2, k - 1)`.

The classical proof is by induction on `k + ℓ` using
`R(k, ℓ) ≤ R(k - 1, ℓ) + R(k, ℓ - 1)`.
-/

open SimpleGraph

namespace RamseyRatio

private lemma hasRamseyProperty_pos {N k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ)
    (h : HasRamseyProperty N k ℓ) : 0 < N := by
  by_contra hN
  have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
  subst N
  rcases h (⊥ : SimpleGraph (Fin 0)) with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hle : s.card ≤ 0 := by
      simpa using Finset.card_le_univ s
    have hcard := hs.card_eq
    omega
  · have hle : s.card ≤ 0 := by
      simpa using Finset.card_le_univ s
    have hcard := hs.card_eq
    omega

lemma isNIndepSet_insert {α : Type*} [DecidableEq α] {G : SimpleGraph α}
    {n : ℕ} {s : Finset α} {a : α} (hs : G.IsNIndepSet n s) (ha : a ∉ s)
    (h : ∀ b ∈ s, ¬ G.Adj a b) : G.IsNIndepSet (n + 1) (insert a s) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact G.loopless _
    · exact h y hy
    · intro hxa
      exact h x hx hxa.symm
    · exact hs.isIndepSet hx hy hxy
  · rw [Finset.card_insert_of_notMem ha, hs.card_eq]

private lemma isNClique_map_comap {α β : Type*} {G : SimpleGraph β} {f : α ↪ β}
    {n : ℕ} {s : Finset α} (h : (G.comap f).IsNClique n s) :
    G.IsNClique n (s.map f) :=
  h.map.mono (SimpleGraph.map_comap_le f G)

private lemma isNIndepSet_map_comap {α β : Type*} {G : SimpleGraph β} {f : α ↪ β}
    {n : ℕ} {s : Finset α} (h : (G.comap f).IsNIndepSet n s) :
    G.IsNIndepSet n (s.map f) := by
  constructor
  · intro x hx y hy hxy hxy'
    rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    have hne : x' ≠ y' := by
      intro hxy''
      exact hxy (by simp [hxy''])
    exact h.isIndepSet hx' hy' hne hxy'
  · rw [Finset.card_map, h.card_eq]

lemma ramseyProperty_of_finset {N M k ℓ : ℕ} (G : SimpleGraph (Fin N))
    {s : Finset (Fin N)} (hs : s.card = M) (hR : HasRamseyProperty M k ℓ) :
    (∃ t : Finset (Fin N), t ⊆ s ∧ G.IsNClique k t) ∨
      (∃ t : Finset (Fin N), t ⊆ s ∧ G.IsNIndepSet ℓ t) := by
  classical
  let e : s ≃ Fin M := s.equivFinOfCardEq hs
  let f : Fin M ↪ Fin N :=
    { toFun := fun i => (e.symm i).1
      inj' := by
        intro i j hij
        exact e.symm.injective (Subtype.ext hij) }
  rcases hR (G.comap f) with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨t.map f, ?_, isNClique_map_comap ht⟩
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    exact (e.symm i).2
  · refine Or.inr ⟨t.map f, ?_, isNIndepSet_map_comap ht⟩
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    exact (e.symm i).2

private lemma hasRamseyProperty_add {a b k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ)
    (ha : HasRamseyProperty a (k - 1) ℓ) (hb : HasRamseyProperty b k (ℓ - 1)) :
    HasRamseyProperty (a + b) k ℓ := by
  classical
  have ha_pos : 0 < a := hasRamseyProperty_pos (by omega) (by omega) ha
  intro G
  let v : Fin (a + b) := ⟨0, Nat.add_pos_left ha_pos b⟩
  let neigh : Finset (Fin (a + b)) := G.neighborFinset v
  let nonneigh : Finset (Fin (a + b)) := (Finset.univ.erase v) \ neigh
  have hneigh_subset : neigh ⊆ Finset.univ.erase v := by
    intro x hx
    rw [Finset.mem_erase]
    have hx' : G.Adj v x := (G.mem_neighborFinset v x).mp hx
    exact ⟨hx'.ne.symm, Finset.mem_univ x⟩
  have hcard_sum : neigh.card + nonneigh.card + 1 = a + b := by
    have hle : neigh.card ≤ (Finset.univ.erase v).card := Finset.card_le_card hneigh_subset
    have hsum : neigh.card + nonneigh.card = (Finset.univ.erase v).card := by
      rw [Finset.card_sdiff_of_subset hneigh_subset]
      omega
    have herase : (Finset.univ.erase v).card = a + b - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    omega
  have hlarge : a ≤ neigh.card ∨ b ≤ nonneigh.card := by
    by_contra h
    push_neg at h
    omega
  rcases hlarge with hlarge | hlarge
  · obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq hlarge
    rcases ramseyProperty_of_finset G hA_card ha with
      ⟨C, hC_sub, hC⟩ | ⟨I, -, hI⟩
    · refine Or.inl ⟨insert v C, ?_⟩
      have hadj : ∀ x ∈ C, G.Adj v x := by
        intro x hx
        exact (G.mem_neighborFinset v x).mp (hA_sub (hC_sub hx))
      have hC' := hC.insert hadj
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      simpa [hk'] using hC'
    · exact Or.inr ⟨I, hI⟩
  · obtain ⟨B, hB_sub, hB_card⟩ := Finset.exists_subset_card_eq hlarge
    rcases ramseyProperty_of_finset G hB_card hb with
      ⟨C, -, hC⟩ | ⟨I, hI_sub, hI⟩
    · exact Or.inl ⟨C, hC⟩
    · refine Or.inr ⟨insert v I, ?_⟩
      have hv_notMem : v ∉ I := by
        intro hv
        have hv' : v ∈ nonneigh := hB_sub (hI_sub hv)
        simp [nonneigh] at hv'
      have hnonadj : ∀ x ∈ I, ¬ G.Adj v x := by
        intro x hx hxadj
        have hx' : x ∈ nonneigh := hB_sub (hI_sub hx)
        exact (Finset.mem_sdiff.mp hx').2 ((G.mem_neighborFinset v x).mpr hxadj)
      have hI' := isNIndepSet_insert hI hv_notMem hnonadj
      have hℓ' : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel (by omega)
      simpa [hℓ'] using hI'

private theorem hasRamseyProperty_choose (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    HasRamseyProperty (Nat.choose (k + ℓ - 2) (k - 1)) k ℓ := by
  classical
  match k, ℓ with
  | 0, _ => omega
  | _, 0 => omega
  | 1, ℓ + 1 =>
      have hN : Nat.choose (1 + (ℓ + 1) - 2) (1 - 1) = 1 := by simp
      rw [hN]
      intro G
      exact Or.inl ⟨{(0 : Fin 1)}, by simp⟩
  | k + 2, 1 =>
      have hN : Nat.choose (k + 2 + 1 - 2) (k + 2 - 1) = 1 := by
        have h₁ : k + 2 + 1 - 2 = k + 1 := by omega
        have h₂ : k + 2 - 1 = k + 1 := by omega
        simp [h₁, h₂]
      rw [hN]
      intro G
      refine Or.inr ⟨{(0 : Fin 1)}, ?_⟩
      simp [SimpleGraph.isNIndepSet_iff]
  | k + 2, ℓ + 2 =>
      let a := Nat.choose (k + ℓ + 1) k
      let b := Nat.choose (k + ℓ + 1) (k + 1)
      have hleft : HasRamseyProperty a (k + 1) (ℓ + 2) := by
        have h₁ : k + 1 + (ℓ + 2) - 2 = k + ℓ + 1 := by omega
        have h₂ : k + 1 - 1 = k := by omega
        simpa [a, h₁, h₂] using
          hasRamseyProperty_choose (k + 1) (ℓ + 2) (by omega) (by omega)
      have hright : HasRamseyProperty b (k + 2) (ℓ + 1) := by
        have h₁ : k + 2 + (ℓ + 1) - 2 = k + ℓ + 1 := by omega
        have h₂ : k + 2 - 1 = k + 1 := by omega
        simpa [b, h₁, h₂] using
          hasRamseyProperty_choose (k + 2) (ℓ + 1) (by omega) (by omega)
      have hleft' : HasRamseyProperty a (k + 2 - 1) (ℓ + 2) := by
        simpa using hleft
      have hright' : HasRamseyProperty b (k + 2) (ℓ + 2 - 1) := by
        simpa using hright
      have hsum : HasRamseyProperty (a + b) (k + 2) (ℓ + 2) :=
        hasRamseyProperty_add (a := a) (b := b) (k := k + 2) (ℓ := ℓ + 2)
          (by omega) (by omega) hleft' hright'
      have hmain₁ : k + 2 + (ℓ + 2) - 2 = k + ℓ + 2 := by omega
      have hmain₂ : k + 2 - 1 = k + 1 := by omega
      have hpascal :
          Nat.choose (k + ℓ + 2) (k + 1) =
            Nat.choose (k + ℓ + 1) k + Nat.choose (k + ℓ + 1) (k + 1) := by
        simpa using Nat.choose_succ_succ' (k + ℓ + 1) k
      simpa [a, b, hmain₁, hmain₂, hpascal] using hsum
termination_by k + ℓ
decreasing_by
  all_goals simp_wf

lemma ramseySet_nonempty (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    ({N : ℕ | HasRamseyProperty N k ℓ} : Set ℕ).Nonempty :=
  ⟨Nat.choose (k + ℓ - 2) (k - 1), hasRamseyProperty_choose k ℓ hk hℓ⟩

lemma ramsey_mem_property (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    HasRamseyProperty R(k, ℓ) k ℓ :=
  Nat.sInf_mem (ramseySet_nonempty k ℓ hk hℓ)

/-- Pascal-style induction step:
`R(k, ℓ) ≤ R(k - 1, ℓ) + R(k, ℓ - 1)`. -/
theorem ramsey_le_pascal (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ) :
    R(k, ℓ) ≤ R(k - 1, ℓ) + R(k, ℓ - 1) := by
  apply Nat.sInf_le
  exact hasRamseyProperty_add (a := R(k - 1, ℓ)) (b := R(k, ℓ - 1))
    (k := k) (ℓ := ℓ) hk hℓ
    (ramsey_mem_property (k - 1) ℓ (by omega) (by omega))
    (ramsey_mem_property k (ℓ - 1) (by omega) (by omega))

/-- **Lemma 1 (Erdős–Szekeres).** For `k, ℓ ≥ 2`,
`R(k, ℓ) ≤ C(k + ℓ - 2, k - 1)`. -/
theorem ramsey_le_choose (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 2 ≤ ℓ) :
    R(k, ℓ) ≤ Nat.choose (k + ℓ - 2) (k - 1) := by
  apply Nat.sInf_le
  exact hasRamseyProperty_choose k ℓ (by omega) (by omega)

/-- For positive `k, ℓ`, `R(k, ℓ) ≥ 1` — the empty graph on `Fin 0` has no
nonempty clique/indep set, so `0` is never in the Ramsey set. -/
theorem one_le_ramsey (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) : 1 ≤ R(k, ℓ) := by
  rw [Nat.one_le_iff_ne_zero]
  intro hR0
  have hmem : HasRamseyProperty 0 k ℓ := hR0 ▸ ramsey_mem_property k ℓ hk hℓ
  obtain ⟨s, hs⟩ | ⟨s, hs⟩ := hmem (⊥ : SimpleGraph (Fin 0))
  all_goals
    have hemp : s = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun x _ => x.elim0)
    have hcard := hs.card_eq
    rw [hemp, Finset.card_empty] at hcard
    omega

/-- Monotonicity in the second argument: `R(k, ℓ) ≤ R(k, ℓ + 1)`.
Needs the Ramsey set to be nonempty, supplied here by Erdős–Szekeres. -/
theorem ramsey_le_ramsey_succ (k ℓ : ℕ) : R(k, ℓ) ≤ R(k, ℓ + 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hR0 : R(0, ℓ) = 0 := by
      apply Nat.sInf_eq_zero.mpr
      refine Or.inl ?_
      intro G
      exact Or.inl ⟨∅, isNClique_empty.mpr rfl⟩
    rw [hR0]
    exact Nat.zero_le _
  · have hmem : HasRamseyProperty R(k, ℓ + 1) k (ℓ + 1) :=
      ramsey_mem_property k (ℓ + 1) hk (by omega)
    apply Nat.sInf_le
    intro G
    rcases hmem G with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨s, hs⟩
    · have hcard : ℓ ≤ s.card := by rw [hs.card_eq]; omega
      obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
      refine Or.inr ⟨t, ?_, htcard⟩
      intro a ha b hb hab
      exact hs.isIndepSet (htsub ha) (htsub hb) hab


/-- Monotonicity in the first argument: `R(k - 1, ℓ) ≤ R(k, ℓ)` for `k ≥ 2`. -/
lemma ramsey_mono_left (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) : R(k - 1, ℓ) ≤ R(k, ℓ) := by
  apply Nat.sInf_le
  have hmem : HasRamseyProperty R(k, ℓ) k ℓ := ramsey_mem_property k ℓ (by omega) hℓ
  intro G
  rcases hmem G with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hcard : k - 1 ≤ s.card := by rw [hs.card_eq]; omega
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
    exact Or.inl ⟨t, ⟨hs.isClique.subset (Finset.coe_subset.mpr htsub), htcard⟩⟩
  · exact Or.inr ⟨s, hs⟩

end RamseyRatio
