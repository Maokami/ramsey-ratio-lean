import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card

/-!
# Off-diagonal Ramsey numbers

`ramsey k ℓ` is the smallest `N` such that every `N`-vertex simple graph contains
either a `k`-clique or an independent set of size `ℓ`.

Convention: `ramsey 1 ℓ = 1` and `ramsey k 1 = 1` (a single vertex is both a
`K₁` and an independent set of size 1).
-/

open SimpleGraph

namespace RamseyRatio

/-- `HasRamseyProperty N k ℓ` says every simple graph on `Fin N` contains either
a `k`-clique or an independent set of size `ℓ`. -/
def HasRamseyProperty (N k ℓ : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), (∃ s : Finset (Fin N), G.IsNClique k s) ∨
    (∃ s : Finset (Fin N), G.IsNIndepSet ℓ s)

/-- The off-diagonal Ramsey number `R(k, ℓ)`. -/
noncomputable def ramsey (k ℓ : ℕ) : ℕ :=
  sInf { N : ℕ | HasRamseyProperty N k ℓ }

@[inherit_doc] notation "R(" k ", " ℓ ")" => ramsey k ℓ

private lemma fin_zero_finset_empty (s : Finset (Fin 0)) : s = ∅ :=
  Finset.eq_empty_of_forall_notMem (fun x _ => x.elim0)

/-- Convention `R(1, ℓ) = 1`. -/
theorem ramsey_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : R(1, ℓ) = 1 := by
  have h1 : (1 : ℕ) ∈ {N | HasRamseyProperty N 1 ℓ} := by
    intro G
    refine Or.inl ⟨{(0 : Fin 1)}, ?_, rfl⟩
    intro a _ b _ hab
    exact absurd (Subsingleton.elim a b) hab
  have h0 : (0 : ℕ) ∉ {N | HasRamseyProperty N 1 ℓ} := by
    intro hp
    obtain ⟨s, hs⟩ | ⟨s, hs⟩ := hp (⊥ : SimpleGraph (Fin 0))
    · have := hs.card_eq
      rw [fin_zero_finset_empty s] at this
      simp at this
    · have := hs.card_eq
      rw [fin_zero_finset_empty s] at this
      simp at this
      omega
  apply le_antisymm (Nat.sInf_le h1)
  rw [Nat.one_le_iff_ne_zero]
  intro hR
  rcases Nat.sInf_eq_zero.mp hR with h | h
  · exact h0 h
  · exact (Set.eq_empty_iff_forall_notMem.mp h) 1 h1

/-- Diagonal trivial case `R(2, ℓ) = ℓ`. The proof actually works for any
`ℓ ≥ 0`, but we keep `hℓ : 2 ≤ ℓ` to match the paper's stated regime. -/
theorem ramsey_two (ℓ : ℕ) (_hℓ : 2 ≤ ℓ) : R(2, ℓ) = ℓ := by
  have hmem : (ℓ : ℕ) ∈ {N | HasRamseyProperty N 2 ℓ} := by
    intro G
    by_cases h : ∃ u v : Fin ℓ, G.Adj u v
    · obtain ⟨u, v, huv⟩ := h
      have hne : u ≠ v := huv.ne
      refine Or.inl ⟨{u, v}, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton,
                   Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact huv
        · exact huv.symm
        · exact absurd rfl hab
      · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    · push_neg at h
      refine Or.inr ⟨Finset.univ, ?_, ?_⟩
      · intro a _ b _ _
        exact h a b
      · simp
  have hnot : ∀ N < ℓ, N ∉ {M | HasRamseyProperty M 2 ℓ} := by
    intro N hN hp
    obtain ⟨s, hs⟩ | ⟨s, hs⟩ := hp (⊥ : SimpleGraph (Fin N))
    · rw [isNClique_bot_iff] at hs
      omega
    · have hc : s.card = ℓ := hs.card_eq
      have hle : s.card ≤ N := by
        have := Finset.card_le_univ s
        simpa using this
      omega
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra hlt
  push_neg at hlt
  have hmem' : R(2, ℓ) ∈ {N | HasRamseyProperty N 2 ℓ} := Nat.sInf_mem ⟨ℓ, hmem⟩
  exact hnot _ hlt hmem'

/-- Symmetry: `R(k, ℓ) = R(ℓ, k)` (by complementation). -/
theorem ramsey_symm (k ℓ : ℕ) : R(k, ℓ) = R(ℓ, k) := by
  have hiff : ∀ N, HasRamseyProperty N k ℓ ↔ HasRamseyProperty N ℓ k := by
    intro N
    constructor
    · intro hp G
      rcases hp Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [isNClique_compl] at hs
        exact Or.inr ⟨s, hs⟩
      · rw [isNIndepSet_compl] at hs
        exact Or.inl ⟨s, hs⟩
    · intro hp G
      rcases hp Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [isNClique_compl] at hs
        exact Or.inr ⟨s, hs⟩
      · rw [isNIndepSet_compl] at hs
        exact Or.inl ⟨s, hs⟩
  unfold ramsey
  congr 1
  ext N
  exact hiff N

-- Monotonicity `ramsey_le_ramsey_succ` lives in `RamseyRatio.ErdosSzekeres` because the
-- proof needs the Ramsey set to be nonempty (supplied by the Erdős–Szekeres bound).

/-- Existence of a critical (Ramsey-extremal) graph: a `K_k`-free graph on
`R(k, ℓ + 1) - 1` vertices with independence number `≤ ℓ`. -/
theorem exists_critical_graph (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) :
    ∃ G : SimpleGraph (Fin (R(k, ℓ + 1) - 1)),
      (¬ ∃ s : Finset _, G.IsNClique k s) ∧
      (¬ ∃ s : Finset _, G.IsNIndepSet (ℓ + 1) s) := by
  suffices hnot : ¬ HasRamseyProperty (R(k, ℓ + 1) - 1) k (ℓ + 1) by
    unfold HasRamseyProperty at hnot
    push_neg at hnot
    obtain ⟨G, hc, hi⟩ := hnot
    exact ⟨G, fun ⟨s, hs⟩ => hc s hs, fun ⟨s, hs⟩ => hi s hs⟩
  rcases Nat.eq_zero_or_pos (R(k, ℓ + 1)) with hR | hR
  · rw [hR]
    simp only [Nat.zero_sub]
    intro hp
    obtain ⟨s, hs⟩ | ⟨s, hs⟩ := hp (⊥ : SimpleGraph (Fin 0))
    · have hcard := hs.card_eq
      rw [fin_zero_finset_empty s, Finset.card_empty] at hcard
      omega
    · have hcard := hs.card_eq
      rw [fin_zero_finset_empty s, Finset.card_empty] at hcard
      omega
  · intro hp
    have hle : R(k, ℓ + 1) ≤ R(k, ℓ + 1) - 1 :=
      Nat.sInf_le (show R(k, ℓ + 1) - 1 ∈ {N | HasRamseyProperty N k (ℓ + 1)} from hp)
    omega

end RamseyRatio
