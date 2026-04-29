import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Lemma 3 — Dependent random choice

Standard Fox–Sudakov / Zhao formulation: in any `N`-vertex graph of average
degree `d`, for positive integers `q, s, m`, there is `U ⊆ V(G)` such that every
`s`-subset of `U` has at least `m` common neighbours and

  `|U| ≥ d^q / N^(q-1) - C(N, s) · ((m - 1) / N)^q`.

The proof samples a uniformly random `q`-tuple of vertices and lets `U` be the
intersection of their neighbourhoods.
-/

open SimpleGraph Finset

namespace RamseyRatio

/-! ### §1. Common neighborhoods (Set and Finset views) -/

/-- Common neighbourhood of a set of vertices. -/
def commonNeighbors {V : Type*} (G : SimpleGraph V) (s : Finset V) : Set V :=
  { w | ∀ v ∈ s, G.Adj v w }

private def commonNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset V :=
  Finset.univ.filter fun w => ∀ v ∈ s, G.Adj v w

private lemma commonNeighbors_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    (commonNeighbors G s).ncard = (commonNeighborFinset G s).card := by
  rw [Set.ncard_eq_toFinset_card (commonNeighbors G s)]
  congr 1
  ext w
  simp [commonNeighbors, commonNeighborFinset]

/-! ### §2. Counting helpers — q-tuples, double sums, greedy deletion -/

private lemma exists_subset_avoiding
    {α : Type*} [DecidableEq α] (A : Finset α) (bad : Finset (Finset α))
    (hbad_sub : ∀ T ∈ bad, T ⊆ A)
    (hbad_nonempty : ∀ T ∈ bad, T.Nonempty) :
    ∃ U : Finset α,
      U ⊆ A ∧
      (∀ T ∈ bad, ¬ T ⊆ U) ∧
      (A.card : ℝ) - (bad.card : ℝ) ≤ (U.card : ℝ) := by
  classical
  let pick : (T : Finset α) → T ∈ bad → α :=
    fun T hT => Classical.choose (hbad_nonempty T hT)
  let D : Finset α := bad.attach.image fun T => pick T.1 T.2
  refine ⟨A \ D, sdiff_subset, ?_, ?_⟩
  · intro T hT hTU
    have hpick_mem : pick T hT ∈ T :=
      Classical.choose_spec (hbad_nonempty T hT)
    have hpick_D : pick T hT ∈ D := by
      refine mem_image.mpr ?_
      exact ⟨⟨T, hT⟩, mem_attach _ _, rfl⟩
    exact (mem_sdiff.mp (hTU hpick_mem)).2 hpick_D
  · have hDsubA : D ⊆ A := by
      intro x hx
      rcases mem_image.mp hx with ⟨T, -, rfl⟩
      exact hbad_sub T.1 T.2 (Classical.choose_spec (hbad_nonempty T.1 T.2))
    have hDcard_le_bad : D.card ≤ bad.card := by
      calc
        D.card ≤ bad.attach.card := card_image_le
        _ = bad.card := card_attach
    have hDcard_le_A : D.card ≤ A.card := card_le_card hDsubA
    rw [card_sdiff_of_subset hDsubA]
    rw [Nat.cast_sub hDcard_le_A]
    exact sub_le_sub_left (Nat.cast_le.mpr hDcard_le_bad) _

private lemma card_fun_filter_mem {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (q : ℕ) :
    ((Finset.univ : Finset (Fin q → β)).filter fun f => ∀ i, f i ∈ S).card =
      S.card ^ q := by
  classical
  let e : {f : Fin q → β // ∀ i, f i ∈ S} ≃ (Fin q → S) := {
    toFun f := fun i => ⟨f.1 i, f.2 i⟩
    invFun f := ⟨fun i => f i, fun i => (f i).2⟩
    left_inv f := by
      ext i
      rfl
    right_inv f := by
      ext i
      rfl
  }
  calc
    ((Finset.univ : Finset (Fin q → β)).filter fun f => ∀ i, f i ∈ S).card =
        Fintype.card {f : Fin q → β // ∀ i, f i ∈ S} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (Fin q → S) := Fintype.card_congr e
    _ = Fintype.card S ^ Fintype.card (Fin q) := Fintype.card_fun
    _ = S.card ^ q := by simp [Fintype.card_coe]

private lemma sum_card_tuple_commonNeighborhood
    {N q : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    (∑ X : Fin q → Fin N,
        (Finset.univ.filter fun w : Fin N => ∀ i, G.Adj (X i) w).card) =
      ∑ w : Fin N, G.degree w ^ q := by
  classical
  calc
    (∑ X : Fin q → Fin N,
        (Finset.univ.filter fun w : Fin N => ∀ i, G.Adj (X i) w).card) =
        ∑ X : Fin q → Fin N, ∑ w : Fin N, if (∀ i, G.Adj (X i) w) then 1 else 0 := by
      congr with X
      rw [Finset.card_filter]
    _ = ∑ w : Fin N, ∑ X : Fin q → Fin N, if (∀ i, G.Adj (X i) w) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ w : Fin N, G.degree w ^ q := by
      congr with w
      calc
        (∑ X : Fin q → Fin N, if (∀ i, G.Adj (X i) w) then 1 else 0) =
            ((Finset.univ : Finset (Fin q → Fin N)).filter
              fun X => ∀ i, X i ∈ G.neighborFinset w).card := by
          rw [Finset.card_filter]
          simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
        _ = (G.neighborFinset w).card ^ q := card_fun_filter_mem (G.neighborFinset w) q
        _ = G.degree w ^ q := by rw [SimpleGraph.card_neighborFinset_eq_degree]

private lemma sum_bad_tuple_sets_le
    {N q s m : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    (∑ X : Fin q → Fin N,
        (((Finset.univ : Finset (Fin N)).powersetCard s).filter fun T =>
          T ⊆ (Finset.univ.filter fun w : Fin N => ∀ i, G.Adj (X i) w) ∧
            (commonNeighborFinset G T).card < m).card) ≤
      Nat.choose N s * (m - 1) ^ q := by
  classical
  let allS : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard s
  let UX : (Fin q → Fin N) → Finset (Fin N) :=
    fun X => Finset.univ.filter fun w : Fin N => ∀ i, G.Adj (X i) w
  calc
    (∑ X : Fin q → Fin N,
        (allS.filter fun T => T ⊆ UX X ∧ (commonNeighborFinset G T).card < m).card) =
        ∑ X : Fin q → Fin N,
          allS.sum fun T => if T ⊆ UX X ∧ (commonNeighborFinset G T).card < m then 1 else 0 := by
      congr with X
      rw [Finset.card_filter]
    _ = allS.sum fun T =>
        ∑ X : Fin q → Fin N, if T ⊆ UX X ∧ (commonNeighborFinset G T).card < m then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ allS.sum fun _T => (m - 1) ^ q := by
      refine sum_le_sum ?_
      intro T hT
      by_cases hsmall : (commonNeighborFinset G T).card < m
      · have hinner :
            (∑ X : Fin q → Fin N,
                if T ⊆ UX X ∧ (commonNeighborFinset G T).card < m then 1 else 0) =
              ((Finset.univ : Finset (Fin q → Fin N)).filter fun X => T ⊆ UX X).card := by
          rw [Finset.card_filter]
          simp [hsmall]
        have hsubset :
            ((Finset.univ : Finset (Fin q → Fin N)).filter fun X => T ⊆ UX X) ⊆
              ((Finset.univ : Finset (Fin q → Fin N)).filter
                fun X => ∀ i, X i ∈ commonNeighborFinset G T) := by
          intro X hX
          rw [mem_filter] at hX ⊢
          constructor
          · simp
          · intro i
            simp [commonNeighborFinset]
            intro v hvT
            have hvUX : v ∈ UX X := hX.2 hvT
            have hAdj : G.Adj (X i) v := by
              simpa [UX] using (mem_filter.mp hvUX).2 i
            simpa [SimpleGraph.adj_comm] using hAdj
        have hcard_le :
            ((Finset.univ : Finset (Fin q → Fin N)).filter fun X => T ⊆ UX X).card ≤
              (commonNeighborFinset G T).card ^ q := by
          calc
            ((Finset.univ : Finset (Fin q → Fin N)).filter fun X => T ⊆ UX X).card ≤
                ((Finset.univ : Finset (Fin q → Fin N)).filter
                  fun X => ∀ i, X i ∈ commonNeighborFinset G T).card :=
              card_le_card hsubset
            _ = (commonNeighborFinset G T).card ^ q :=
              card_fun_filter_mem (commonNeighborFinset G T) q
        have hle_pred : (commonNeighborFinset G T).card ≤ m - 1 :=
          Nat.le_pred_of_lt hsmall
        calc
          (∑ X : Fin q → Fin N,
              if T ⊆ UX X ∧ (commonNeighborFinset G T).card < m then 1 else 0) =
              ((Finset.univ : Finset (Fin q → Fin N)).filter fun X => T ⊆ UX X).card := hinner
          _ ≤ (commonNeighborFinset G T).card ^ q := hcard_le
          _ ≤ (m - 1) ^ q := pow_le_pow_left' hle_pred q
      · simp [hsmall]
    _ = Nat.choose N s * (m - 1) ^ q := by
      simp [allS]

private lemma degree_pow_sum_lower
    {N q : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (d : ℝ) (hd : (∑ v : Fin N, (G.degree v : ℝ)) = N * d)
    (hN : 0 < N) (hq : 0 < q) :
    (N : ℝ) * d ^ q ≤ ∑ v : Fin N, (G.degree v : ℝ) ^ q := by
  classical
  have hpow :
      (∑ v : Fin N, (G.degree v : ℝ)) ^ q / (N : ℝ) ^ (q - 1) ≤
        ∑ v : Fin N, (G.degree v : ℝ) ^ q := by
    have hnonneg :
        ∀ v ∈ (Finset.univ : Finset (Fin N)), 0 ≤ (G.degree v : ℝ) := by
      intro v hv
      positivity
    have hpm :=
      pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin N)))
        (f := fun v : Fin N => (G.degree v : ℝ)) hnonneg (q - 1)
    have hqpred : q - 1 + 1 = q := by omega
    simpa [hqpred] using hpm
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hrewrite :
      (∑ v : Fin N, (G.degree v : ℝ)) ^ q / (N : ℝ) ^ (q - 1) =
        (N : ℝ) * d ^ q := by
    rw [hd]
    have hqeq : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hq).symm
    rw [hqeq, mul_pow]
    field_simp [hNne]
    have hpowexp : q - 1 + 1 - 1 = q - 1 := by omega
    rw [hpowexp, pow_succ (N : ℝ) (q - 1), pow_succ d (q - 1)]
    ring
  rwa [hrewrite] at hpow

private lemma exists_ge_of_card_mul_le_sum
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) {r : ℝ}
    (h : (Fintype.card α : ℝ) * r ≤ ∑ x, f x) :
    ∃ x, r ≤ f x := by
  classical
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  have hsum_le : (∑ y, f y) ≤ (Fintype.card α : ℝ) * f x := by
    calc
      (∑ y, f y) ≤ ∑ _y : α, f x := by
        refine sum_le_sum ?_
        intro y hy
        exact hmax y (mem_univ y)
      _ = (Fintype.card α : ℝ) * f x := by simp [mul_comm]
  have hcard_pos : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  nlinarith

/-! ### §3. The dependent-random-choice bound -/

/-- **Lemma 3 (Dependent random choice).** -/
theorem dependent_random_choice
    {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (d : ℝ) (hd : (∑ v : Fin N, (G.degree v : ℝ)) = N * d)
    (q s m : ℕ) (hN : 0 < N) (hq : 0 < q) (hs : 0 < s) (hm : 0 < m) :
    ∃ U : Finset (Fin N),
      (∀ T : Finset (Fin N), T ⊆ U → T.card = s →
        m ≤ (commonNeighbors G T).ncard) ∧
      (d ^ q / (N : ℝ) ^ (q - 1) -
        (Nat.choose N s : ℝ) * ((m - 1 : ℝ) / N) ^ q ≤ (U.card : ℝ)) := by
  classical
  let allS : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard s
  let UX : (Fin q → Fin N) → Finset (Fin N) :=
    fun X => Finset.univ.filter fun w : Fin N => ∀ i, G.Adj (X i) w
  let bad : (Fin q → Fin N) → Finset (Finset (Fin N)) :=
    fun X => allS.filter fun T => T ⊆ UX X ∧ (commonNeighborFinset G T).card < m
  let R : ℝ :=
    d ^ q / (N : ℝ) ^ (q - 1) -
      (Nat.choose N s : ℝ) * ((m - 1 : ℝ) / N) ^ q
  have hUXsum :
      (∑ X : Fin q → Fin N, ((UX X).card : ℝ)) =
        ∑ w : Fin N, (G.degree w : ℝ) ^ q := by
    exact_mod_cast (sum_card_tuple_commonNeighborhood (N := N) (q := q) G)
  have hUXlower :
      (N : ℝ) * d ^ q ≤ ∑ X : Fin q → Fin N, ((UX X).card : ℝ) := by
    rw [hUXsum]
    exact degree_pow_sum_lower G d hd hN hq
  have hbadNat :
      (∑ X : Fin q → Fin N, (bad X).card) ≤ Nat.choose N s * (m - 1) ^ q := by
    simpa [bad, allS, UX] using
      (sum_bad_tuple_sets_le (N := N) (q := q) (s := s) (m := m) G)
  have hmCast : ((m - 1 : ℕ) : ℝ) = (m - 1 : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hbadUpper :
      (∑ X : Fin q → Fin N, ((bad X).card : ℝ)) ≤
        (Nat.choose N s : ℝ) * (m - 1 : ℝ) ^ q := by
    have hbadUpperNat :
        (∑ X : Fin q → Fin N, ((bad X).card : ℝ)) ≤
          (Nat.choose N s : ℝ) * (((m - 1 : ℕ) : ℝ) ^ q) := by
      exact_mod_cast hbadNat
    simpa [hmCast] using hbadUpperNat
  have hsumLower :
      (N : ℝ) * d ^ q - (Nat.choose N s : ℝ) * (m - 1 : ℝ) ^ q ≤
        ∑ X : Fin q → Fin N, (((UX X).card : ℝ) - ((bad X).card : ℝ)) := by
    rw [sum_sub_distrib]
    nlinarith
  have hcardTuples : Fintype.card (Fin q → Fin N) = N ^ q := by
    rw [Fintype.card_fun]
    simp
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hscale :
      ((N : ℝ) ^ q) * R =
        (N : ℝ) * d ^ q - (Nat.choose N s : ℝ) * (m - 1 : ℝ) ^ q := by
    dsimp [R]
    rw [mul_sub]
    have hqeq : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hq).symm
    have hfirst :
        (N : ℝ) ^ q * (d ^ q / (N : ℝ) ^ (q - 1)) = (N : ℝ) * d ^ q := by
      rw [hqeq, pow_succ (N : ℝ) (q - 1)]
      field_simp [hNne]
      have hpowexp : q - 1 + 1 - 1 = q - 1 := by omega
      rw [hpowexp]
      ring
    have hsecond :
        (N : ℝ) ^ q * ((Nat.choose N s : ℝ) * ((m - 1 : ℝ) / N) ^ q) =
          (Nat.choose N s : ℝ) * (m - 1 : ℝ) ^ q := by
      rw [div_pow]
      field_simp [hNne]
    rw [hfirst, hsecond]
  have haverage :
      (Fintype.card (Fin q → Fin N) : ℝ) * R ≤
        ∑ X : Fin q → Fin N, (((UX X).card : ℝ) - ((bad X).card : ℝ)) := by
    rw [hcardTuples]
    simp only [Nat.cast_pow]
    rw [hscale]
    exact hsumLower
  letI : Nonempty (Fin q → Fin N) := ⟨fun _ => ⟨0, hN⟩⟩
  obtain ⟨X, hX⟩ :=
    exists_ge_of_card_mul_le_sum
      (α := Fin q → Fin N)
      (fun X => ((UX X).card : ℝ) - ((bad X).card : ℝ))
      (r := R) haverage
  have hbad_sub : ∀ T ∈ bad X, T ⊆ UX X := by
    intro T hT
    exact (mem_filter.mp hT).2.1
  have hbad_nonempty : ∀ T ∈ bad X, T.Nonempty := by
    intro T hT
    have hTcard : T.card = s := (mem_powersetCard.mp (mem_filter.mp hT).1).2
    exact card_pos.mp (by rw [hTcard]; exact hs)
  obtain ⟨U, hUsub, hAvoid, hUsize⟩ :=
    exists_subset_avoiding (UX X) (bad X) hbad_sub hbad_nonempty
  refine ⟨U, ?_, ?_⟩
  · intro T hTU hTcard
    by_contra hnot
    have hsmallSet : (commonNeighbors G T).ncard < m := Nat.lt_of_not_ge hnot
    have hsmallFin : (commonNeighborFinset G T).card < m := by
      rwa [commonNeighbors_ncard] at hsmallSet
    have hTUX : T ⊆ UX X := Subset.trans hTU hUsub
    have hTall : T ∈ allS := by
      rw [mem_powersetCard]
      exact ⟨by intro v hv; simp, hTcard⟩
    have hTbad : T ∈ bad X := by
      rw [mem_filter]
      exact ⟨hTall, hTUX, hsmallFin⟩
    exact hAvoid T hTbad hTU
  · exact le_trans hX hUsize

end RamseyRatio
