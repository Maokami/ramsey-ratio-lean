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

/-! ### §1. Real-arithmetic helpers (eventually-true rpow inequalities) -/

private lemma eventually_const_mul_rpow_le_rpow
    {A a b : ℝ} (_hA : 0 ≤ A) (hab : b < a) :
    ∀ᶠ ℓ : ℕ in atTop, A * (ℓ : ℝ) ^ (-a) ≤ (ℓ : ℝ) ^ (-b) := by
  have hε : 0 < a - b := sub_pos.mpr hab
  have htend : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [htend.eventually_ge_atTop A, Filter.eventually_ge_atTop 1] with ℓ hA_le hℓ
  have hx1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hx0 : 0 < (ℓ : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  calc
    A * (ℓ : ℝ) ^ (-a) ≤ (ℓ : ℝ) ^ (a - b) * (ℓ : ℝ) ^ (-a) := by
      exact mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg hx0.le _)
    _ = (ℓ : ℝ) ^ (-b) := by
      rw [← Real.rpow_add hx0]
      ring_nf

private lemma eventually_const_mul_rpow_le_const_mul_rpow
    {A B a b : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hab : b < a) :
    ∀ᶠ ℓ : ℕ in atTop, A * (ℓ : ℝ) ^ (-a) ≤ B * (ℓ : ℝ) ^ (-b) := by
  have hAB : 0 ≤ A / B := div_nonneg hA hB.le
  filter_upwards [eventually_const_mul_rpow_le_rpow hAB hab] with ℓ hℓ
  calc
    A * (ℓ : ℝ) ^ (-a) = B * ((A / B) * (ℓ : ℝ) ^ (-a)) := by
      field_simp [hB.ne']
    _ ≤ B * (ℓ : ℝ) ^ (-b) :=
      mul_le_mul_of_nonneg_left hℓ hB.le

private lemma half_nat_cast_le_sub_one_cast {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) * (n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hsub]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

private lemma ramsey_sub_one_le_two_mul_rpow (a ℓ : ℕ) (ha : 1 ≤ a) (hℓ : a ≤ ℓ) :
    ((R(a, ℓ + 1) - 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (a - 1) * (ℓ : ℝ) ^ ((a - 1 : ℕ) : ℝ) := by
  have hpowNat : R(a, ℓ + 1) - 1 ≤ (2 * ℓ) ^ (a - 1) := by
    by_cases ha1 : a = 1
    · subst a
      rw [ramsey_one (ℓ + 1) (by omega : 1 ≤ ℓ + 1)]
      simp
    · have ha2 : 2 ≤ a := by omega
      have hRle : R(a, ℓ + 1) ≤ Nat.choose (a + (ℓ + 1) - 2) (a - 1) :=
        ramsey_le_choose a (ℓ + 1) ha2 (by omega)
      have hchoose_le :
          Nat.choose (a + (ℓ + 1) - 2) (a - 1) ≤
            (a + (ℓ + 1) - 2) ^ (a - 1) :=
        Nat.choose_le_pow _ _
      have hbase_le : a + (ℓ + 1) - 2 ≤ 2 * ℓ := by omega
      have hpow_le :
          (a + (ℓ + 1) - 2) ^ (a - 1) ≤ (2 * ℓ) ^ (a - 1) :=
        Nat.pow_le_pow_left hbase_le _
      omega
  have hcast :
      ((R(a, ℓ + 1) - 1 : ℕ) : ℝ) ≤ (((2 * ℓ) ^ (a - 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  calc
    ((R(a, ℓ + 1) - 1 : ℕ) : ℝ) ≤ (((2 * ℓ) ^ (a - 1) : ℕ) : ℝ) := hcast
    _ = (2 : ℝ) ^ (a - 1) * (ℓ : ℝ) ^ ((a - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_mul, mul_pow, Real.rpow_natCast]
      norm_num

private lemma model_second_term_eq {N B : ℝ} {s q : ℕ} (hN : 0 < N) (hB : 0 ≤ B) :
    N ^ s * (B / N) ^ q / N = B ^ q * N ^ ((s : ℝ) - (q : ℝ) - 1) := by
  rw [← Real.rpow_natCast N s, ← Real.rpow_natCast (B / N) q]
  rw [Real.div_rpow hB hN.le]
  rw [Real.rpow_sub hN]
  rw [Real.rpow_sub hN]
  rw [Real.rpow_natCast B q, Real.rpow_one]
  field_simp [hN.ne']

private lemma second_term_const_eq {x C δ z : ℝ} {t q : ℕ} (hx : 0 < x) (hC : 0 < C) :
    (((2 : ℝ) ^ (t - 1) * x ^ ((t - 1 : ℕ) : ℝ)) ^ q) *
        ((C / 2) * x ^ δ) ^ z =
      (((2 : ℝ) ^ (t - 1)) ^ q * (C / 2) ^ z) *
        x ^ (((t - 1 : ℕ) : ℝ) * (q : ℝ) + δ * z) := by
  rw [mul_pow]
  rw [Real.mul_rpow (by positivity : 0 ≤ C / 2) (Real.rpow_nonneg hx.le δ)]
  rw [← Real.rpow_natCast (x ^ ((t - 1 : ℕ) : ℝ)) q]
  rw [← Real.rpow_mul hx.le]
  rw [← Real.rpow_mul hx.le]
  calc
    ((2 : ℝ) ^ (t - 1)) ^ q * x ^ (((t - 1 : ℕ) : ℝ) * (q : ℝ)) *
        ((C / 2) ^ z * x ^ (δ * z))
        = (((2 : ℝ) ^ (t - 1)) ^ q * (C / 2) ^ z) *
            (x ^ (((t - 1 : ℕ) : ℝ) * (q : ℝ)) * x ^ (δ * z)) := by
          ring
    _ = (((2 : ℝ) ^ (t - 1)) ^ q * (C / 2) ^ z) *
        x ^ (((t - 1 : ℕ) : ℝ) * (q : ℝ) + δ * z) := by
          rw [← Real.rpow_add hx]

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

/-! ### §3. The DRC asymptotic estimate (paper eq. (3) and the q-th root step) -/

set_option maxHeartbeats 800000 in
/-- DRC estimate for the nontrivial branch of the main theorem.

This is the paper's quantitative argument after fixing `k ≥ 3`: combine the
probabilistic lower bound for `R(k, ℓ)`, a critical graph on
`R(k, ℓ + 1) - 1` vertices, the min-degree estimate above, and dependent random
choice with `s = ⌈k / 2⌉`, `t = ⌊k / 2⌋`, and `q = k²`. -/
theorem ramsey_ratio_drc_estimate (k : ℕ) (hk : 3 ≤ k) :
    ∃ c > (0 : ℝ), ∀ᶠ ℓ : ℕ in atTop,
      (R(k, ℓ + 1) : ℝ) / R(k, ℓ) ≤ 1 + (ℓ : ℝ) ^ (-c) := by
  classical
  -- Step 1: Obtain the polynomial lower bound, plus the simple linear consequence
  -- used by the current proof skeleton below.
  obtain ⟨C_lb, hC_lb, hLBpoly⟩ := ramsey_lower_bound_power k hk
  -- Let N = R(k,ℓ+1)-1, s = ⌈k/2⌉, t = ⌊k/2⌋, q = k², and
  -- δ = k/2 - 1/4.
  let s := (k + 1) / 2
  let t := k / 2
  let q := k ^ 2
  let δ : ℝ := (k : ℝ) / 2 - 1 / 4
  let c : ℝ := 1 / (8 * (k : ℝ) ^ 2)
  let A₁ : ℝ := ((2 : ℝ) ^ (s - 1)) / (C_lb / 2)
  let A₂ : ℝ := ((2 : ℝ) ^ (t - 1)) ^ q * (C_lb / 2) ^ ((s : ℝ) - (q : ℝ) - 1)
  let A : ℝ := A₁ + A₂
  have hq_pos₀ : 0 < q := by
    dsimp [q]
    exact pow_pos (by omega : 0 < k) 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcq : c * (q : ℝ) = 1 / 8 := by
    have hq_cast : (q : ℝ) = (k : ℝ) ^ 2 := by
      dsimp [q]
      norm_num [Nat.cast_pow]
    have hk_ne : (k : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hq_cast]
    dsimp [c]
    field_simp [hk_ne]
  have hc_lt_one : c < 1 := by
    dsimp [c]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hden_gt : (1 : ℝ) < 8 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) - 3)]
    simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, A₁, A₂]
    positivity
  have hLBpoly_succ :
      ∀ᶠ ℓ : ℕ in atTop,
        C_lb * ((ℓ + 1 : ℕ) : ℝ) ^ δ ≤ (R(k, ℓ + 1) : ℝ) := by
    simpa [δ, Function.comp_def] using (tendsto_add_atTop_nat 1).eventually hLBpoly
  have hSmallPow :
      ∀ᶠ ℓ : ℕ in atTop,
        A * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) ≤
          ((1 / 8 : ℝ) * (ℓ : ℝ) ^ (-c)) ^ q := by
    have hbase :=
      eventually_const_mul_rpow_le_const_mul_rpow
        (A := A) (B := (1 / 8 : ℝ) ^ q) hA_nonneg (by positivity)
        (show (1 / 8 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [hbase, Filter.eventually_ge_atTop 1] with ℓ hℓ hℓ_ge
    have hx1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_ge
    have hx0 : 0 ≤ (ℓ : ℝ) := by positivity
    have hpow :
        ((ℓ : ℝ) ^ (-c)) ^ q = (ℓ : ℝ) ^ (-(1 / 8 : ℝ)) := by
      rw [← Real.rpow_mul_natCast hx0]
      congr 1
      nlinarith [hcq]
    calc
      A * (ℓ : ℝ) ^ (-(1 / 4 : ℝ))
          ≤ (1 / 8 : ℝ) ^ q * (ℓ : ℝ) ^ (-(1 / 8 : ℝ)) := hℓ
      _ = ((1 / 8 : ℝ) * (ℓ : ℝ) ^ (-c)) ^ q := by
        rw [mul_pow, hpow]
  have hInvSmall :
      ∀ᶠ ℓ : ℕ in atTop,
        (ℓ : ℝ) ^ (-(1 : ℝ)) ≤ (1 / 8 : ℝ) * (ℓ : ℝ) ^ (-c) := by
    simpa [one_mul] using
      eventually_const_mul_rpow_le_const_mul_rpow
        (A := (1 : ℝ)) (B := (1 / 8 : ℝ)) (by norm_num) (by norm_num) hc_lt_one
  -- Step 2: The DRC-based ratio bound.
  refine ⟨1 / (8 * (k : ℝ) ^ 2), by positivity, ?_⟩
  change ∀ᶠ ℓ : ℕ in atTop, (R(k, ℓ + 1) : ℝ) / R(k, ℓ) ≤ 1 + (ℓ : ℝ) ^ (-c)
  filter_upwards
      [hLBpoly, hLBpoly_succ, ramsey_lower_bound k hk, Filter.eventually_ge_atTop (k + 2),
        hSmallPow, hInvSmall]
    with ℓ hLBpolyℓ hLBpolySuccℓ hLBℓ hℓk hSmallPowℓ hInvSmallℓ
  -- Basic setup.
  have hℓ2 : 2 ≤ ℓ := by omega
  have hRkℓ_pos : (0 : ℝ) < (R(k, ℓ) : ℝ) :=
    Nat.cast_pos.mpr (one_le_ramsey k ℓ (by omega) (by omega))
  have hRkℓ1_pos : (0 : ℝ) < (R(k, ℓ + 1) : ℝ) :=
    Nat.cast_pos.mpr (one_le_ramsey k (ℓ + 1) (by omega) (by omega))
  have hRkℓ1_ge_Rkℓ : R(k, ℓ) ≤ R(k, ℓ + 1) := ramsey_le_ramsey_succ k ℓ
  have hRkℓ_lb : (ℓ : ℝ) ≤ (R(k, ℓ) : ℝ) := hLBℓ
  have hRkℓ_poly :
      C_lb * (ℓ : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) ≤ (R(k, ℓ) : ℝ) := hLBpolyℓ
  have hs_pos : 0 < s := by
    dsimp [s]
    omega
  have ht_pos : 0 < t := by
    dsimp [t]
    omega
  have hq_pos : 0 < q := by
    exact hq_pos₀
  have ht_one : 1 ≤ t := ht_pos
  have hN_pos : 0 < R(k, ℓ + 1) - 1 := by
    have htwo : 2 ≤ R(k, ℓ + 1) := two_le_ramsey k (ℓ + 1) (by omega) (by omega)
    omega
  have hm_pos : 0 < R(t, ℓ + 1) :=
    one_le_ramsey t (ℓ + 1) ht_one (by omega)
  obtain ⟨G, h_no_clique, h_indep⟩ := exists_critical_graph k ℓ (by omega) (by omega)
  have hdeg :
      ∀ v : Fin (R(k, ℓ + 1) - 1),
        R(k, ℓ + 1) - R(k, ℓ) - 1 ≤ G.degree v := by
    intro v
    exact critical_min_degree (k := k) (ℓ := ℓ) (by omega) (by omega)
      G h_no_clique h_indep v
  let d : ℝ :=
    (∑ v : Fin (R(k, ℓ + 1) - 1), (G.degree v : ℝ)) /
      ((R(k, ℓ + 1) - 1 : ℕ) : ℝ)
  have hd :
      (∑ v : Fin (R(k, ℓ + 1) - 1), (G.degree v : ℝ)) =
        ((R(k, ℓ + 1) - 1 : ℕ) : ℝ) * d := by
    dsimp [d]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN_pos.ne')).symm
  obtain ⟨U, hU_common, hU_size⟩ :=
    dependent_random_choice (N := R(k, ℓ + 1) - 1) G d hd q s (R(t, ℓ + 1))
      hN_pos hq_pos hs_pos hm_pos
  -- critical_min_degree gives: every vertex of the critical graph G has
  --   degree ≥ R(k,ℓ+1)-R(k,ℓ)-1.
  -- Applying DRC with m = R(t,ℓ+1) bounds this normalized degree increment.
  -- Combining that bound with Erdős-Szekeres and `hRkℓ_lb` gives the displayed
  -- ratio estimate.
  have hU_card_le : U.card ≤ R(s, ℓ + 1) - 1 := by
    by_contra hnot
    push_neg at hnot
    have hU_large : R(s, ℓ + 1) ≤ U.card := by
      have hRs_pos : 0 < R(s, ℓ + 1) :=
        one_le_ramsey s (ℓ + 1) (by omega) (by omega)
      omega
    obtain ⟨U', hU'_sub, hU'_card⟩ := Finset.exists_subset_card_eq hU_large
    have hRs : HasRamseyProperty R(s, ℓ + 1) s (ℓ + 1) :=
      ramsey_mem_property s (ℓ + 1) (by omega) (by omega)
    rcases ramseyProperty_of_finset G hU'_card hRs with
      ⟨C, hC_subU', hC⟩ | ⟨I, -, hI⟩
    · have hC_subU : C ⊆ U := fun x hx => hU'_sub (hC_subU' hx)
      have hCN_large : R(t, ℓ + 1) ≤ (commonNeighbors G C).ncard :=
        hU_common C hC_subU hC.card_eq
      let W : Finset (Fin (R(k, ℓ + 1) - 1)) :=
        (Set.toFinite (commonNeighbors G C)).toFinset
      have hW_card : W.card = (commonNeighbors G C).ncard := by
        dsimp [W]
        rw [Set.ncard_eq_toFinset_card]
      have hCN_large_W : R(t, ℓ + 1) ≤ W.card := by
        rwa [hW_card]
      obtain ⟨W', hW'_sub, hW'_card⟩ := Finset.exists_subset_card_eq hCN_large_W
      have hRt : HasRamseyProperty R(t, ℓ + 1) t (ℓ + 1) :=
        ramsey_mem_property t (ℓ + 1) ht_one (by omega)
      rcases ramseyProperty_of_finset G hW'_card hRt with
        ⟨Kt, hKt_subW', hKt⟩ | ⟨I, -, hI⟩
      · have hKt_common : ∀ ⦃x⦄, x ∈ Kt → x ∈ commonNeighbors G C := by
          intro x hx
          have hxW : x ∈ W := hW'_sub (hKt_subW' hx)
          simpa [W] using hxW
        have hdisj : Disjoint C Kt := by
          rw [Finset.disjoint_left]
          intro x hxC hxKt
          exact G.loopless x ((hKt_common hxKt) x hxC)
        have hclique_union : G.IsClique (↑(C ∪ Kt) : Set _) := by
          rw [Finset.coe_union]
          intro x hx y hy hxy
          simp only [Set.mem_union] at hx hy
          rcases hx with hxC | hxKt <;> rcases hy with hyC | hyKt
          · exact hC.isClique hxC hyC hxy
          · exact (hKt_common hyKt) x hxC
          · exact ((hKt_common hxKt) y hyC).symm
          · exact hKt.isClique hxKt hyKt hxy
        have hst : s + t = k := by
          dsimp [s, t]
          omega
        have hcard_union : (C ∪ Kt).card = k := by
          rw [Finset.card_union_of_disjoint hdisj, hC.card_eq, hKt.card_eq, hst]
        exact h_no_clique ⟨C ∪ Kt, ⟨hclique_union, hcard_union⟩⟩
      · exact h_indep ⟨I, hI⟩
    · exact h_indep ⟨I, hI⟩
  let Δ : ℝ := (R(k, ℓ + 1) - R(k, ℓ) - 1 : ℕ)
  let Nℝ : ℝ := (R(k, ℓ + 1) - 1 : ℕ)
  have hNℝ_pos : 0 < Nℝ := by
    dsimp [Nℝ]
    exact_mod_cast hN_pos
  have hNℝ_ne : Nℝ ≠ 0 := hNℝ_pos.ne'
  have hΔ_nonneg : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  have hΔ_le_d : Δ ≤ d := by
    have hdeg_real :
        ∀ v : Fin (R(k, ℓ + 1) - 1), Δ ≤ (G.degree v : ℝ) := by
      intro v
      dsimp [Δ]
      exact_mod_cast hdeg v
    have hsum_ge :
        (∑ _v : Fin (R(k, ℓ + 1) - 1), Δ) ≤
          ∑ v : Fin (R(k, ℓ + 1) - 1), (G.degree v : ℝ) := by
      exact Finset.sum_le_sum fun v _ => hdeg_real v
    have hsum_const :
        (∑ _v : Fin (R(k, ℓ + 1) - 1), Δ) = Nℝ * Δ := by
      dsimp [Nℝ]
      simp
    nlinarith [hsum_ge, hsum_const, hd, hNℝ_pos]
  have hd_nonneg : 0 ≤ d := hΔ_nonneg.trans hΔ_le_d
  have hU_card_le_real :
      (U.card : ℝ) ≤ (R(s, ℓ + 1) - 1 : ℕ) := by
    exact_mod_cast hU_card_le
  have hDRC_upper :
      d ^ q / Nℝ ^ (q - 1) ≤
        (R(s, ℓ + 1) - 1 : ℕ) +
          ((R(k, ℓ + 1) - 1).choose s : ℝ) *
            (((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q := by
    have hU_size' :
        d ^ q / Nℝ ^ (q - 1) -
          ((R(k, ℓ + 1) - 1).choose s : ℝ) *
            (((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q ≤
          (U.card : ℝ) := by
      have hRt_cast_sub :
          ((R(t, ℓ + 1) - 1 : ℕ) : ℝ) = (R(t, ℓ + 1) : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ R(t, ℓ + 1))]
        norm_num
      simpa [Nℝ, hRt_cast_sub] using hU_size
    nlinarith [hU_size', hU_card_le_real]
  have hΔ_div_pow_le :
      (Δ / Nℝ) ^ q ≤
        ((R(s, ℓ + 1) - 1 : ℕ) +
            ((R(k, ℓ + 1) - 1).choose s : ℝ) *
              (((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q) / Nℝ := by
    have hpow_le : Δ ^ q ≤ d ^ q :=
      pow_le_pow_left₀ hΔ_nonneg hΔ_le_d q
    have hNpow_nonneg : 0 ≤ Nℝ ^ q := pow_nonneg hNℝ_pos.le q
    have hleft_le : Δ ^ q / Nℝ ^ q ≤ d ^ q / Nℝ ^ q :=
      div_le_div_of_nonneg_right hpow_le hNpow_nonneg
    have hrewrite :
        d ^ q / Nℝ ^ q = (d ^ q / Nℝ ^ (q - 1)) / Nℝ := by
      have hqeq : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hq_pos).symm
      rw [hqeq, pow_succ]
      field_simp [hNℝ_ne]
      have hpowexp : q - 1 + 1 - 1 = q - 1 := by omega
      rw [hpowexp]
      rw [show q - 1 + 1 = q by omega]
      calc
        d ^ (q - 1) * d * Nℝ ^ (q - 1) * Nℝ =
            d ^ (q - 1) * d * (Nℝ ^ (q - 1) * Nℝ) := by ring
        _ = d ^ (q - 1) * d * Nℝ ^ q := by
            rw [show Nℝ ^ (q - 1) * Nℝ = Nℝ ^ q by
              rw [← pow_succ, show q - 1 + 1 = q by omega]]
    calc
      (Δ / Nℝ) ^ q = Δ ^ q / Nℝ ^ q := by rw [div_pow]
      _ ≤ d ^ q / Nℝ ^ q := hleft_le
      _ = (d ^ q / Nℝ ^ (q - 1)) / Nℝ := hrewrite
      _ ≤
          ((R(s, ℓ + 1) - 1 : ℕ) +
              ((R(k, ℓ + 1) - 1).choose s : ℝ) *
                (((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q) / Nℝ := by
        exact div_le_div_of_nonneg_right hDRC_upper hNℝ_pos.le
  have hℓ_pos : 0 < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ_nonneg : 0 ≤ (ℓ : ℝ) := hℓ_pos.le
  have hℓ_one : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hC2_pos : 0 < C_lb / 2 := by positivity
  let L : ℝ := (C_lb / 2) * (ℓ : ℝ) ^ δ
  have hL_pos : 0 < L := by
    dsimp [L]
    positivity
  have hN_lower : L ≤ Nℝ := by
    have hR1_two : 2 ≤ R(k, ℓ + 1) :=
      two_le_ramsey k (ℓ + 1) (by omega) (by omega)
    have hhalf : (1 / 2 : ℝ) * (R(k, ℓ + 1) : ℝ) ≤ Nℝ := by
      dsimp [Nℝ]
      exact half_nat_cast_le_sub_one_cast hR1_two
    have hℓ_le_succ_pow :
        (ℓ : ℝ) ^ δ ≤ ((ℓ + 1 : ℕ) : ℝ) ^ δ := by
      refine Real.rpow_le_rpow hℓ_nonneg ?_ hδ_pos.le
      exact_mod_cast Nat.le_succ ℓ
    have hpoly_succ_l : C_lb * (ℓ : ℝ) ^ δ ≤ (R(k, ℓ + 1) : ℝ) := by
      calc
        C_lb * (ℓ : ℝ) ^ δ ≤ C_lb * ((ℓ + 1 : ℕ) : ℝ) ^ δ := by
          exact mul_le_mul_of_nonneg_left hℓ_le_succ_pow hC_lb.le
        _ ≤ (R(k, ℓ + 1) : ℝ) := hLBpolySuccℓ
    calc
      L = (1 / 2 : ℝ) * (C_lb * (ℓ : ℝ) ^ δ) := by
        dsimp [L]
        ring
      _ ≤ (1 / 2 : ℝ) * (R(k, ℓ + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hpoly_succ_l (by norm_num)
      _ ≤ Nℝ := hhalf
  have hs_le_ℓ : s ≤ ℓ := by
    dsimp [s]
    omega
  have hterm1_num :
      ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (s - 1) * (ℓ : ℝ) ^ ((s - 1 : ℕ) : ℝ) :=
    ramsey_sub_one_le_two_mul_rpow s ℓ (by omega) hs_le_ℓ
  have hs_exp_le :
      ((s - 1 : ℕ) : ℝ) - δ ≤ -(1 / 4 : ℝ) := by
    have hs2 : 2 * s ≤ k + 1 := by
      dsimp [s]
      omega
    have hs2R : (2 : ℝ) * (s : ℝ) ≤ (k : ℝ) + 1 := by
      exact_mod_cast hs2
    have hsm1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s)]
      norm_num
    rw [hsm1]
    dsimp [δ]
    linarith
  have hterm1_le :
      ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ ≤
        A₁ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := by
    let B₁ : ℝ := (2 : ℝ) ^ (s - 1) * (ℓ : ℝ) ^ ((s - 1 : ℕ) : ℝ)
    have hB₁_nonneg : 0 ≤ B₁ := by
      dsimp [B₁]
      positivity
    have hnum_nonneg : 0 ≤ ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) := by positivity
    have hdiv_le : ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ ≤ B₁ / L := by
      rw [div_le_div_iff₀ hNℝ_pos hL_pos]
      have hcross : ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) * L ≤ B₁ * Nℝ := by
        exact mul_le_mul hterm1_num hN_lower hL_pos.le hB₁_nonneg
      simpa [B₁, mul_comm, mul_left_comm, mul_assoc] using hcross
    have hB₁_div :
        B₁ / L = A₁ * (ℓ : ℝ) ^ (((s - 1 : ℕ) : ℝ) - δ) := by
      dsimp [B₁, L, A₁]
      rw [Real.rpow_sub hℓ_pos]
      field_simp [hC2_pos.ne', (Real.rpow_pos_of_pos hℓ_pos δ).ne']
      rw [← Real.rpow_add hℓ_pos, ← Real.rpow_add hℓ_pos]
      congr 1
      dsimp [δ]
      ring
    have hpow_exp :
        (ℓ : ℝ) ^ (((s - 1 : ℕ) : ℝ) - δ) ≤
          (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hℓ_one hs_exp_le
    have hA₁_nonneg : 0 ≤ A₁ := by
      dsimp [A₁]
      positivity
    calc
      ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ ≤ B₁ / L := hdiv_le
      _ = A₁ * (ℓ : ℝ) ^ (((s - 1 : ℕ) : ℝ) - δ) := hB₁_div
      _ ≤ A₁ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow_exp hA₁_nonneg
  let M : ℝ := ((R(t, ℓ + 1) - 1 : ℕ) : ℝ)
  let B₂ℓ : ℝ := (2 : ℝ) ^ (t - 1) * (ℓ : ℝ) ^ ((t - 1 : ℕ) : ℝ)
  have ht_le_ℓ : t ≤ ℓ := by
    dsimp [t]
    omega
  have hM_le : M ≤ B₂ℓ := by
    dsimp [M, B₂ℓ]
    exact ramsey_sub_one_le_two_mul_rpow t ℓ ht_one ht_le_ℓ
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hB₂ℓ_nonneg : 0 ≤ B₂ℓ := by
    dsimp [B₂ℓ]
    positivity
  have hchoose_le :
      (((R(k, ℓ + 1) - 1).choose s : ℕ) : ℝ) ≤ Nℝ ^ s := by
    have hnat : (R(k, ℓ + 1) - 1).choose s ≤ (R(k, ℓ + 1) - 1) ^ s :=
      Nat.choose_le_pow _ _
    have hcast :
        (((R(k, ℓ + 1) - 1).choose s : ℕ) : ℝ) ≤
          (((R(k, ℓ + 1) - 1) ^ s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nℝ, Nat.cast_pow] using hcast
  have hterm2_raw :
      (((R(k, ℓ + 1) - 1).choose s : ℝ) * (M / Nℝ) ^ q) / Nℝ ≤
        (Nℝ ^ s * (B₂ℓ / Nℝ) ^ q) / Nℝ := by
    have hratio_le : M / Nℝ ≤ B₂ℓ / Nℝ :=
      div_le_div_of_nonneg_right hM_le hNℝ_pos.le
    have hratio_pow : (M / Nℝ) ^ q ≤ (B₂ℓ / Nℝ) ^ q :=
      pow_le_pow_left₀ (div_nonneg hM_nonneg hNℝ_pos.le) hratio_le q
    have hprod_le :
        (((R(k, ℓ + 1) - 1).choose s : ℝ) * (M / Nℝ) ^ q) ≤
          Nℝ ^ s * (B₂ℓ / Nℝ) ^ q := by
      exact mul_le_mul hchoose_le hratio_pow
        (pow_nonneg (div_nonneg hM_nonneg hNℝ_pos.le) q)
        (pow_nonneg hNℝ_pos.le s)
    exact div_le_div_of_nonneg_right hprod_le hNℝ_pos.le
  let z : ℝ := (s : ℝ) - (q : ℝ) - 1
  let E₂ : ℝ := ((t - 1 : ℕ) : ℝ) * (q : ℝ) + δ * z
  have hz_nonpos : z ≤ 0 := by
    have hs_le_k : s ≤ k := by
      dsimp [s]
      omega
    have hs_le_kR : (s : ℝ) ≤ (k : ℝ) := by exact_mod_cast hs_le_k
    have hk_le_q_nat : k ≤ q := by
      dsimp [q]
      rw [pow_two]
      exact Nat.le_mul_of_pos_right k (by omega : 0 < k)
    have hk_le_qR : (k : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hk_le_q_nat
    have hs_le_qR : (s : ℝ) ≤ (q : ℝ) := hs_le_kR.trans hk_le_qR
    have hz' : (s : ℝ) - (q : ℝ) - 1 ≤ 0 := by
      linarith only [hs_le_qR]
    simpa [z] using hz'
  have hmodel_eq :
      (Nℝ ^ s * (B₂ℓ / Nℝ) ^ q) / Nℝ =
        B₂ℓ ^ q * Nℝ ^ z := by
    simpa [z] using model_second_term_eq (N := Nℝ) (B := B₂ℓ) (s := s) (q := q)
      hNℝ_pos hB₂ℓ_nonneg
  have hN_negpow_le : Nℝ ^ z ≤ L ^ z :=
    Real.rpow_le_rpow_of_nonpos hL_pos hN_lower hz_nonpos
  have hmodel_le_L :
      (Nℝ ^ s * (B₂ℓ / Nℝ) ^ q) / Nℝ ≤ B₂ℓ ^ q * L ^ z := by
    rw [hmodel_eq]
    exact mul_le_mul_of_nonneg_left hN_negpow_le (pow_nonneg hB₂ℓ_nonneg q)
  have hA₂_eq : A₂ = ((2 : ℝ) ^ (t - 1)) ^ q * (C_lb / 2) ^ z := by
    rfl
  have hB₂L_eq : B₂ℓ ^ q * L ^ z = A₂ * (ℓ : ℝ) ^ E₂ := by
    simpa [B₂ℓ, L, A₂, E₂] using
      second_term_const_eq (x := (ℓ : ℝ)) (C := C_lb) (δ := δ) (z := z)
        (t := t) (q := q) hℓ_pos hC_lb
  have hE₂_le : E₂ ≤ -(1 / 4 : ℝ) := by
    have ht2 : 2 * t ≤ k := by
      dsimp [t]
      omega
    have ht2R : (2 : ℝ) * (t : ℝ) ≤ (k : ℝ) := by exact_mod_cast ht2
    have htm1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]
      norm_num
    have ht_exp_le : ((t - 1 : ℕ) : ℝ) ≤ (k : ℝ) / 2 - 1 := by
      rw [htm1]
      linarith
    have hs_le_k : s ≤ k := by
      dsimp [s]
      omega
    have hs_le_kR : (s : ℝ) ≤ (k : ℝ) := by exact_mod_cast hs_le_k
    have hz_le : z ≤ (k : ℝ) - (q : ℝ) - 1 := by
      dsimp [z]
      linarith
    have hE_le :
        E₂ ≤ ((k : ℝ) / 2 - 1) * (q : ℝ) + δ * ((k : ℝ) - (q : ℝ) - 1) := by
      dsimp [E₂]
      exact add_le_add
        (mul_le_mul_of_nonneg_right ht_exp_le (by positivity : 0 ≤ (q : ℝ)))
        (mul_le_mul_of_nonneg_left hz_le hδ_pos.le)
    have hq_cast : (q : ℝ) = (k : ℝ) ^ 2 := by
      dsimp [q]
      norm_num [Nat.cast_pow]
    have hpoly :
        ((k : ℝ) / 2 - 1) * (q : ℝ) + δ * ((k : ℝ) - (q : ℝ) - 1) ≤
          -(1 / 4 : ℝ) := by
      rw [hq_cast]
      dsimp [δ]
      have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
      ring_nf
      nlinarith
    exact hE_le.trans hpoly
  have hterm2_le :
      (((R(k, ℓ + 1) - 1).choose s : ℝ) * (M / Nℝ) ^ q) / Nℝ ≤
        A₂ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hA₂_nonneg : 0 ≤ A₂ := by
      dsimp [A₂]
      positivity
    have hpow_E :
        (ℓ : ℝ) ^ E₂ ≤ (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hℓ_one hE₂_le
    calc
      (((R(k, ℓ + 1) - 1).choose s : ℝ) * (M / Nℝ) ^ q) / Nℝ
          ≤ (Nℝ ^ s * (B₂ℓ / Nℝ) ^ q) / Nℝ := hterm2_raw
      _ ≤ B₂ℓ ^ q * L ^ z := hmodel_le_L
      _ = A₂ * (ℓ : ℝ) ^ E₂ := hB₂L_eq
      _ ≤ A₂ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow_E hA₂_nonneg
  have hDRC_rhs_le :
      (((R(s, ℓ + 1) - 1 : ℕ) : ℝ) +
          ((R(k, ℓ + 1) - 1).choose s : ℝ) *
            ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ ≤
        A * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hsplit :
        (((R(s, ℓ + 1) - 1 : ℕ) : ℝ) +
            ((R(k, ℓ + 1) - 1).choose s : ℝ) *
              ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ =
          ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ +
            (((R(k, ℓ + 1) - 1).choose s : ℝ) *
              ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ := by
      ring
    calc
      (((R(s, ℓ + 1) - 1 : ℕ) : ℝ) +
          ((R(k, ℓ + 1) - 1).choose s : ℝ) *
            ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ
          =
        ((R(s, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ +
            (((R(k, ℓ + 1) - 1).choose s : ℝ) *
              ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ := hsplit
      _ ≤ A₁ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) +
            A₂ * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := by
        exact add_le_add hterm1_le (by simpa [M] using hterm2_le)
      _ = A * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := by
        dsimp [A]
        ring
  let x : ℝ := (ℓ : ℝ) ^ (-c)
  let a : ℝ := (1 / 8 : ℝ) * x
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg hℓ_nonneg _
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hΔ_div_pow_small : (Δ / Nℝ) ^ q ≤ a ^ q := by
    calc
      (Δ / Nℝ) ^ q
          ≤ (((R(s, ℓ + 1) - 1 : ℕ) : ℝ) +
              ((R(k, ℓ + 1) - 1).choose s : ℝ) *
                ((((R(t, ℓ + 1) - 1 : ℕ) : ℝ) / Nℝ) ^ q)) / Nℝ := by
            simpa using hΔ_div_pow_le
      _ ≤ A * (ℓ : ℝ) ^ (-(1 / 4 : ℝ)) := hDRC_rhs_le
      _ ≤ a ^ q := by
        simpa [a, x] using hSmallPowℓ
  have hΔ_div_le_small : Δ / Nℝ ≤ a := by
    exact (pow_le_pow_iff_left₀ (div_nonneg hΔ_nonneg hNℝ_pos.le) ha_nonneg hq_pos.ne').mp
      hΔ_div_pow_small
  have hR_inv_small : ((R(k, ℓ) : ℝ))⁻¹ ≤ a := by
    have hR_inv_le_l_inv : ((R(k, ℓ) : ℝ))⁻¹ ≤ ((ℓ : ℝ))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hℓ_pos hRkℓ_lb
    calc
      ((R(k, ℓ) : ℝ))⁻¹ ≤ ((ℓ : ℝ))⁻¹ := hR_inv_le_l_inv
      _ = (ℓ : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]
      _ ≤ a := by
        simpa [a, x] using hInvSmallℓ
  let ratio : ℝ := (R(k, ℓ + 1) : ℝ) / R(k, ℓ)
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    exact div_nonneg hRkℓ1_pos.le hRkℓ_pos.le
  have hdiff_le :
      ((R(k, ℓ + 1) - R(k, ℓ) : ℕ) : ℝ) ≤ Δ + 1 := by
    dsimp [Δ]
    exact_mod_cast (show R(k, ℓ + 1) - R(k, ℓ) ≤
      R(k, ℓ + 1) - R(k, ℓ) - 1 + 1 by omega)
  have hratio_eq :
      ratio = 1 + ((R(k, ℓ + 1) - R(k, ℓ) : ℕ) : ℝ) / (R(k, ℓ) : ℝ) := by
    have hsub_cast :
        ((R(k, ℓ + 1) - R(k, ℓ) : ℕ) : ℝ) =
          (R(k, ℓ + 1) : ℝ) - (R(k, ℓ) : ℝ) := by
      rw [Nat.cast_sub hRkℓ1_ge_Rkℓ]
    dsimp [ratio]
    rw [hsub_cast]
    field_simp [hRkℓ_pos.ne']
    ring
  have hN_le_Rsucc : Nℝ ≤ (R(k, ℓ + 1) : ℝ) := by
    dsimp [Nℝ]
    exact_mod_cast Nat.sub_le (R(k, ℓ + 1)) 1
  have hΔ_le_aN : Δ ≤ a * Nℝ := by
    have h := (div_le_iff₀ hNℝ_pos).mp hΔ_div_le_small
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hΔ_div_R_le : Δ / (R(k, ℓ) : ℝ) ≤ ratio * a := by
    have h₁ : Δ / (R(k, ℓ) : ℝ) ≤ (a * Nℝ) / (R(k, ℓ) : ℝ) :=
      div_le_div_of_nonneg_right hΔ_le_aN hRkℓ_pos.le
    have h₂ : Nℝ / (R(k, ℓ) : ℝ) ≤ ratio := by
      dsimp [ratio]
      exact div_le_div_of_nonneg_right hN_le_Rsucc hRkℓ_pos.le
    calc
      Δ / (R(k, ℓ) : ℝ) ≤ (a * Nℝ) / (R(k, ℓ) : ℝ) := h₁
      _ = a * (Nℝ / (R(k, ℓ) : ℝ)) := by ring
      _ ≤ a * ratio := mul_le_mul_of_nonneg_left h₂ ha_nonneg
      _ = ratio * a := by ring
  have hratio_pre : ratio ≤ 1 + ratio * a + a := by
    calc
      ratio = 1 + ((R(k, ℓ + 1) - R(k, ℓ) : ℕ) : ℝ) / (R(k, ℓ) : ℝ) := hratio_eq
      _ ≤ 1 + (Δ + 1) / (R(k, ℓ) : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (div_le_div_of_nonneg_right hdiff_le hRkℓ_pos.le) 1
      _ = 1 + Δ / (R(k, ℓ) : ℝ) + ((R(k, ℓ) : ℝ))⁻¹ := by
        field_simp [hRkℓ_pos.ne']
        ring
      _ ≤ 1 + ratio * a + a := by
        linarith [hΔ_div_R_le, hR_inv_small]
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hx_le_one : x ≤ 1 := by
    dsimp [x]
    exact Real.rpow_le_one_of_one_le_of_nonpos hℓ_one (by linarith : -c ≤ 0)
  have ha_le_eighth : a ≤ (1 / 8 : ℝ) := by
    calc
      a = (1 / 8 : ℝ) * x := rfl
      _ ≤ (1 / 8 : ℝ) * 1 := mul_le_mul_of_nonneg_left hx_le_one (by norm_num)
      _ = (1 / 8 : ℝ) := by norm_num
  have hratio_le_two : ratio ≤ 2 := by
    have hratio_mul_a_le : ratio * a ≤ ratio * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left ha_le_eighth hratio_nonneg
    have hpre_bound : ratio ≤ 1 + ratio * (1 / 8 : ℝ) + (1 / 8 : ℝ) := by
      linarith only [hratio_pre, hratio_mul_a_le, ha_le_eighth]
    linarith only [hpre_bound]
  have htail : ratio * a + a ≤ x := by
    have hratio_mul_a_le : ratio * a ≤ 2 * a :=
      mul_le_mul_of_nonneg_right hratio_le_two ha_nonneg
    calc
      ratio * a + a ≤ 2 * a + a := by
        exact add_le_add hratio_mul_a_le le_rfl
      _ = (3 / 8 : ℝ) * x := by
        dsimp [a]
        linarith
      _ ≤ x := by
        calc
          (3 / 8 : ℝ) * x ≤ 1 * x := mul_le_mul_of_nonneg_right (by norm_num) hx_nonneg
          _ = x := by ring
  have hratio_final : ratio ≤ 1 + x := by
    calc
      ratio ≤ 1 + ratio * a + a := hratio_pre
      _ = 1 + (ratio * a + a) := by ring
      _ ≤ 1 + x := by
        exact add_le_add le_rfl htail
  simpa [ratio, x] using hratio_final

/-! ### §4. Main theorem and its quantitative form -/

/-- Quantitative version of the main theorem (paper Remark 1):
there is `cₖ > 0` with `R(k, ℓ + 1) / R(k, ℓ) ≤ 1 + ℓ^(-cₖ)` for large `ℓ`. -/
theorem ramsey_ratio_quantitative (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ), ∀ᶠ ℓ : ℕ in atTop,
      (R(k, ℓ + 1) : ℝ) / R(k, ℓ) ≤ 1 + (ℓ : ℝ) ^ (-c) := by
  by_cases hk2 : k = 2
  · subst k
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 2] with ℓ hℓ
    have hℓposNat : 0 < ℓ := by omega
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓposNat
    have hRℓ : R(2, ℓ) = ℓ := ramsey_two ℓ hℓ
    have hRℓ_succ : R(2, ℓ + 1) = ℓ + 1 := ramsey_two (ℓ + 1) (by omega)
    calc
      (R(2, ℓ + 1) : ℝ) / R(2, ℓ) =
          (((ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) := by
        rw [hRℓ_succ, hRℓ]
      _ = 1 + (ℓ : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]
        field_simp [hℓpos.ne']
        norm_num
      _ ≤ 1 + (ℓ : ℝ) ^ (-(1 : ℝ)) := le_rfl
  · have _hk3 : 3 ≤ k := by omega
    exact ramsey_ratio_drc_estimate k _hk3

/-- **Theorem 1 (Erdős).** For every fixed `k ≥ 2`,
`R(k, ℓ + 1) / R(k, ℓ) → 1` as `ℓ → ∞`. -/
theorem ramsey_ratio_tendsto_one (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun ℓ : ℕ => (R(k, ℓ + 1) : ℝ) / R(k, ℓ)) atTop (𝓝 1) := by
  obtain ⟨c, hc, hq⟩ := ramsey_ratio_quantitative k hk
  have h_lower : ∀ᶠ ℓ : ℕ in atTop, (1 : ℝ) ≤ (R(k, ℓ + 1) : ℝ) / R(k, ℓ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with ℓ hℓ
    have hRpos : (0 : ℝ) < (R(k, ℓ) : ℝ) := by
      exact_mod_cast one_le_ramsey k ℓ (by omega) hℓ
    rw [le_div_iff₀ hRpos, one_mul]
    exact_mod_cast ramsey_le_ramsey_succ k ℓ
  have h_upper_tendsto : Tendsto (fun ℓ : ℕ => (1 : ℝ) + (ℓ : ℝ) ^ (-c)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-c)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
    have h2 : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ (-c)) atTop (𝓝 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_upper_tendsto h_lower hq

end RamseyRatio

#print axioms RamseyRatio.ramsey_ratio_tendsto_one
