import RequestProject.AlphaTwo
import RequestProject.SplitGraph

/-!
# The diameter-two case

Here we treat the remaining case of the main theorem: `G` is connected, every vertex has
eccentricity `2`, and every induced bipartite subgraph has at most four vertices. We show that
`G` has a Hamiltonian path.

Since `b(G) ≤ 4`:

* `G` has no independent set of size four (an independent set of size four together with any
  further vertex would be induced bipartite of order five);
* if `{p, q, r}` is an independent set of size three, then all remaining vertices form a clique
  (two non-adjacent vertices outside `{p, q, r}` would give an induced bipartite subgraph of
  order five).

In the first case we are done by the independence-number-two lemma, in the second by the
split-graph lemma.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

omit [Fintype α] [DecidableEq α] in
/-- From `dist v w = 2` we obtain a common neighbour. -/
theorem exists_common_neighbor_of_dist_two (hc : G.Connected) {v w : α} (h : G.dist v w = 2) :
    ∃ m, G.Adj v m ∧ G.Adj m w := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  rw [h] at hp
  refine ⟨p.getVert 1, ?_, ?_⟩
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · have := p.adj_getVert_succ (i := 1) (by omega)
    rwa [show (1 : ℕ) + 1 = p.length by omega, p.getVert_length] at this

/-- A vertex adjacent to every other vertex has eccentricity at most one. -/
theorem natEccentricity_le_one_of_univ {v : α} (h : ∀ u, u ≠ v → G.Adj v u) :
    G.natEccentricity v ≤ 1 := by
  rw [natEccentricity_le_iff]
  intro u
  by_cases hu : u = v
  · simp [hu]
  · exact le_of_eq (dist_eq_one_iff_adj.2 (h u hu))

/-- In a connected self-centered graph of diameter two every vertex has at least two neighbours. -/
theorem exists_two_neighbors (hc : G.Connected) (hsc : ∀ v : α, G.natEccentricity v = 2) (v : α) :
    ∃ k₁ k₂ : α, k₁ ≠ k₂ ∧ G.Adj v k₁ ∧ G.Adj v k₂ := by
  by_contra hcon
  push_neg at hcon
  -- `v` has at least one neighbour
  haveI : Nonempty α := ⟨v⟩
  obtain ⟨w, hw⟩ := G.exists_dist_eq_natEccentricity v
  rw [hsc v] at hw
  obtain ⟨k, hvk, hkw⟩ := exists_common_neighbor_of_dist_two hc hw
  -- and in fact exactly one, namely `k`
  have hone : ∀ u, G.Adj v u → u = k := by
    intro u hu
    by_contra hne
    exact (hcon u k hne hu) hvk
  -- then `k` is adjacent to everything, so it has eccentricity at most one
  have huniv : ∀ u, u ≠ k → G.Adj k u := by
    intro u hu
    by_cases hv : u = v
    · exact hv ▸ hvk.symm
    · have hd : G.dist v u ≤ 2 := by
        have := G.dist_le_natEccentricity v u
        rw [hsc v] at this
        exact this
      have hd0 : G.dist v u ≠ 0 := by
        rw [Ne, dist_eq_zero_iff_eq_or_not_reachable]
        push_neg
        exact ⟨fun hvu => hv hvu.symm, hc.preconnected v u⟩
      rcases (show G.dist v u = 1 ∨ G.dist v u = 2 by omega) with hdd | hdd
      · exact absurd (hone u (dist_eq_one_iff_adj.1 hdd)) hu
      · obtain ⟨m, hvm, hmu⟩ := exists_common_neighbor_of_dist_two hc hdd
        exact (hone m hvm) ▸ hmu
  have := natEccentricity_le_one_of_univ huniv
  rw [hsc k] at this
  omega

/-- **The diameter-two case.** -/
theorem exists_hamiltonian_of_diam_two (hc : G.Connected)
    (hsc : ∀ v : α, G.natEccentricity v = 2)
    (hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ 4) :
    ∃ a b : α, ∃ w : G.Walk a b, w.IsHamiltonian := by
  by_cases hind : ∃ p q r : α, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ¬ G.Adj p q ∧ ¬ G.Adj p r ∧ ¬ G.Adj q r
  · -- there is an independent set of size three; the rest of the graph is a clique
    obtain ⟨p, q, r, hpq, hpr, hqr, hnpq, hnpr, hnqr⟩ := hind
    have hclique : ∀ x y : α, x ∉ ({p, q, r} : Finset α) → y ∉ ({p, q, r} : Finset α) → x ≠ y →
        G.Adj x y := by
      intro x y hx hy hxy
      by_contra hadj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
      have hbip : G.BipFinset {p, q, r, x, y} := by
        refine ⟨fun z => if z = x ∨ z = y then 1 else 0, ?_⟩
        intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl | rfl <;>
          simp_all <;> tauto
      have hcard : ({p, q, r, x, y} : Finset α).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, Ne.symm hx.1, Ne.symm hy.1]),
          Finset.card_insert_of_notMem (by simp [hqr, Ne.symm hx.2.1, Ne.symm hy.2.1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hx.2.2, Ne.symm hy.2.2]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      have := hbound _ hbip
      omega
    have hnouniv : ∀ k : α, ¬ (G.Adj k p ∧ G.Adj k q ∧ G.Adj k r) := by
      rintro k ⟨hkp, hkq, hkr⟩
      have hk : k ∉ ({p, q, r} : Finset α) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hkp.ne, hkq.ne, hkr.ne⟩
      have : G.natEccentricity k ≤ 1 := by
        refine natEccentricity_le_one_of_univ fun u hu => ?_
        by_cases hu3 : u ∈ ({p, q, r} : Finset α)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu3
          rcases hu3 with rfl | rfl | rfl
          · exact hkp
          · exact hkq
          · exact hkr
        · exact hclique k u hk hu3 (Ne.symm hu)
      rw [hsc k] at this
      omega
    refine exists_hamiltonian_of_split hpq hpr hqr (fun x y h1 h2 h3 h4 h5 h6 h7 =>
      hclique x y (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                      exact ⟨h1, h2, h3⟩)
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨h4, h5, h6⟩) h7) hnpq hnpr hnqr
      (exists_two_neighbors hc hsc p) (exists_two_neighbors hc hsc q)
      (exists_two_neighbors hc hsc r) hnouniv
  · -- there is no independent set of size three
    push_neg at hind
    refine exists_hamiltonian_of_indep_le_two hc fun a b c hab hac hbc => ?_
    by_contra hcon
    push_neg at hcon
    exact absurd (hind a b c hab hac hbc hcon.1 hcon.2.1) (fun h => hcon.2.2 h)

end SimpleGraph
