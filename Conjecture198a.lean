import RequestProject.GeodesicLemma
import RequestProject.SelfCentered
import RequestProject.DiamTwo

/-!
# Written on the Wall II, Conjecture 198a

This file assembles the proof of

> for a finite connected graph `G` with at least two vertices, `b G ≤ 2 + averageEccentricity G`
> implies that `G` has a Hamiltonian path,

following Ben Cohen, *Average Eccentricity, Induced Bipartite Subgraphs, and Hamiltonian Paths*,
version 0.1 (July 21, 2026).

The statement and the definitions `SimpleGraph.b` and `SimpleGraph.averageEccentricity` are the
ones used in the Formal Conjectures repository (file
`FormalConjectures/WrittenOnTheWallII/GraphConjecture198a.lean`), ported to the Lean and Mathlib
versions pinned by this project.

The proof runs as follows. Assume `G` has no Hamiltonian path and let `D` be the diameter.

* The geodesic lemma (`SimpleGraph.geodesic_lemma`) gives `D + 2 ≤ b G`, while
  `averageEccentricity G ≤ D` gives `b G ≤ D + 2`; so `b G = D + 2` and the average eccentricity
  equals `D`, whence every eccentricity equals `D`.
* `D ≥ 3` is impossible by `SimpleGraph.selfCentered_bipartite_ge`.
* `D = 1` means `G` is complete, which has a Hamiltonian path.
* `D = 2` is handled by `SimpleGraph.exists_hamiltonian_of_diam_two`.
-/

namespace WrittenOnTheWallII.GraphConjecture198a

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 198a](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `b(G) ≤ 2 + ecc_avg(G)`, then `G` has a Hamiltonian path.
Here `b(G)` is the number of vertices in a largest induced bipartite subgraph, and
`ecc_avg(G)` is the average eccentricity of `G`.
A Hamiltonian path is a walk visiting every vertex exactly once.
-/
theorem conjecture198a (G : SimpleGraph α) (h : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_contra hno
  classical
  set N : ℕ := Fintype.card α with hN
  have hNpos : 0 < N := Fintype.card_pos
  -- the diameter, as a natural number
  set D : ℕ := Finset.univ.sup (fun v : α => G.natEccentricity v) with hDdef
  obtain ⟨v0, -, hv0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset α) Finset.univ_nonempty
    (fun v : α => G.natEccentricity v)
  have hle : ∀ v : α, G.natEccentricity v ≤ D := fun v =>
    Finset.le_sup (f := fun v : α => G.natEccentricity v) (Finset.mem_univ v)
  -- the geodesic lemma
  have hgl : D + 2 ≤ G.largestInducedBipartiteSubgraphSize := by
    rw [hDdef, hv0]
    exact geodesic_lemma h v0 hno
  -- the sum of the eccentricities
  set S : ℕ := ∑ v : α, G.natEccentricity v with hS
  have havecS : averageEccentricity G = (S : ℝ) / (N : ℝ) := by
    unfold averageEccentricity
    congr 1
    rw [hS]
    push_cast
    exact Finset.sum_congr rfl fun v _ => by rw [natEccentricity_eq_eccent_toNat h v]
  have hSle : S ≤ N * D := by
    calc S ≤ ∑ _v : α, D := Finset.sum_le_sum fun v _ => hle v
      _ = N * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hN]
  have havec : averageEccentricity G ≤ (D : ℝ) := by
    rw [havecS, div_le_iff₀ (by exact_mod_cast hNpos)]
    calc (S : ℝ) ≤ (N * D : ℕ) := by exact_mod_cast hSle
      _ = (D : ℝ) * (N : ℝ) := by push_cast; ring
  -- equality throughout
  have hbR : ((G.largestInducedBipartiteSubgraphSize : ℕ) : ℝ) ≤ 2 + averageEccentricity G := hb
  have hglR : (D : ℝ) + 2 ≤ ((G.largestInducedBipartiteSubgraphSize : ℕ) : ℝ) := by
    exact_mod_cast hgl
  have haveceq : averageEccentricity G = (D : ℝ) := le_antisymm havec (by linarith)
  have hSeq : S = N * D := by
    have : (S : ℝ) = (N : ℝ) * (D : ℝ) := by
      rw [havecS] at haveceq
      field_simp at haveceq
      linarith [haveceq]
    exact_mod_cast this
  -- every eccentricity equals `D`
  have hsc : ∀ v : α, G.natEccentricity v = D := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw⟩ := hcon
    have hlt : S < N * D := by
      calc S < ∑ _v : α, D := by
            refine Finset.sum_lt_sum (fun v _ => hle v) ⟨w, Finset.mem_univ w, ?_⟩
            exact lt_of_le_of_ne (hle w) hw
        _ = N * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hN]
    omega
  -- `b G = D + 2`
  have hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ D + 2 := by
    intro s hs
    have h1 := card_le_largestInducedBipartiteSubgraphSize hs
    have h2 : (G.largestInducedBipartiteSubgraphSize : ℝ) ≤ (D : ℝ) + 2 := by
      rw [haveceq] at hbR; linarith
    have : G.largestInducedBipartiteSubgraphSize ≤ D + 2 := by exact_mod_cast h2
    omega
  -- `D ≥ 1`
  have hD1 : 1 ≤ D := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    have : 1 ≤ G.natEccentricity a := by
      have hd : G.dist a b ≠ 0 := by
        rw [Ne, dist_eq_zero_iff_eq_or_not_reachable]
        push_neg
        exact ⟨hab, h.preconnected a b⟩
      have := G.dist_le_natEccentricity a b
      omega
    exact le_trans this (hle a)
  rcases Nat.lt_or_ge D 3 with hD3 | hD3
  · interval_cases D
    · -- `D = 1`: the graph is complete
      refine hno (exists_hamiltonian_of_indep_le_two h fun a b c hab _ _ => Or.inl ?_)
      have h1 : G.dist a b ≤ 1 := by
        have := G.dist_le_natEccentricity a b
        rw [hsc a] at this
        exact this
      have h0 : G.dist a b ≠ 0 := by
        rw [Ne, dist_eq_zero_iff_eq_or_not_reachable]
        push_neg
        exact ⟨hab, h.preconnected a b⟩
      exact dist_eq_one_iff_adj.1 (by omega)
    · -- `D = 2`
      exact hno (exists_hamiltonian_of_diam_two h hsc hbound)
  · -- `D ≥ 3` is impossible
    have := selfCentered_bipartite_ge h hD3 hsc
    have h2 : G.largestInducedBipartiteSubgraphSize ≤ D + 2 :=
      largestInducedBipartiteSubgraphSize_le hbound
    omega

end WrittenOnTheWallII.GraphConjecture198a
