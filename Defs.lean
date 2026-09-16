import Mathlib

/-!
# Definitions for Written on the Wall II, Conjecture 198a

This file reproduces (ported to the Lean/Mathlib versions pinned by this project) the
definitions used by the Formal Conjectures statement of *Written on the Wall II,
Conjecture 198a*:

* `SimpleGraph.largestInducedBipartiteSubgraphSize`
* `SimpleGraph.b`
* `SimpleGraph.averageEccentricity`

together with a convenient `ℕ`-valued eccentricity `SimpleGraph.natEccentricity` and a
`Finset`-level notion of "induces a bipartite subgraph", `SimpleGraph.BipFinset`, which are
proved equivalent to the official ones.

The mathematical content formalized in this project follows Ben Cohen, *Average Eccentricity,
Induced Bipartite Subgraphs, and Hamiltonian Paths*, version 0.1 (July 21, 2026).
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. (Definition taken from the Formal Conjectures repository.) -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`,
returned as a real number. (Definition taken from the Formal Conjectures repository.) -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns `0` if the graph has no vertices.
(Definition taken from the Formal Conjectures repository.) -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)

/-- A `Finset` of vertices induces a bipartite subgraph iff it admits a proper `2`-coloring. -/
def BipFinset (G : SimpleGraph α) (s : Finset α) : Prop :=
  ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v

omit [Fintype α] in
/-- An induced subgraph is bipartite exactly when its vertices admit a two-coloring.
(Taken from the Formal Conjectures repository.) -/
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔ G.BipFinset s := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

omit [DecidableEq α] in
/-- The set of cardinalities of induced bipartite subgraphs is bounded above. -/
theorem bddAbove_bipartite_sizes (G : SimpleGraph α) :
    BddAbove { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n } :=
  ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩

/-- Any vertex set inducing a bipartite subgraph has at most
`largestInducedBipartiteSubgraphSize G` elements. -/
theorem card_le_largestInducedBipartiteSubgraphSize {s : Finset α} (hs : G.BipFinset s) :
    s.card ≤ G.largestInducedBipartiteSubgraphSize :=
  le_csSup (G.bddAbove_bipartite_sizes)
    ⟨s, (G.induce_isBipartite_iff_exists_coloring s).mpr hs, rfl⟩

omit [Fintype α] in
/-- If every vertex set inducing a bipartite subgraph has at most `n` elements, then
`largestInducedBipartiteSubgraphSize G ≤ n`. -/
theorem largestInducedBipartiteSubgraphSize_le {n : ℕ}
    (h : ∀ s : Finset α, G.BipFinset s → s.card ≤ n) :
    G.largestInducedBipartiteSubgraphSize ≤ n := by
  refine csSup_le ⟨0, ∅, ?_, rfl⟩ ?_
  · rw [induce_isBipartite_iff_exists_coloring]
    exact ⟨fun _ => 0, by simp⟩
  · rintro m ⟨s, hs, rfl⟩
    exact h s ((G.induce_isBipartite_iff_exists_coloring s).mp hs)

/-- The eccentricity of a vertex, as a natural number: the greatest distance from `v`
to any vertex of the graph. For a finite connected graph this agrees with
`(G.eccent v).toNat`, see `natEccentricity_eq_eccent_toNat`. -/
noncomputable def natEccentricity (G : SimpleGraph α) (v : α) : ℕ :=
  Finset.univ.sup fun u => G.dist v u

omit [DecidableEq α] in
theorem dist_le_natEccentricity (G : SimpleGraph α) (v u : α) :
    G.dist v u ≤ G.natEccentricity v :=
  Finset.le_sup (f := fun u => G.dist v u) (Finset.mem_univ u)

omit [DecidableEq α] in
theorem exists_dist_eq_natEccentricity [Nonempty α] (G : SimpleGraph α) (v : α) :
    ∃ u, G.dist v u = G.natEccentricity v := by
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset α) Finset.univ_nonempty
    (fun u => G.dist v u)
  exact ⟨u, hu.symm⟩

omit [DecidableEq α] in
theorem natEccentricity_le_iff {v : α} {n : ℕ} :
    G.natEccentricity v ≤ n ↔ ∀ u, G.dist v u ≤ n := by
  simp [natEccentricity, Finset.sup_le_iff]

omit [DecidableEq α] in
/-- For a connected finite graph, the `ℕ`-valued eccentricity agrees with Mathlib's
`ℕ∞`-valued `eccent`. -/
theorem natEccentricity_eq_eccent_toNat (hc : G.Connected) (v : α) :
    G.natEccentricity v = (G.eccent v).toNat := by
  have : Nonempty α := ⟨v⟩
  have hfin : G.eccent v ≠ ⊤ := by
    have : G.eccent v ≤ (G.natEccentricity v : ℕ∞) := by
      refine iSup_le fun u => ?_
      rw [← (hc.preconnected v u).coe_dist_eq_edist]
      exact_mod_cast G.dist_le_natEccentricity v u
    exact ne_top_of_le_ne_top (by simp) this
  have : G.eccent v = (G.natEccentricity v : ℕ∞) := by
    refine le_antisymm (iSup_le fun u => ?_) ?_
    · rw [← (hc.preconnected v u).coe_dist_eq_edist]
      exact_mod_cast G.dist_le_natEccentricity v u
    · obtain ⟨u, hu⟩ := G.exists_dist_eq_natEccentricity (α := α) v
      rw [← hu, (hc.preconnected v u).coe_dist_eq_edist]
      exact edist_le_eccent
  simp [this]

end SimpleGraph
