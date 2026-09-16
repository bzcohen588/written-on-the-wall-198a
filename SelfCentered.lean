import RequestProject.PathTools

/-!
# Self-centered graphs of diameter at least three

This file replaces the two external graph-theoretic inputs of the paper's Section 3 in the case
`D ≥ 3` by an elementary argument:

> If `G` is connected and every vertex has eccentricity `D ≥ 3`, then `G` has an induced bipartite
> subgraph on `D + 3` vertices.

(The paper deduces `D ≤ 2` at this point from the radius bound `b(G) ≥ 2 rad(G)` of
DeLaViña–Pepper–Waller; since `rad(G) = D` for a self-centered graph, that bound gives
`b(G) ≥ 2D ≥ D + 3` for `D ≥ 3`. The proof below is a self-contained substitute which uses only
the geodesic structure and is enough for the application.)

The argument: fix a geodesic `f 0, …, f D`. Call a vertex off the geodesic *monochromatic* if all
its neighbours on the geodesic have indices of the same parity. Then

* two distinct monochromatic vertices are adjacent, else the geodesic plus the two vertices is an
  induced bipartite subgraph of order `D + 3`;
* a monochromatic vertex with *no* neighbour on the geodesic cannot coexist with another
  monochromatic vertex, for the same reason;
* self-centeredness produces monochromatic vertices far away from `f 1` and from `f (D-1)`, and
  these force a contradiction.
-/

namespace SimpleGraph

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} {f : ℕ → α} {D : ℕ}
  {x y : α}

/-- A vertex off the geodesic all of whose neighbours on the geodesic have indices of the same
parity. -/
def MonoOffPath (G : SimpleGraph α) (f : ℕ → α) (D : ℕ) (x : α) : Prop :=
  x ∉ pathSet f D ∧ ∀ k ≤ D, ∀ l ≤ D, G.Adj x (f k) → G.Adj x (f l) → k % 2 = l % 2

section Bound

omit [Fintype α] in
/-- A monochromatic vertex can be given a colour compatible with the parity colouring of the
geodesic. -/
theorem exists_color_of_mono (hx : MonoOffPath G f D x) :
    ∃ c : Fin 2, ∀ k ≤ D, G.Adj x (f k) → c ≠ idxColor k := by
  by_cases h : ∃ m ≤ D, G.Adj x (f m) ∧ m % 2 = 0
  · obtain ⟨m, hm, hadjm, hm2⟩ := h
    refine ⟨1, fun k hk hadj => ?_⟩
    have : k % 2 = m % 2 := hx.2 k hk m hm hadj hadjm
    simp [idxColor, this, hm2]
  · push_neg at h
    refine ⟨0, fun k hk hadj => ?_⟩
    have hk2 : k % 2 ≠ 0 := h k hk hadj
    simp [idxColor, hk2]

variable (hg : IsGeodesicSeq G f D)
  (hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ D + 2)

include hg hbound

omit [Fintype α] in
/-- Two distinct monochromatic vertices off the geodesic are adjacent. -/
theorem monoOffPath_adj (hx : MonoOffPath G f D x) (hy : MonoOffPath G f D y) (hxy : x ≠ y) :
    G.Adj x y := by
  by_contra hadj
  obtain ⟨cx, hcx⟩ := exists_color_of_mono hx
  obtain ⟨cy, hcy⟩ := exists_color_of_mono hy
  have hbip : G.BipFinset (insert x (insert y (pathSet f D))) :=
    bipFinset_insert_pair hg (subset_refl _) hx.1 hy.1 cx cy
      (fun k hk _ hadjk => hcx k hk hadjk) (fun k hk _ hadjk => hcy k hk hadjk)
      (fun h => absurd h hadj)
  have hcard : (insert x (insert y (pathSet f D))).card = D + 3 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hx.1⟩),
      Finset.card_insert_of_notMem hy.1, card_pathSet hg]
  have := hbound _ hbip
  omega

omit [Fintype α] in
/-- A vertex off the geodesic with no neighbour on it cannot coexist with another monochromatic
vertex off the geodesic. -/
theorem no_two_of_isolated (hx : x ∉ pathSet f D) (hxn : ∀ k ≤ D, ¬ G.Adj x (f k))
    (hy : MonoOffPath G f D y) (hne : y ≠ x) : False := by
  obtain ⟨cy, hcy⟩ := exists_color_of_mono hy
  have hbip : G.BipFinset (insert x (insert y (pathSet f D))) := by
    refine bipFinset_insert_pair hg (subset_refl _) hx hy.1 (if cy = 0 then 1 else 0) cy
      (fun k hk _ hadjk => absurd hadjk (hxn k hk)) (fun k hk _ hadjk => hcy k hk hadjk)
      (fun _ => ?_)
    rcases Fin.exists_fin_two.1 ⟨cy, rfl⟩ with _
    fin_cases cy <;> simp
  have hcard : (insert x (insert y (pathSet f D))).card = D + 3 := by
    rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hne h.symm, hx⟩),
      Finset.card_insert_of_notMem hy.1, card_pathSet hg]
  have := hbound _ hbip
  omega

end Bound

omit [Fintype α] in
/-- A vertex off the geodesic which is not monochromatic has two consecutive neighbours on it. -/
theorem exists_consecutive_of_not_mono (hg : IsGeodesicSeq G f D) (hx : x ∉ pathSet f D)
    (hnm : ¬ MonoOffPath G f D x) : ∃ i < D, G.Adj x (f i) ∧ G.Adj x (f (i + 1)) := by
  rw [MonoOffPath, not_and_or] at hnm
  rcases hnm with h | h
  · exact absurd hx h
  · push_neg at h
    obtain ⟨k, hk, l, hl, h1, h2, hpar⟩ := h
    rcases le_total k l with hkl | hkl
    · have hs := geodesic_nbr_span hg hk hl h1 h2
      have hlk : l = k + 1 := by omega
      exact ⟨k, by omega, h1, by rw [← hlk]; exact h2⟩
    · have hs := geodesic_nbr_span hg hk hl h1 h2
      have hkl' : k = l + 1 := by omega
      exact ⟨l, by omega, h2, by rw [← hkl']; exact h1⟩

section SelfCentered

variable (hc : G.Connected) (hg : IsGeodesicSeq G f D) (hsc : ∀ v : α, G.natEccentricity v = D)
  (hD : 3 ≤ D)

include hc hg hsc hD

/-- Self-centeredness gives a vertex at distance `D` from `f 1`; its only possible neighbour on
the geodesic is `f D`. -/
theorem exists_far_from_one :
    ∃ w, w ∉ pathSet f D ∧ G.dist (f 1) w = D ∧ ∀ j ≤ D, G.Adj w (f j) → j = D := by
  haveI : Nonempty α := ⟨f 0⟩
  obtain ⟨w, hw⟩ := G.exists_dist_eq_natEccentricity (f 1)
  rw [hsc (f 1)] at hw
  refine ⟨w, ?_, hw, ?_⟩
  · rw [not_mem_pathSet_iff]
    intro k hk hkw
    rw [← hkw] at hw
    have := hg.dist_eq' (i := 1) (j := k) (by omega) hk
    omega
  · intro j hj hadj
    have t : G.dist (f 1) w ≤ G.dist (f 1) (f j) + G.dist (f j) w :=
      Reachable.dist_triangle_left (hc.preconnected (f 1) (f j)) w
    rw [dist_eq_one_iff_adj.2 hadj.symm] at t
    have := hg.dist_eq' (i := 1) (j := j) (by omega) hj
    omega

/-- Self-centeredness gives a vertex at distance `D` from `f (D-1)`; its only possible neighbour on
the geodesic is `f 0`. -/
theorem exists_far_from_pred :
    ∃ w, w ∉ pathSet f D ∧ G.dist (f (D - 1)) w = D ∧ ∀ j ≤ D, G.Adj w (f j) → j = 0 := by
  haveI : Nonempty α := ⟨f 0⟩
  obtain ⟨w, hw⟩ := G.exists_dist_eq_natEccentricity (f (D - 1))
  rw [hsc (f (D - 1))] at hw
  refine ⟨w, ?_, hw, ?_⟩
  · rw [not_mem_pathSet_iff]
    intro k hk hkw
    rw [← hkw] at hw
    have := hg.dist_eq' (i := D - 1) (j := k) (by omega) hk
    omega
  · intro j hj hadj
    have t : G.dist (f (D - 1)) w ≤ G.dist (f (D - 1)) (f j) + G.dist (f j) w :=
      Reachable.dist_triangle_left (hc.preconnected (f (D - 1)) (f j)) w
    rw [dist_eq_one_iff_adj.2 hadj.symm] at t
    have := hg.dist_eq' (i := D - 1) (j := j) (by omega) hj
    omega

end SelfCentered

/-- **Diameter at least three is impossible for a self-centered graph with `b(G) ≤ D + 2`.**
If `G` is connected and all eccentricities equal `D ≥ 3`, then `G` has an induced bipartite
subgraph on `D + 3` vertices. -/
theorem selfCentered_bipartite_ge (hc : G.Connected) (hD : 3 ≤ D)
    (hsc : ∀ v : α, G.natEccentricity v = D) :
    D + 3 ≤ G.largestInducedBipartiteSubgraphSize := by
  by_contra hcon
  push_neg at hcon
  have hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ D + 2 := fun s hs =>
    le_trans (card_le_largestInducedBipartiteSubgraphSize hs) (by omega)
  haveI hne : Nonempty α := hc.nonempty
  obtain ⟨v0⟩ := id hne
  obtain ⟨u, hu⟩ := G.exists_dist_eq_natEccentricity v0
  rw [hsc v0] at hu
  obtain ⟨f, hg, hf0, hfD⟩ := exists_geodesicSeq hc v0 u
  rw [hu] at hg
  obtain ⟨w1, hw1p, hw1d, hw1n⟩ := exists_far_from_one hc hg hsc hD
  obtain ⟨w2, hw2p, hw2d, hw2n⟩ := exists_far_from_pred hc hg hsc hD
  have hw1mono : MonoOffPath G f D w1 :=
    ⟨hw1p, fun k hk l hl h1 h2 => by rw [hw1n k hk h1, hw1n l hl h2]⟩
  have hw2mono : MonoOffPath G f D w2 :=
    ⟨hw2p, fun k hk l hl h1 h2 => by rw [hw2n k hk h1, hw2n l hl h2]⟩
  by_cases hF : ∃ z, z ∉ pathSet f D ∧ ∀ k ≤ D, ¬ G.Adj z (f k)
  · -- There is a vertex with no neighbour on the geodesic; then it is the only monochromatic
    -- vertex, hence equals both `w1` and `w2`, and its distance-two attachment to the geodesic
    -- is incompatible with being at distance `D` from both `f 1` and `f (D-1)`.
    obtain ⟨z, hzp, hzn⟩ := hF
    have hw1z : w1 = z := by
      by_contra h
      exact no_two_of_isolated hg hbound hzp hzn hw1mono h
    have hw2z : w2 = z := by
      by_contra h
      exact no_two_of_isolated hg hbound hzp hzn hw2mono h
    rw [hw1z] at hw1d
    rw [hw2z] at hw2d
    -- a neighbour `q` of `z`, lying off the geodesic
    have hz0 : z ≠ f 0 := fun h => hzp (h ▸ mem_pathSet (Nat.zero_le _))
    obtain ⟨g, hg2, hg20, hg2m⟩ := exists_geodesicSeq hc z (f 0)
    have hm : 1 ≤ G.dist z (f 0) := by
      rcases Nat.eq_zero_or_pos (G.dist z (f 0)) with h | h
      · rcases (dist_eq_zero_iff_eq_or_not_reachable).1 h with h' | h'
        · exact absurd h' hz0
        · exact absurd (hc.preconnected _ _) h'
      · exact h
    have hzq : G.Adj z (g 1) := hg20 ▸ hg2.adj hm
    have hqp : g 1 ∉ pathSet f D := by
      rw [not_mem_pathSet_iff]
      intro k hk hkq
      exact hzn k hk (hkq ▸ hzq)
    have hqnm : ¬ MonoOffPath G f D (g 1) := fun hq =>
      no_two_of_isolated hg hbound hzp hzn hq hzq.ne'
    obtain ⟨i, hi, hqi, hqi1⟩ := exists_consecutive_of_not_mono hg hqp hqnm
    -- distance estimates
    have hzi : G.dist z (f i) ≤ 2 := by
      have := (hzq.reachable).dist_triangle_left (f i)
      rw [dist_eq_one_iff_adj.2 hzq, dist_eq_one_iff_adj.2 hqi] at this
      exact this
    have hzi1 : G.dist z (f (i + 1)) ≤ 2 := by
      have := (hzq.reachable).dist_triangle_left (f (i + 1))
      rw [dist_eq_one_iff_adj.2 hzq, dist_eq_one_iff_adj.2 hqi1] at this
      exact this
    have tri1 : G.dist (f 1) z ≤ G.dist (f 1) (f (i + 1)) + G.dist (f (i + 1)) z :=
      Reachable.dist_triangle_left (hc.preconnected (f 1) (f (i + 1))) z
    have tri2 : G.dist (f (D - 1)) z ≤ G.dist (f (D - 1)) (f i) + G.dist (f i) z :=
      Reachable.dist_triangle_left (hc.preconnected (f (D - 1)) (f i)) z
    have tri3 : G.dist (f 1) z ≤ G.dist (f 1) (f i) + G.dist (f i) z :=
      Reachable.dist_triangle_left (hc.preconnected (f 1) (f i)) z
    rw [dist_comm] at hzi hzi1
    have d1 := hg.dist_eq' (i := 1) (j := i + 1) (by omega) (by omega)
    have d2 := hg.dist_eq' (i := D - 1) (j := i) (by omega) (by omega)
    have d3 := hg.dist_eq' (i := 1) (j := i) (by omega) (by omega)
    rw [hw1d] at tri1 tri3
    rw [hw2d] at tri2
    omega
  · -- Every vertex off the geodesic has a neighbour on it.
    push_neg at hF
    obtain ⟨j1, hj1, hadj1⟩ := hF w1 hw1p
    obtain ⟨j2, hj2, hadj2⟩ := hF w2 hw2p
    rw [hw1n j1 hj1 hadj1] at hadj1
    rw [hw2n j2 hj2 hadj2] at hadj2
    have hww : w1 ≠ w2 := by
      rintro rfl
      have := geodesic_nbr_span hg (k := D) (l := 0) (by omega) (by omega) hadj1 hadj2
      omega
    have hadjw : G.Adj w1 w2 := monoOffPath_adj hg hbound hw1mono hw2mono hww
    rcases Nat.lt_or_ge D 4 with hD4 | hD4
    · -- `D = 3`: the geodesic together with `w1` and `w2` is bipartite of order `D + 3`
      have hD3 : D = 3 := by omega
      subst hD3
      have hbip : G.BipFinset (insert w1 (insert w2 (pathSet f 3))) := by
        refine bipFinset_insert_pair hg (subset_refl _) hw1p hw2p 0 1 ?_ ?_ ?_
        · intro k hk _ hadj
          rw [hw1n k hk hadj]
          decide
        · intro k hk _ hadj
          rw [hw2n k hk hadj]
          decide
        · intro _
          decide
      have hcard : (insert w1 (insert w2 (pathSet f 3))).card = 6 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hw2p, card_pathSet hg]
        simp only [Finset.mem_insert, not_or]
        exact ⟨hww, hw1p⟩
      have := hbound _ hbip
      omega
    · -- `D ≥ 4`: the three edges `f 0 ~ w2 ~ w1 ~ f D` make `f 0` and `f D` too close
      have h1 : G.dist (f 0) (f D) ≤ 3 := by
        have t1 : G.dist (f 0) (f D) ≤ G.dist (f 0) w2 + G.dist w2 (f D) :=
          Reachable.dist_triangle_left (hc.preconnected (f 0) w2) (f D)
        have t2 : G.dist w2 (f D) ≤ G.dist w2 w1 + G.dist w1 (f D) :=
          Reachable.dist_triangle_left (hc.preconnected w2 w1) (f D)
        rw [dist_eq_one_iff_adj.2 hadj2.symm] at t1
        rw [dist_eq_one_iff_adj.2 hadjw.symm, dist_eq_one_iff_adj.2 hadj1] at t2
        omega
      have := hg.dist_eq 0 D (by omega) (by omega)
      omega

end SimpleGraph
