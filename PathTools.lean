import RequestProject.Defs

/-!
# Tools for building Hamiltonian paths, and geodesics

This file contains two pieces of infrastructure used throughout the project.

* `SimpleGraph.exists_hamiltonian_of_list`: a duplicate-free list of vertices which covers all
  vertices and whose consecutive entries are adjacent yields a Hamiltonian path.
* `SimpleGraph.IsGeodesicSeq`: a geodesic, presented as a function `f : ℕ → α` such that
  `G.dist (f i) (f j) = j - i` for `i ≤ j ≤ n`, together with its existence
  (`SimpleGraph.exists_geodesicSeq`) and basic properties.
-/

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

/-! ### From lists to Hamiltonian paths -/

omit [DecidableEq α] in
theorem exists_walk_of_chain :
    ∀ (l : List α) (a : α), (a :: l).IsChain G.Adj →
      ∃ (b : α) (p : G.Walk a b), p.support = a :: l
  | [], a, _ => ⟨a, Walk.nil, rfl⟩
  | x :: t, a, h => by
    obtain ⟨hax, ht⟩ := List.isChain_cons_cons.1 h
    obtain ⟨b, q, hq⟩ := exists_walk_of_chain t x ht
    exact ⟨b, q.cons hax, by simp [hq]⟩

/-- A duplicate-free list of vertices covering every vertex, with consecutive entries adjacent,
gives rise to a Hamiltonian path. -/
theorem exists_hamiltonian_of_list {l : List α} (hne : l ≠ []) (hchain : l.IsChain G.Adj)
    (hnodup : l.Nodup) (hcov : ∀ v : α, v ∈ l) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  obtain ⟨b, p, hp⟩ := exists_walk_of_chain t a hchain
  refine ⟨a, b, p, ?_⟩
  have hpath : p.IsPath := Walk.IsPath.mk' (by rw [hp]; exact hnodup)
  exact hpath.isHamiltonian_of_mem fun w => by rw [hp]; exact hcov w

omit [DecidableEq α] in
/-- The elements of a clique, listed without repetition, form a chain of adjacent vertices. -/
theorem isChain_adj_toList {K : Finset α} (hK : (K : Set α).Pairwise G.Adj) :
    K.toList.IsChain G.Adj :=
  List.Pairwise.isChain <|
    K.nodup_toList.pairwise_of_forall_ne fun x hx y hy hxy =>
      hK (by simpa using hx) (by simpa using hy) hxy

/-! ### Geodesics -/

/-- `IsGeodesicSeq G f n` says that `f 0, f 1, …, f n` is a geodesic (shortest path) of `G`:
the distance between `f i` and `f j` is exactly `j - i` for `i ≤ j ≤ n`. -/
structure IsGeodesicSeq (G : SimpleGraph α) (f : ℕ → α) (n : ℕ) : Prop where
  dist_eq : ∀ i j, i ≤ j → j ≤ n → G.dist (f i) (f j) = j - i

namespace IsGeodesicSeq

variable {f : ℕ → α} {n : ℕ}

omit [DecidableEq α] in
theorem dist_eq' (h : IsGeodesicSeq G f n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    G.dist (f i) (f j) = (j - i) + (i - j) := by
  rcases le_total i j with hij | hij
  · rw [h.dist_eq i j hij hj]; omega
  · rw [dist_comm, h.dist_eq j i hij hi]; omega

omit [DecidableEq α] in
/-- Distinct indices give distinct vertices. -/
theorem injOn (h : IsGeodesicSeq G f n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hij : f i = f j) :
    i = j := by
  by_contra hne
  have := h.dist_eq' hi hj
  rw [hij, dist_self] at this
  omega

omit [DecidableEq α] in
/-- Consecutive vertices of a geodesic are adjacent. -/
theorem adj (h : IsGeodesicSeq G f n) {i : ℕ} (hi : i < n) : G.Adj (f i) (f (i + 1)) := by
  have h1 : G.dist (f i) (f (i + 1)) = 1 := by
    rw [h.dist_eq i (i + 1) (by omega) (by omega)]; omega
  exact (dist_eq_one_iff_adj (u := f i) (v := f (i + 1))).1 h1

omit [DecidableEq α] in
/-- A geodesic is an induced path: two of its vertices are adjacent only if their indices are
consecutive. -/
theorem adj_iff (h : IsGeodesicSeq G f n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    G.Adj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i) := by
  constructor
  · intro hadj
    have h1 : G.dist (f i) (f j) = 1 := (dist_eq_one_iff_adj).2 hadj
    have := h.dist_eq' hi hj
    omega
  · rintro (rfl | rfl)
    · exact h.adj (by omega)
    · exact (h.adj (i := j) (by omega)).symm

end IsGeodesicSeq

omit [DecidableEq α] in
/-- Every pair of vertices in a connected graph is joined by a geodesic. -/
theorem exists_geodesicSeq (hc : G.Connected) (u v : α) :
    ∃ f : ℕ → α, IsGeodesicSeq G f (G.dist u v) ∧ f 0 = u ∧ f (G.dist u v) = v := by
  set n := G.dist u v with hn
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  refine ⟨p.getVert, ⟨?_⟩, p.getVert_zero, by rw [hn, ← hp, p.getVert_length]⟩
  intro i j hij hj
  -- upper bound on `dist (f i) (f j)`
  have hle : G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
    have h1 : (p.drop i).getVert (j - i) = p.getVert j := by
      rw [Walk.drop_getVert]
      congr 1
      omega
    refine le_trans (SimpleGraph.dist_le (((p.drop i).take (j - i)).copy rfl h1)) ?_
    rw [Walk.length_copy, Walk.take_length]
    exact min_le_left _ _
  -- lower bound coming from `dist u v = n`
  have hui : G.dist u (p.getVert i) ≤ i := by
    have := SimpleGraph.dist_le (p.take i)
    rw [Walk.take_length] at this
    exact le_trans this (min_le_left _ _)
  have hjv : G.dist (p.getVert j) v ≤ n - j := by
    have := SimpleGraph.dist_le (p.drop j)
    rw [Walk.drop_length, hp] at this
    exact this
  have htri : G.dist u v ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) (p.getVert j)
      + G.dist (p.getVert j) v := by
    refine le_trans (hc.dist_triangle (v := p.getVert j)) ?_
    exact Nat.add_le_add_right (hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)) _
  omega

/-! ### The vertex set of a geodesic, and colourings by index parity -/

section PathSet

variable {f : ℕ → α} {n : ℕ} {x y : α} {k : ℕ}

/-- The vertex set of the geodesic `f 0, …, f n`. -/
def pathSet (f : ℕ → α) (n : ℕ) : Finset α := (Finset.range (n + 1)).image f

theorem mem_pathSet_iff : x ∈ pathSet f n ↔ ∃ k ≤ n, f k = x := by
  simp [pathSet]

theorem mem_pathSet (hk : k ≤ n) : f k ∈ pathSet f n := mem_pathSet_iff.2 ⟨k, hk, rfl⟩

theorem not_mem_pathSet_iff : x ∉ pathSet f n ↔ ∀ k ≤ n, f k ≠ x := by
  rw [mem_pathSet_iff]
  push_neg
  rfl

theorem card_pathSet (hg : IsGeodesicSeq G f n) : (pathSet f n).card = n + 1 := by
  rw [pathSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact hg.injOn (by omega) (by omega) hab

/-- The colour assigned to the geodesic vertex of index `k`. -/
def idxColor (k : ℕ) : Fin 2 := if k % 2 = 0 then 0 else 1

theorem idxColor_eq_iff_parity {k l : ℕ} : idxColor k = idxColor l ↔ k % 2 = l % 2 := by
  unfold idxColor
  have hk := Nat.mod_two_eq_zero_or_one k
  have hl := Nat.mod_two_eq_zero_or_one l
  rcases hk with hk | hk <;> rcases hl with hl | hl <;> simp [hk, hl]

theorem idxColor_ne_iff_parity {k l : ℕ} : idxColor k ≠ idxColor l ↔ k % 2 ≠ l % 2 :=
  not_congr idxColor_eq_iff_parity

omit [DecidableEq α] in
/-- The neighbours of a vertex on a geodesic span at most three consecutive indices. -/
theorem geodesic_nbr_span (hg : IsGeodesicSeq G f n) {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n)
    (h1 : G.Adj x (f k)) (h2 : G.Adj x (f l)) : k ≤ l + 2 ∧ l ≤ k + 2 := by
  have h3 : G.dist (f k) (f l) ≤ 2 := by
    have htri : G.dist (f k) (f l) ≤ G.dist (f k) x + G.dist x (f l) :=
      (h1.symm.reachable).dist_triangle_left (f l)
    rw [dist_eq_one_iff_adj.2 h1.symm, dist_eq_one_iff_adj.2 h2] at htri
    exact htri
  have := hg.dist_eq' hk hl
  omega

/-- Colouring a subset of a geodesic by index parity, together with two extra vertices with
prescribed colours, yields an induced bipartite subgraph. -/
theorem bipFinset_insert_pair (hg : IsGeodesicSeq G f n) {t : Finset α} (ht : t ⊆ pathSet f n)
    (hx : x ∉ pathSet f n) (hy : y ∉ pathSet f n) (cx cy : Fin 2)
    (hcx : ∀ k ≤ n, f k ∈ t → G.Adj x (f k) → cx ≠ idxColor k)
    (hcy : ∀ k ≤ n, f k ∈ t → G.Adj y (f k) → cy ≠ idxColor k)
    (hxy : G.Adj x y → cx ≠ cy) :
    G.BipFinset (insert x (insert y t)) := by
  classical
  set c : α → Fin 2 := fun z => if z = x then cx else if z = y then cy else
    (if ∃ k ≤ n, f k = z ∧ k % 2 = 0 then 0 else 1) with hc
  have hxt : x ∉ t := fun h => hx (ht h)
  have hyt : y ∉ t := fun h => hy (ht h)
  -- the colour of a vertex of `t`
  have hin : ∀ z ∈ t, ∃ k ≤ n, f k = z ∧ c z = idxColor k := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := mem_pathSet_iff.1 (ht hz)
    have hkx : f k ≠ x := fun h => hxt (h ▸ hz)
    have hky : f k ≠ y := fun h => hyt (h ▸ hz)
    refine ⟨k, hk, rfl, ?_⟩
    simp only [hc, if_neg hkx, if_neg hky, idxColor]
    by_cases hk2 : k % 2 = 0
    · rw [if_pos ⟨k, hk, rfl, hk2⟩, if_pos hk2]
    · rw [if_neg hk2, if_neg]
      rintro ⟨m, hm, hmk, hm2⟩
      exact hk2 (by rw [← hg.injOn hm hk hmk]; exact hm2)
  -- the colour of the two extra vertices
  have hout : ∀ z, (z = x ∨ z = y) → (c z = cx ∧ z = x) ∨ (c z = cy ∧ z = y) := by
    rintro z (rfl | rfl)
    · exact Or.inl ⟨by simp [hc], rfl⟩
    · by_cases h : z = x
      · exact Or.inl ⟨by simp [hc, h], h⟩
      · exact Or.inr ⟨by simp [hc, h], rfl⟩
  have hnotin : ∀ z ∈ insert x (insert y t), z ∉ t → z = x ∨ z = y := by
    intro z hz hzt
    simp only [Finset.mem_insert] at hz
    tauto
  refine ⟨c, ?_⟩
  intro u hu v hv huv
  by_cases hut : u ∈ t <;> by_cases hvt : v ∈ t
  · obtain ⟨k, hk, rfl, hck⟩ := hin u hut
    obtain ⟨l, hl, rfl, hcl⟩ := hin v hvt
    rw [hck, hcl, idxColor_ne_iff_parity]
    have := (hg.adj_iff hk hl).1 huv
    omega
  · obtain ⟨k, hk, rfl, hck⟩ := hin u hut
    rcases hout v (hnotin v hv hvt) with ⟨hcv, rfl⟩ | ⟨hcv, rfl⟩
    · rw [hck, hcv]
      exact fun h => hcx k hk hut huv.symm h.symm
    · rw [hck, hcv]
      exact fun h => hcy k hk hut huv.symm h.symm
  · obtain ⟨l, hl, rfl, hcl⟩ := hin v hvt
    rcases hout u (hnotin u hu hut) with ⟨hcu, rfl⟩ | ⟨hcu, rfl⟩
    · rw [hcl, hcu]
      exact hcx l hl hvt huv
    · rw [hcl, hcu]
      exact hcy l hl hvt huv
  · rcases hout u (hnotin u hu hut) with ⟨hcu, rfl⟩ | ⟨hcu, rfl⟩ <;>
      rcases hout v (hnotin v hv hvt) with ⟨hcv, rfl⟩ | ⟨hcv, rfl⟩
    · exact absurd rfl huv.ne
    · rw [hcu, hcv]; exact hxy huv
    · rw [hcu, hcv]; exact fun h => hxy huv.symm h.symm
    · exact absurd rfl huv.ne

end PathSet

end SimpleGraph
