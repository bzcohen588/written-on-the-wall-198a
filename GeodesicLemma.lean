import RequestProject.PathTools

/-!
# The geodesic lemma

This file proves the main ingredient of the paper (Ben Cohen, *Average Eccentricity, Induced
Bipartite Subgraphs, and Hamiltonian Paths*, v0.1, Lemma 2):

> If a connected graph `G` has no Hamiltonian path, then `b G ≥ ecc v + 2` for every vertex `v`.

The proof is by contradiction: if every induced bipartite subgraph has at most `ecc v + 1`
vertices, then a geodesic starting at `v` can be fattened into a Hamiltonian path.
-/

namespace SimpleGraph

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} {f : ℕ → α} {e : ℕ}
  {x y : α} {i j : ℕ}

section Core

variable (hg : IsGeodesicSeq G f e)
  (hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ e + 1)

include hg hbound

omit [Fintype α] in
/-- Every vertex off the geodesic has neighbours of both parities on it. -/
theorem exists_neighbor_parity (hx : x ∉ pathSet f e) :
    (∃ k ≤ e, G.Adj x (f k) ∧ k % 2 = 0) ∧ (∃ k ≤ e, G.Adj x (f k) ∧ k % 2 = 1) := by
  classical
  have hcard : (insert x (pathSet f e)).card = e + 2 := by
    rw [Finset.card_insert_of_notMem hx, card_pathSet hg]
  have key : ∀ c : Fin 2, (∀ k ≤ e, G.Adj x (f k) → c ≠ idxColor k) → False := by
    intro c hc
    have hbip := bipFinset_insert_pair hg (t := pathSet f e) (subset_refl _) hx hx c c
      (fun k hk _ hadj => hc k hk hadj) (fun k hk _ hadj => hc k hk hadj)
      (fun hadj => absurd hadj (G.irrefl))
    rw [Finset.insert_idem] at hbip
    have := hbound _ hbip
    rw [hcard] at this
    omega
  constructor
  · by_contra hcon
    push_neg at hcon
    refine key 0 fun k hk hadj => ?_
    have h2 := hcon k hk hadj
    simp [idxColor, h2]
  · by_contra hcon
    push_neg at hcon
    refine key 1 fun k hk hadj => ?_
    have h2 := hcon k hk hadj
    have : k % 2 = 0 := by omega
    simp [idxColor, this]

end Core

/-- `BlockPred G f e i x` says that `x` lies off the geodesic, is adjacent to `f i` and
`f (i + 1)`, and has no other neighbour on the geodesic except possibly `f (i - 1)`. -/
def BlockPred (G : SimpleGraph α) (f : ℕ → α) (e i : ℕ) (x : α) : Prop :=
  x ∉ pathSet f e ∧ G.Adj x (f i) ∧ G.Adj x (f (i + 1)) ∧
    ∀ k ≤ e, G.Adj x (f k) → (k + 1 = i ∨ k = i ∨ k = i + 1)

open Classical in
/-- The set `S i` of the paper: the vertices assigned to the index `i`. -/
noncomputable def blockSet (G : SimpleGraph α) (f : ℕ → α) (e i : ℕ) : Finset α :=
  Finset.univ.filter (fun x => BlockPred G f e i x)

theorem mem_blockSet_iff : x ∈ blockSet G f e i ↔ BlockPred G f e i x := by
  classical simp [blockSet]

section Core2

variable (hg : IsGeodesicSeq G f e)
  (hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ e + 1)

include hg

omit [Fintype α] in
/-- Every vertex off the geodesic is assigned to some index `i < e`. -/
theorem exists_blockPred (hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ e + 1)
    (hx : x ∉ pathSet f e) : ∃ i < e, BlockPred G f e i x := by
  classical
  obtain ⟨⟨k0, hk0, hadj0, hp0⟩, ⟨k1, hk1, hadj1, hp1⟩⟩ := exists_neighbor_parity hg hbound hx
  set N : Finset ℕ := (Finset.range (e + 1)).filter (fun k => G.Adj x (f k)) with hN
  have hmemN : ∀ k, k ∈ N ↔ (k ≤ e ∧ G.Adj x (f k)) := by
    intro k; simp [hN]
  have hne : N.Nonempty := ⟨k0, (hmemN k0).2 ⟨hk0, hadj0⟩⟩
  obtain ⟨hmle, hmadj⟩ := (hmemN _).1 (N.min'_mem hne)
  obtain ⟨hMle, hMadj⟩ := (hmemN _).1 (N.max'_mem hne)
  set m := N.min' hne with hm
  set M := N.max' hne with hM
  have hspan := geodesic_nbr_span hg hmle hMle hmadj hMadj
  have hbdd : ∀ k ≤ e, G.Adj x (f k) → m ≤ k ∧ k ≤ M := fun k hk hadj =>
    ⟨N.min'_le _ ((hmemN k).2 ⟨hk, hadj⟩), N.le_max' _ ((hmemN k).2 ⟨hk, hadj⟩)⟩
  obtain ⟨h0m, h0M⟩ := hbdd k0 hk0 hadj0
  obtain ⟨h1m, h1M⟩ := hbdd k1 hk1 hadj1
  have hMm : M = m + 1 ∨ M = m + 2 := by omega
  rcases hMm with hMm | hMm
  · refine ⟨m, by omega, hx, hmadj, ?_, ?_⟩
    · rw [← hMm]; exact hMadj
    · intro k hk hadj
      have := hbdd k hk hadj
      omega
  · have hmid : G.Adj x (f (m + 1)) := by
      have : k0 = m + 1 ∨ k1 = m + 1 := by omega
      rcases this with h | h
      · rw [← h]; exact hadj0
      · rw [← h]; exact hadj1
    refine ⟨m + 1, by omega, hx, hmid, ?_, ?_⟩
    · have : m + 1 + 1 = M := by omega
      rw [this]; exact hMadj
    · intro k hk hadj
      have := hbdd k hk hadj
      omega

omit [Fintype α] hg in
/-- The index assigned to a vertex off the geodesic is unique. -/
theorem blockPred_unique (hi : i < e) (hj : j < e) (h1 : BlockPred G f e i x)
    (h2 : BlockPred G f e j x) : i = j := by
  have hA := h2.2.2.2 i (by omega) h1.2.1
  have hB := h1.2.2.2 (j + 1) (by omega) h2.2.2.1
  have hC := h2.2.2.2 (i + 1) (by omega) h1.2.2.1
  omega

include hbound in
omit [Fintype α] in
/-- Each block `S i` is a clique. -/
theorem blockPred_adj (hi : i < e) (h1 : BlockPred G f e i x) (h2 : BlockPred G f e i y)
    (hxy : x ≠ y) : G.Adj x y := by
  classical
  by_contra hadj
  obtain ⟨hx, hxi, hxi1, hxk⟩ := h1
  obtain ⟨hy, hyi, hyi1, hyk⟩ := h2
  set t := (pathSet f e).erase (f i) with ht
  have hts : t ⊆ pathSet f e := Finset.erase_subset _ _
  have hxt : x ∉ t := fun h => hx (hts h)
  have hyt : y ∉ t := fun h => hy (hts h)
  have hcolor : ∀ z : α, (∀ k ≤ e, G.Adj z (f k) → (k + 1 = i ∨ k = i ∨ k = i + 1)) →
      ∀ k ≤ e, f k ∈ t → G.Adj z (f k) → idxColor i ≠ idxColor k := by
    intro z hz k hk hmem hadjk
    have hki : k ≠ i := fun h => (Finset.mem_erase.1 hmem).1 (by rw [h])
    have := hz k hk hadjk
    rw [idxColor_ne_iff_parity]
    omega
  have hbip := bipFinset_insert_pair hg hts hx hy (idxColor i) (idxColor i)
    (hcolor x hxk) (hcolor y hyk) (fun h => absurd h hadj)
  have h3c : t.card = e := by
    rw [ht, Finset.card_erase_of_mem (mem_pathSet (le_of_lt hi)), card_pathSet hg]
    omega
  have h1c : (insert y t).card = t.card + 1 := Finset.card_insert_of_notMem hyt
  have h2c : (insert x (insert y t)).card = (insert y t).card + 1 :=
    Finset.card_insert_of_notMem (by simp [hxy, hxt])
  have := hbound _ hbip
  omega

include hbound in
/-- The list `f i, [S i], f (i+1), [S (i+1)], …, f e` exists, is a chain of adjacent vertices, is
duplicate-free, and contains exactly the vertices it should. -/
theorem exists_suffix_list :
    ∀ i ≤ e, ∃ l : List α, l.IsChain G.Adj ∧ l.Nodup ∧ l.head? = some (f i) ∧
      ∀ z : α, z ∈ l ↔ ((∃ k, i ≤ k ∧ k ≤ e ∧ z = f k) ∨
        (∃ k, i ≤ k ∧ k < e ∧ z ∈ blockSet G f e k)) := by
  classical
  have hbase : ∃ l : List α, l.IsChain G.Adj ∧ l.Nodup ∧ l.head? = some (f e) ∧
      ∀ z : α, z ∈ l ↔ ((∃ k, e ≤ k ∧ k ≤ e ∧ z = f k) ∨
        (∃ k, e ≤ k ∧ k < e ∧ z ∈ blockSet G f e k)) := by
    refine ⟨[f e], by simp, by simp, by simp, ?_⟩
    intro z
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact Or.inl ⟨e, le_rfl, le_rfl, rfl⟩
    · rintro (⟨k, hk1, hk2, rfl⟩ | ⟨k, hk1, hk2, -⟩)
      · congr 1
        omega
      · omega
  have key : ∀ d i, i ≤ e → e - i ≤ d → ∃ l : List α, l.IsChain G.Adj ∧ l.Nodup ∧
      l.head? = some (f i) ∧ ∀ z : α, z ∈ l ↔ ((∃ k, i ≤ k ∧ k ≤ e ∧ z = f k) ∨
        (∃ k, i ≤ k ∧ k < e ∧ z ∈ blockSet G f e k)) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      obtain rfl : i = e := by omega
      exact hbase
    | succ d ih =>
      intro i hi hd
      rcases eq_or_lt_of_le hi with rfl | hie
      · exact hbase
      obtain ⟨l', hchain', hnodup', hhead', hmem'⟩ := ih (i + 1) (by omega) (by omega)
      set B := (blockSet G f e i).toList with hB
      have hBmem : ∀ z, z ∈ B ↔ z ∈ blockSet G f e i := by
        intro z; simp [hB]
      have hadjfi : ∀ z ∈ B, G.Adj z (f i) := fun z hz =>
        (mem_blockSet_iff.1 ((hBmem z).1 hz)).2.1
      have hadjfi1 : ∀ z ∈ B, G.Adj z (f (i + 1)) := fun z hz =>
        (mem_blockSet_iff.1 ((hBmem z).1 hz)).2.2.1
      have hoff : ∀ z ∈ B, z ∉ pathSet f e := fun z hz =>
        (mem_blockSet_iff.1 ((hBmem z).1 hz)).1
      have hBchain : B.IsChain G.Adj := by
        refine isChain_adj_toList ?_
        intro a ha bb hbb hab
        exact blockPred_adj hg hbound hie (mem_blockSet_iff.1 (by simpa using ha))
          (mem_blockSet_iff.1 (by simpa using hbb)) hab
      have hfi_notl' : f i ∉ l' := by
        rw [hmem']
        rintro (⟨k, hk1, hk2, hEq⟩ | ⟨k, hk1, hk2, hmemb⟩)
        · exact absurd (hg.injOn (le_of_lt hie) hk2 hEq) (by omega)
        · exact (mem_blockSet_iff.1 hmemb).1 (mem_pathSet (le_of_lt hie))
      refine ⟨(f i :: B) ++ l', ?_, ?_, by simp, ?_⟩
      · rw [List.isChain_append]
        refine ⟨?_, hchain', ?_⟩
        · rw [List.isChain_cons]
          exact ⟨fun y hy => (hadjfi y (List.mem_of_mem_head? hy)).symm, hBchain⟩
        · intro u hu v hv
          simp only [hhead', Option.mem_def, Option.some.injEq] at hv
          subst hv
          rcases List.mem_cons.1 (List.mem_of_mem_getLast? hu) with rfl | hu''
          · exact hg.adj hie
          · exact hadjfi1 u hu''
      · rw [List.cons_append, List.nodup_cons]
        refine ⟨?_, ?_⟩
        · rw [List.mem_append]
          rintro (hmemB | hmeml')
          · exact hoff _ hmemB (mem_pathSet (le_of_lt hie))
          · exact hfi_notl' hmeml'
        · rw [List.nodup_append]
          refine ⟨by simpa [hB] using Finset.nodup_toList _, hnodup', ?_⟩
          rintro a ha bb hbb rfl
          rw [hmem'] at hbb
          rcases hbb with ⟨k, hk1, hk2, hEq⟩ | ⟨k, hk1, hk2, hmemb⟩
          · exact hoff a ha (hEq ▸ mem_pathSet hk2)
          · have := blockPred_unique hie hk2 (mem_blockSet_iff.1 ((hBmem a).1 ha))
              (mem_blockSet_iff.1 hmemb)
            omega
      · intro z
        rw [List.cons_append, List.mem_cons, List.mem_append, hmem']
        constructor
        · rintro (rfl | hzB | ⟨k, hk1, hk2, rfl⟩ | ⟨k, hk1, hk2, hk3⟩)
          · exact Or.inl ⟨i, le_rfl, le_of_lt hie, rfl⟩
          · exact Or.inr ⟨i, le_rfl, hie, (hBmem z).1 hzB⟩
          · exact Or.inl ⟨k, by omega, hk2, rfl⟩
          · exact Or.inr ⟨k, by omega, hk2, hk3⟩
        · rintro (⟨k, hk1, hk2, rfl⟩ | ⟨k, hk1, hk2, hk3⟩)
          · rcases eq_or_lt_of_le hk1 with rfl | hlt
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl ⟨k, by omega, hk2, rfl⟩))
          · rcases eq_or_lt_of_le hk1 with rfl | hlt
            · exact Or.inr (Or.inl ((hBmem z).2 hk3))
            · exact Or.inr (Or.inr (Or.inr ⟨k, by omega, hk2, hk3⟩))
  intro i hi
  exact key (e - i) i hi le_rfl

include hbound in
/-- If every induced bipartite subgraph of `G` has at most `e + 1` vertices, where `e` is the
length of a geodesic of `G`, then `G` has a Hamiltonian path. -/
theorem exists_hamiltonian_of_bipBound (he : 1 ≤ e) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨l, hchain, hnodup, hhead, hmem⟩ := exists_suffix_list hg hbound 0 (by omega)
  refine exists_hamiltonian_of_list (l := l) ?_ hchain hnodup ?_
  · intro hl
    rw [hl] at hhead
    simp at hhead
  · intro z
    rw [hmem]
    by_cases hz : z ∈ pathSet f e
    · obtain ⟨k, hk, hkz⟩ := mem_pathSet_iff.1 hz
      exact Or.inl ⟨k, by omega, hk, hkz.symm⟩
    · obtain ⟨i, hi, hbp⟩ := exists_blockPred hg hbound hz
      exact Or.inr ⟨i, by omega, hi, mem_blockSet_iff.2 hbp⟩

end Core2

/-- **The geodesic lemma** (Cohen, Lemma 2). If `G` is connected and has no Hamiltonian path,
then `G` has an induced bipartite subgraph on `ecc v + 2` vertices, for every vertex `v`. -/
theorem geodesic_lemma (hc : G.Connected) (v : α)
    (hno : ¬ ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) :
    G.natEccentricity v + 2 ≤ G.largestInducedBipartiteSubgraphSize := by
  by_contra hcon
  push_neg at hcon
  have hbound : ∀ s : Finset α, G.BipFinset s → s.card ≤ G.natEccentricity v + 1 := fun s hs =>
    le_trans (card_le_largestInducedBipartiteSubgraphSize hs) (by omega)
  -- `e = 0` would force the graph to be a single vertex, which has a Hamiltonian path.
  have : Nonempty α := ⟨v⟩
  obtain ⟨u, hu⟩ := G.exists_dist_eq_natEccentricity (α := α) v
  rcases Nat.eq_zero_or_pos (G.natEccentricity v) with he | he
  · refine hno ⟨v, v, Walk.nil, ?_⟩
    have hsub : Subsingleton α := by
      constructor
      intro a b
      have ha : G.dist v a = 0 := le_antisymm (he ▸ G.dist_le_natEccentricity v a) (Nat.zero_le _)
      have hb : G.dist v b = 0 := le_antisymm (he ▸ G.dist_le_natEccentricity v b) (Nat.zero_le _)
      have := (dist_eq_zero_iff_eq_or_not_reachable (u := v) (v := a)).1 ha
      have hb' := (dist_eq_zero_iff_eq_or_not_reachable (u := v) (v := b)).1 hb
      rcases this with rfl | h1
      · rcases hb' with rfl | h2
        · rfl
        · exact absurd (hc.preconnected _ _) h2
      · exact absurd (hc.preconnected _ _) h1
    exact Walk.IsHamiltonian.of_subsingleton
  · obtain ⟨f, hg, hf0, hfe⟩ := exists_geodesicSeq hc v u
    rw [hu] at hg
    exact hno (exists_hamiltonian_of_bipBound hg hbound he)

end SimpleGraph
