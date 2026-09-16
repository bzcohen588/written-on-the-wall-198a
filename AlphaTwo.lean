import RequestProject.PathTools

/-!
# Connected graphs with independence number at most two have a Hamiltonian path

This is the classical "longest path" argument: if `P` is a longest path and `v` a vertex outside
it, then `v` is adjacent to neither endpoint of `P`, so the two endpoints are adjacent (there is no
independent set of size three), `P` closes into a cycle, and connectivity then produces a longer
path — a contradiction.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-- A list of vertices which is duplicate-free and consists of consecutively adjacent vertices. -/
def IsPathList (G : SimpleGraph α) (l : List α) : Prop := l.Nodup ∧ l.IsChain G.Adj

omit [DecidableEq α] in
/-- There is a path list of maximum length. -/
theorem exists_maximal_pathList [Nonempty α] :
    ∃ l : List α, G.IsPathList l ∧ l ≠ [] ∧ ∀ m : List α, G.IsPathList m → m.length ≤ l.length := by
  classical
  set P : ℕ → Prop := fun n => ∃ l : List α, G.IsPathList l ∧ l.length = n with hP
  obtain ⟨v⟩ := ‹Nonempty α›
  have hP1 : P 1 := ⟨[v], ⟨by simp, by simp⟩, rfl⟩
  have h1card : 1 ≤ Fintype.card α := Fintype.card_pos
  set N := Nat.findGreatest P (Fintype.card α) with hN
  obtain ⟨l, hl, hlen⟩ : P N := Nat.findGreatest_spec h1card hP1
  have hNpos : 1 ≤ N := Nat.le_findGreatest h1card hP1
  refine ⟨l, hl, ?_, ?_⟩
  · intro h
    rw [h] at hlen
    simp at hlen
    omega
  · intro m hm
    have : m.length ≤ N :=
      Nat.le_findGreatest (hm.1.length_le_card) ⟨m, hm, rfl⟩
    omega

omit [Fintype α] [DecidableEq α] in
/-- If `G` is connected and `S` is a nonempty set of vertices which is not everything, then some
edge of `G` leaves `S`. -/
theorem exists_adj_outside (hc : G.Connected) {S : Finset α} {a z : α} (ha : a ∈ S) (hz : z ∉ S) :
    ∃ c ∈ S, ∃ w ∉ S, G.Adj c w := by
  obtain ⟨p⟩ := hc.preconnected a z
  obtain ⟨d, -, hd1, hd2⟩ :=
    p.exists_boundary_dart (S : Set α) (by simpa using ha) (by simpa using hz)
  exact ⟨d.toProd.1, by simpa using hd1, d.toProd.2, by simpa using hd2, d.adj⟩

/-- **Connected graphs with no independent set of size three have a Hamiltonian path.** -/
theorem exists_hamiltonian_of_indep_le_two (hc : G.Connected)
    (h3 : ∀ a b c : α, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hne' : Nonempty α := hc.nonempty
  obtain ⟨l, hl, hlne, hmax⟩ := exists_maximal_pathList (G := G)
  obtain ⟨hnodup, hchain⟩ := hl
  refine exists_hamiltonian_of_list hlne hchain hnodup ?_
  by_contra hcov
  push_neg at hcov
  obtain ⟨z, hz⟩ := hcov
  obtain ⟨v1, hv1⟩ : ∃ a, l.head? = some a := by
    cases l with
    | nil => exact absurd rfl hlne
    | cons a t => exact ⟨a, rfl⟩
  obtain ⟨vk, hvk⟩ : ∃ a, l.getLast? = some a := ⟨l.getLast hlne, List.getLast?_eq_some_getLast _⟩
  have hv1mem : v1 ∈ l := List.mem_of_mem_head? hv1
  have hvkmem : vk ∈ l := List.mem_of_mem_getLast? hvk
  -- the endpoints are not adjacent to `z`
  have hnz1 : ¬ G.Adj z v1 := by
    intro hadj
    have hpl : G.IsPathList (z :: l) :=
      ⟨List.nodup_cons.2 ⟨hz, hnodup⟩, List.isChain_cons.2 ⟨by
        intro y hy
        rw [hv1] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        exact hy ▸ hadj, hchain⟩⟩
    have := hmax _ hpl
    simp at this
  have hnzk : ¬ G.Adj vk z := by
    intro hadj
    have hpl : G.IsPathList (l ++ [z]) := by
      refine ⟨List.nodup_append.2 ⟨hnodup, by simp, ?_⟩, List.isChain_append.2 ⟨hchain, by simp, ?_⟩⟩
      · rintro a ha b hb rfl
        simp only [List.mem_singleton] at hb
        exact hz (hb ▸ ha)
      · intro x hx y hy
        rw [hvk] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        exact hx ▸ hy ▸ hadj
    have := hmax _ hpl
    simp at this
  -- `l` has at least two vertices
  rcases eq_or_ne v1 vk with hvv | hvv
  · -- a single-vertex path: connectivity gives a longer one
    have hlone : ∀ y ∈ l, y = v1 := by
      intro y hy
      by_contra hyne
      -- `l` has a head `v1` and last `vk = v1`, so a second vertex would repeat `v1`
      obtain ⟨t, rfl⟩ : ∃ t, l = v1 :: t := by
        cases l with
        | nil => exact absurd rfl hlne
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at hv1
          exact ⟨t, by rw [hv1]⟩
      have htne : t ≠ [] := by
        rintro rfl
        simp at hy
        exact hyne hy
      have : (v1 :: t).getLast? = t.getLast? := by
        cases t with
        | nil => exact absurd rfl htne
        | cons b s => simp [List.getLast?_cons_cons]
      rw [this, ← hvv] at hvk
      exact (List.nodup_cons.1 hnodup).1 (List.mem_of_mem_getLast? hvk)
    obtain ⟨c, hcmem, w, hw, hadj⟩ :=
      exists_adj_outside hc (S := l.toFinset) (a := v1) (by simpa using hv1mem) (by simpa using hz)
    rw [List.mem_toFinset] at hcmem
    rw [List.mem_toFinset] at hw
    have hcv1 : c = v1 := hlone c hcmem
    have hpl : G.IsPathList (w :: l) :=
      ⟨List.nodup_cons.2 ⟨hw, hnodup⟩, List.isChain_cons.2 ⟨by
        intro y hy
        rw [hv1] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        exact hy ▸ hcv1 ▸ hadj.symm, hchain⟩⟩
    have := hmax _ hpl
    simp at this
  · -- the endpoints are adjacent, so `l` closes into a cycle
    have hzv1 : z ≠ v1 := fun h => hz (h ▸ hv1mem)
    have hzvk : z ≠ vk := fun h => hz (h ▸ hvkmem)
    have hcycle : G.Adj v1 vk := by
      rcases h3 v1 vk z hvv (Ne.symm hzv1) (Ne.symm hzvk) with h | h | h
      · exact h
      · exact absurd h.symm hnz1
      · exact absurd h hnzk
    obtain ⟨c, hcmem, w, hw, hadj⟩ :=
      exists_adj_outside hc (S := l.toFinset) (a := v1) (by simpa using hv1mem) (by simpa using hz)
    rw [List.mem_toFinset] at hcmem
    rw [List.mem_toFinset] at hw
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hcmem
    have hperm : ((c :: B) ++ A).Perm l := by
      rw [hAB]; exact List.perm_append_comm
    have hmemiff : ∀ y, y ∈ (c :: B) ++ A ↔ y ∈ l := fun y => hperm.mem_iff
    have hchainAB : ((c :: B) ++ A).IsChain G.Adj := by
      rw [hAB, List.isChain_append] at hchain
      obtain ⟨hA, hcB, hcross⟩ := hchain
      refine List.isChain_append.2 ⟨hcB, hA, ?_⟩
      intro x hx y hy
      have hxk : x = vk := by
        have hx' : l.getLast? = some x := by
          rw [hAB, List.getLast?_append, Option.mem_def.1 hx]; rfl
        rw [hvk] at hx'
        exact (Option.some.inj hx').symm
      have hy1 : y = v1 := by
        have hy' : l.head? = some y := by
          rw [hAB, List.head?_append, Option.mem_def.1 hy]; rfl
        rw [hv1] at hy'
        exact (Option.some.inj hy').symm
      exact hxk ▸ hy1 ▸ hcycle.symm
    have hpl : G.IsPathList (w :: ((c :: B) ++ A)) := by
      refine ⟨List.nodup_cons.2 ⟨fun h => hw ((hmemiff w).1 h), hperm.nodup_iff.2 hnodup⟩, ?_⟩
      refine List.isChain_cons.2 ⟨?_, hchainAB⟩
      intro y hy
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      exact hy ▸ hadj.symm
    have hlen := hmax _ hpl
    rw [List.length_cons, hperm.length_eq] at hlen
    omega

end SimpleGraph
