import RequestProject.PathTools

/-!
# Hamiltonian paths in split graphs with a three-element independent side

The diameter-two case of the main theorem reduces to the following situation: the vertex set is
the disjoint union of three pairwise non-adjacent vertices `p, q, r` and a clique `K`, each of
`p, q, r` has at least two neighbours in `K`, and no vertex of `K` is adjacent to all three of
`p, q, r`. We show that such a graph has a Hamiltonian path.

The Hamiltonian path is built as an explicit list: a short pattern interleaving `p, q, r` with
suitable clique vertices, with the remaining clique vertices inserted between two consecutive
clique vertices of the pattern.
-/

namespace SimpleGraph

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} {p q r : α}

omit [Fintype α] in
/-- Inserting the remaining clique vertices between two lists produces a Hamiltonian path. -/
theorem exists_hamiltonian_of_sandwich {l₁ l₂ : List α} {t : Finset α}
    (hne : l₁ ++ l₂ ≠ []) (hnodup : (l₁ ++ l₂).Nodup)
    (hchain₁ : l₁.IsChain G.Adj) (hchain₂ : l₂.IsChain G.Adj)
    (hmid : ∀ w ∈ l₁.getLast?, ∀ y ∈ l₂.head?, G.Adj w y)
    (hlast : ∀ w ∈ l₁.getLast?, ∀ k ∈ t, G.Adj w k)
    (hhead : ∀ y ∈ l₂.head?, ∀ k ∈ t, G.Adj k y)
    (ht : (t : Set α).Pairwise G.Adj)
    (hdisj : ∀ x ∈ l₁ ++ l₂, x ∉ t)
    (hcov : ∀ v : α, v ∈ l₁ ++ l₂ ∨ v ∈ t) :
    ∃ a b : α, ∃ w : G.Walk a b, w.IsHamiltonian := by
  classical
  refine exists_hamiltonian_of_list (l := l₁ ++ t.toList ++ l₂) ?_ ?_ ?_ ?_
  · intro h
    apply hne
    have h1 : l₁ = [] ∧ l₂ = [] := by
      constructor <;>
        · apply List.eq_nil_of_subset_nil
          intro x hx
          rw [← h]
          simp_all
    simp [h1.1, h1.2]
  · -- chain
    rw [List.isChain_append]
    refine ⟨?_, hchain₂, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hchain₁, isChain_adj_toList ht, ?_⟩
      intro w hw k hk
      exact hlast w hw k (Finset.mem_toList.1 (List.mem_of_mem_head? hk))
    · intro w hw y hy
      rcases Finset.eq_empty_or_nonempty t with rfl | htne
      · simp only [Finset.toList_empty, List.append_nil] at hw
        exact hmid w hw y hy
      · have hwt : w ∈ t := by
          have : w ∈ l₁ ++ t.toList := List.mem_of_mem_getLast? hw
          rcases List.mem_append.1 this with h | h
          · exfalso
            -- the last element of `l₁ ++ t.toList` lies in `t.toList` since that list is nonempty
            have htl : t.toList ≠ [] := by
              simpa using htne.ne_empty
            rw [List.getLast?_append_of_ne_nil l₁ htl] at hw
            exact absurd (Finset.mem_toList.1 (List.mem_of_mem_getLast? hw)) (hdisj w
              (List.mem_append.2 (Or.inl h)))
          · exact Finset.mem_toList.1 h
        exact hhead y hy w hwt
  · -- nodup
    have h1 : (l₁ ++ l₂).Nodup := hnodup
    rw [List.nodup_append] at h1 ⊢
    refine ⟨?_, h1.2.1, ?_⟩
    · rw [List.nodup_append]
      refine ⟨h1.1, t.nodup_toList, ?_⟩
      intro a ha b hb hab
      exact hdisj a (List.mem_append.2 (Or.inl ha)) (hab ▸ Finset.mem_toList.1 hb)
    · intro a ha b hb
      rcases List.mem_append.1 ha with h | h
      · exact h1.2.2 a h b hb
      · intro hab
        exact hdisj b (List.mem_append.2 (Or.inr hb)) (hab ▸ Finset.mem_toList.1 h)
  · -- coverage
    intro v
    rcases hcov v with h | h
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl h)))
      · exact List.mem_append.2 (Or.inr h)
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (Finset.mem_toList.2 h))))

/-! ### The combinatorial core -/

omit [Fintype α] in
/-- Removing at most two elements from a finset drops its cardinality by at most two. -/
theorem card_sdiff_add_card_le (X s : Finset α) : X.card ≤ (X \ s).card + s.card := by
  classical
  calc X.card ≤ ((X \ s) ∪ s).card := Finset.card_le_card (by intro w hw; by_cases h : w ∈ s <;>
        simp [Finset.mem_union, hw, h])
    _ ≤ (X \ s).card + s.card := Finset.card_union_le _ _

omit [Fintype α] in
theorem sdiff_pair_eq (X : Finset α) (y z : α) :
    X \ ({y, z} : Finset α) = (X \ {y}) \ {z} := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

omit [Fintype α] in
theorem sdiff_singleton_eq_self {X : Finset α} {w : α} (hw : w ∉ X) :
    X \ ({w} : Finset α) = X := by
  rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hw]

omit [Fintype α] in
/-- A system of distinct representatives: two elements of `X`, one of `Y` and one of `Z`, all
distinct. -/
theorem exists_sdr {X Y Z : Finset α} (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card) (hZ : 2 ≤ Z.card)
    (hXY : 3 ≤ (X ∪ Y).card) (hXZ : 3 ≤ (X ∪ Z).card) (hU : 4 ≤ (X ∪ Y ∪ Z).card) :
    ∃ x₁ ∈ X, ∃ x₂ ∈ X, ∃ y ∈ Y, ∃ z ∈ Z,
      x₁ ≠ x₂ ∧ x₁ ≠ y ∧ x₁ ≠ z ∧ x₂ ≠ y ∧ x₂ ≠ z ∧ y ≠ z := by
  classical
  suffices h : ∃ y ∈ Y, ∃ z ∈ Z, y ≠ z ∧ 2 ≤ (X \ {y, z}).card by
    obtain ⟨y, hy, z, hz, hyz, hcard⟩ := h
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (X \ {y, z}).card)
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx₁ hx₂
    exact ⟨x₁, hx₁.1, x₂, hx₂.1, y, hy, z, hz, hne, hx₁.2.1, hx₁.2.2, hx₂.2.1, hx₂.2.2, hyz⟩
  have hsdne : ∀ A B : Finset α, ¬ A ⊆ B → (A \ B).Nonempty := fun A B h => Finset.sdiff_nonempty.2 h
  have hpaircard : ∀ y z : α, ({y, z} : Finset α).card ≤ 2 := fun y z =>
    le_trans (Finset.card_insert_le _ _) (by simp)
  rcases Nat.lt_or_ge X.card 4 with hX4 | hX4
  · rcases Nat.lt_or_ge X.card 3 with hX3 | hX3
    · -- `X.card = 2`: both chosen elements must avoid `X`
      have hXc : X.card = 2 := by omega
      have hYnsub : ¬ Y ⊆ X := by
        intro hsub
        rw [Finset.union_eq_left.2 hsub, hXc] at hXY
        omega
      have hZnsub : ¬ Z ⊆ X := by
        intro hsub
        rw [Finset.union_eq_left.2 hsub, hXc] at hXZ
        omega
      obtain ⟨y, hy⟩ := hsdne Y X hYnsub
      rw [Finset.mem_sdiff] at hy
      by_cases hz : ∃ z ∈ Z \ X, z ≠ y
      · obtain ⟨z, hz, hzy⟩ := hz
        rw [Finset.mem_sdiff] at hz
        refine ⟨y, hy.1, z, hz.1, fun h => hzy h.symm, ?_⟩
        rw [sdiff_pair_eq, sdiff_singleton_eq_self hy.2, sdiff_singleton_eq_self hz.2]
        omega
      · -- every element of `Z \ X` equals `y`, so we look for a second element of `Y \ X`
        push_neg at hz
        by_cases hy2 : ∃ y' ∈ Y \ X, y' ≠ y
        · obtain ⟨y', hy', hy'y⟩ := hy2
          rw [Finset.mem_sdiff] at hy'
          obtain ⟨z0, hz0⟩ := hsdne Z X hZnsub
          have hz0y : z0 = y := hz z0 hz0
          rw [Finset.mem_sdiff] at hz0
          refine ⟨y', hy'.1, z0, hz0.1, by rw [hz0y]; exact hy'y, ?_⟩
          rw [sdiff_pair_eq, sdiff_singleton_eq_self hy'.2, sdiff_singleton_eq_self hz0.2]
          omega
        · -- then `X ∪ Y ∪ Z ⊆ X ∪ {y}`, which is too small
          push_neg at hy2
          exfalso
          have hsub : X ∪ Y ∪ Z ⊆ insert y X := by
            intro w hw
            simp only [Finset.mem_union] at hw
            rcases hw with (hw | hw) | hw
            · exact Finset.mem_insert_of_mem hw
            · by_cases hwX : w ∈ X
              · exact Finset.mem_insert_of_mem hwX
              · exact Finset.mem_insert.2 (Or.inl (hy2 w (Finset.mem_sdiff.2 ⟨hw, hwX⟩)))
            · by_cases hwX : w ∈ X
              · exact Finset.mem_insert_of_mem hwX
              · exact Finset.mem_insert.2 (Or.inl (hz w (Finset.mem_sdiff.2 ⟨hw, hwX⟩)))
          have := Finset.card_le_card hsub
          have h2 := Finset.card_insert_le y X
          omega
    · -- `X.card = 3`: one of the two chosen elements must avoid `X`
      have hXc : X.card = 3 := by omega
      by_cases hYnsub : Y ⊆ X
      · by_cases hZnsub : Z ⊆ X
        · exfalso
          have hsub : X ∪ Y ∪ Z ⊆ X := by
            intro w hw
            simp only [Finset.mem_union] at hw
            rcases hw with (hw | hw) | hw
            · exact hw
            · exact hYnsub hw
            · exact hZnsub hw
          have := Finset.card_le_card hsub
          omega
        · obtain ⟨z, hz⟩ := hsdne Z X hZnsub
          rw [Finset.mem_sdiff] at hz
          obtain ⟨y, hy, hyz⟩ := Finset.exists_mem_ne (by omega : 1 < Y.card) z
          refine ⟨y, hy, z, hz.1, hyz, ?_⟩
          have hznot : z ∉ X \ ({y} : Finset α) := fun h => hz.2 (Finset.mem_sdiff.1 h).1
          rw [sdiff_pair_eq, sdiff_singleton_eq_self hznot]
          have := card_sdiff_add_card_le X ({y} : Finset α)
          simp only [Finset.card_singleton] at this
          omega
      · obtain ⟨y, hy⟩ := hsdne Y X hYnsub
        rw [Finset.mem_sdiff] at hy
        obtain ⟨z, hz, hzy⟩ := Finset.exists_mem_ne (by omega : 1 < Z.card) y
        refine ⟨y, hy.1, z, hz, fun h => hzy h.symm, ?_⟩
        rw [sdiff_pair_eq, sdiff_singleton_eq_self hy.2]
        have := card_sdiff_add_card_le X ({z} : Finset α)
        simp only [Finset.card_singleton] at this
        omega
  · -- `X.card ≥ 4`: any choice works
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < Y.card)
    obtain ⟨z, hz, hzy⟩ := Finset.exists_mem_ne (by omega : 1 < Z.card) y
    refine ⟨y, hy, z, hz, fun h => hzy h.symm, ?_⟩
    have := card_sdiff_add_card_le X ({y, z} : Finset α)
    have := hpaircard y z
    omega

section Split

variable (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
  (hclique : ∀ x y : α, x ≠ p → x ≠ q → x ≠ r → y ≠ p → y ≠ q → y ≠ r → x ≠ y → G.Adj x y)

include hpq hpr hqr hclique

omit hpq hpr hqr in
/-- The generic construction: a list through `p`, `q`, `r` and finitely many clique vertices,
with the remaining clique vertices inserted between the two lists. -/
theorem exists_hamiltonian_of_split_lists {l₁ l₂ : List α}
    (hne : l₁ ++ l₂ ≠ []) (hnodup : (l₁ ++ l₂).Nodup)
    (hchain₁ : l₁.IsChain G.Adj) (hchain₂ : l₂.IsChain G.Adj)
    (hmid : ∀ w ∈ l₁.getLast?, ∀ y ∈ l₂.head?, G.Adj w y)
    (hlast : ∀ w ∈ l₁.getLast?, w ≠ p ∧ w ≠ q ∧ w ≠ r)
    (hhead : ∀ y ∈ l₂.head?, y ≠ p ∧ y ≠ q ∧ y ≠ r)
    (hp : p ∈ l₁ ++ l₂) (hq : q ∈ l₁ ++ l₂) (hr : r ∈ l₁ ++ l₂) :
    ∃ x y : α, ∃ w : G.Walk x y, w.IsHamiltonian := by
  classical
  set t : Finset α := Finset.univ \ (l₁ ++ l₂).toFinset with htdef
  have hmem : ∀ k : α, k ∈ t ↔ k ∉ l₁ ++ l₂ := by
    intro k
    simp [htdef]
  have hnot : ∀ k ∈ t, k ≠ p ∧ k ≠ q ∧ k ≠ r := by
    intro k hk
    rw [hmem] at hk
    exact ⟨fun h => hk (h ▸ hp), fun h => hk (h ▸ hq), fun h => hk (h ▸ hr)⟩
  refine exists_hamiltonian_of_sandwich (t := t) hne hnodup hchain₁ hchain₂ hmid ?_ ?_ ?_ ?_ ?_
  · intro w hw k hk
    obtain ⟨h1, h2, h3⟩ := hlast w hw
    obtain ⟨h4, h5, h6⟩ := hnot k hk
    refine hclique w k h1 h2 h3 h4 h5 h6 ?_
    rintro rfl
    exact ((hmem w).1 hk) (List.mem_append.2 (Or.inl (List.mem_of_mem_getLast? hw)))
  · intro y hy k hk
    obtain ⟨h1, h2, h3⟩ := hhead y hy
    obtain ⟨h4, h5, h6⟩ := hnot k hk
    refine hclique k y h4 h5 h6 h1 h2 h3 ?_
    rintro rfl
    exact ((hmem k).1 hk) (List.mem_append.2 (Or.inr (List.mem_of_mem_head? hy)))
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    obtain ⟨h1, h2, h3⟩ := hnot x hx
    obtain ⟨h4, h5, h6⟩ := hnot y hy
    exact hclique x y h1 h2 h3 h4 h5 h6 hxy
  · intro x hx
    rw [hmem]
    exact fun h => h hx
  · intro v
    by_cases hv : v ∈ l₁ ++ l₂
    · exact Or.inl hv
    · exact Or.inr ((hmem v).2 hv)

/-- The pattern `p, a, [rest of the clique], b₁, q, b₂, c, r`: it needs four distinct clique
vertices, one adjacent to `p`, two adjacent to `q`, one adjacent to `r`. -/
theorem exists_hamiltonian_sdr {a b₁ b₂ c : α}
    (hnpq : ¬ G.Adj p q) (hnpr : ¬ G.Adj p r) (hnqr : ¬ G.Adj q r)
    (ha : G.Adj p a) (hb₁ : G.Adj q b₁) (hb₂ : G.Adj q b₂) (hc : G.Adj r c)
    (hab : a ≠ b₁) (hab2 : a ≠ b₂) (hac : a ≠ c) (hb12 : b₁ ≠ b₂) (hb1c : b₁ ≠ c)
    (hb2c : b₂ ≠ c) :
    ∃ x y : α, ∃ w : G.Walk x y, w.IsHamiltonian := by
  -- the four clique vertices avoid `p`, `q`, `r`
  have hap : a ≠ p := ha.ne'
  have haq : a ≠ q := fun h => hnpq (h ▸ ha)
  have har : a ≠ r := fun h => hnpr (h ▸ ha)
  have hb₁p : b₁ ≠ p := fun h => hnpq (h ▸ hb₁).symm
  have hb₁q : b₁ ≠ q := hb₁.ne'
  have hb₁r : b₁ ≠ r := fun h => hnqr (h ▸ hb₁)
  have hb₂p : b₂ ≠ p := fun h => hnpq (h ▸ hb₂).symm
  have hb₂q : b₂ ≠ q := hb₂.ne'
  have hb₂r : b₂ ≠ r := fun h => hnqr (h ▸ hb₂)
  have hcp : c ≠ p := fun h => hnpr (h ▸ hc).symm
  have hcq : c ≠ q := fun h => hnqr (h ▸ hc).symm
  have hcr : c ≠ r := hc.ne'
  refine exists_hamiltonian_of_split_lists hclique
    (l₁ := [p, a]) (l₂ := [b₁, q, b₂, c, r]) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp)
    (by simp)
  · simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Ne.symm, eq_comm]
  · simpa using ha
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hb₁.symm, hb₂, hclique b₂ c hb₂p hb₂q hb₂r hcp hcq hcr hb2c, hc.symm⟩
  · intro w hw y hy
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at hw
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hw
    subst hy
    exact hclique a b₁ hap haq har hb₁p hb₁q hb₁r hab
  · intro w hw
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at hw
    subst hw
    exact ⟨hap, haq, har⟩
  · intro y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact ⟨hb₁p, hb₁q, hb₁r⟩

/-- The pattern `p, k₃, q, k₁, r, k₂, [rest of the clique]`. -/
theorem exists_hamiltonian_triple {k₁ k₂ k₃ : α}
    (hnpq : ¬ G.Adj p q) (hnpr : ¬ G.Adj p r) (hnqr : ¬ G.Adj q r)
    (h₁ : G.Adj p k₃) (h₂ : G.Adj q k₃) (h₃ : G.Adj q k₁) (h₄ : G.Adj r k₁) (h₅ : G.Adj r k₂)
    (h12 : k₁ ≠ k₂) (h13 : k₁ ≠ k₃) (h23 : k₂ ≠ k₃) :
    ∃ x y : α, ∃ w : G.Walk x y, w.IsHamiltonian := by
  have hk₃p : k₃ ≠ p := h₁.ne'
  have hk₃q : k₃ ≠ q := h₂.ne'
  have hk₃r : k₃ ≠ r := fun h => hnqr (h ▸ h₂)
  have hk₁p : k₁ ≠ p := fun h => hnpq (h ▸ h₃).symm
  have hk₁q : k₁ ≠ q := h₃.ne'
  have hk₁r : k₁ ≠ r := h₄.ne'
  have hk₂p : k₂ ≠ p := fun h => hnpr (h ▸ h₅).symm
  have hk₂q : k₂ ≠ q := fun h => hnqr (h ▸ h₅).symm
  have hk₂r : k₂ ≠ r := h₅.ne'
  refine exists_hamiltonian_of_split_lists hclique
    (l₁ := [p, k₃, q, k₁, r, k₂]) (l₂ := []) (by simp) ?_ ?_ (by simp) (by simp) ?_ (by simp)
    (by simp) (by simp) (by simp)
  · simp only [List.append_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Ne.symm, eq_comm]
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨h₁, h₂.symm, h₃, h₄.symm, h₅⟩
  · intro w hw
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at hw
    subst hw
    exact ⟨hk₂p, hk₂q, hk₂r⟩

end Split

/-! ### The split-graph lemma -/

open Classical in
/-- The neighbourhood of a vertex, as a finset. -/
noncomputable def nbrs (G : SimpleGraph α) (v : α) : Finset α :=
  Finset.univ.filter (fun k => G.Adj v k)

omit [DecidableEq α] in
theorem mem_nbrs {v k : α} : k ∈ nbrs G v ↔ G.Adj v k := by
  classical
  simp [nbrs]

/-- The split-graph construction when the middle role is played by `q`: if the neighbourhood of
`q` together with each of the neighbourhoods of `p` and `r` is large enough, a system of distinct
representatives exists and yields a Hamiltonian path. -/
theorem exists_hamiltonian_of_split_mid {p q r : α} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hclique : ∀ x y : α, x ≠ p → x ≠ q → x ≠ r → y ≠ p → y ≠ q → y ≠ r → x ≠ y → G.Adj x y)
    (hnpq : ¬ G.Adj p q) (hnpr : ¬ G.Adj p r) (hnqr : ¬ G.Adj q r)
    (hp2 : 2 ≤ (nbrs G p).card) (hq2 : 2 ≤ (nbrs G q).card) (hr2 : 2 ≤ (nbrs G r).card)
    (hXY : 3 ≤ (nbrs G q ∪ nbrs G p).card) (hXZ : 3 ≤ (nbrs G q ∪ nbrs G r).card)
    (hU : 4 ≤ (nbrs G q ∪ nbrs G p ∪ nbrs G r).card) :
    ∃ x y : α, ∃ w : G.Walk x y, w.IsHamiltonian := by
  obtain ⟨b₁, hb₁, b₂, hb₂, a, ha, c, hc, h12, h1a, h1c, h2a, h2c, hac⟩ :=
    exists_sdr hq2 hp2 hr2 hXY hXZ hU
  exact exists_hamiltonian_sdr hpq hpr hqr hclique hnpq hnpr hnqr (mem_nbrs.1 ha)
    (mem_nbrs.1 hb₁) (mem_nbrs.1 hb₂) (mem_nbrs.1 hc) (Ne.symm h1a) (Ne.symm h2a) hac h12 h1c h2c

/-- **The split-graph lemma.** If the vertex set of `G` splits into three pairwise non-adjacent
vertices `p, q, r` and a clique, each of `p, q, r` has at least two neighbours, and no vertex is
adjacent to all of `p, q, r`, then `G` has a Hamiltonian path. -/
theorem exists_hamiltonian_of_split {p q r : α} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hclique : ∀ x y : α, x ≠ p → x ≠ q → x ≠ r → y ≠ p → y ≠ q → y ≠ r → x ≠ y → G.Adj x y)
    (hnpq : ¬ G.Adj p q) (hnpr : ¬ G.Adj p r) (hnqr : ¬ G.Adj q r)
    (hdp : ∃ k₁ k₂ : α, k₁ ≠ k₂ ∧ G.Adj p k₁ ∧ G.Adj p k₂)
    (hdq : ∃ k₁ k₂ : α, k₁ ≠ k₂ ∧ G.Adj q k₁ ∧ G.Adj q k₂)
    (hdr : ∃ k₁ k₂ : α, k₁ ≠ k₂ ∧ G.Adj r k₁ ∧ G.Adj r k₂)
    (hnouniv : ∀ k : α, ¬ (G.Adj k p ∧ G.Adj k q ∧ G.Adj k r)) :
    ∃ x y : α, ∃ w : G.Walk x y, w.IsHamiltonian := by
  classical
  set A := nbrs G p with hA
  set B := nbrs G q with hB
  set C := nbrs G r with hC
  -- the clique hypothesis is symmetric under permuting `p`, `q`, `r`
  have hcl_qpr : ∀ x y : α, x ≠ q → x ≠ p → x ≠ r → y ≠ q → y ≠ p → y ≠ r → x ≠ y → G.Adj x y :=
    fun x y h1 h2 h3 h4 h5 h6 h7 => hclique x y h2 h1 h3 h5 h4 h6 h7
  have hcl_prq : ∀ x y : α, x ≠ p → x ≠ r → x ≠ q → y ≠ p → y ≠ r → y ≠ q → x ≠ y → G.Adj x y :=
    fun x y h1 h2 h3 h4 h5 h6 h7 => hclique x y h1 h3 h2 h4 h6 h5 h7
  have hcard2 : ∀ (v : α), (∃ k₁ k₂ : α, k₁ ≠ k₂ ∧ G.Adj v k₁ ∧ G.Adj v k₂) →
      2 ≤ (nbrs G v).card := by
    rintro v ⟨k₁, k₂, hne, h1, h2⟩
    exact Finset.one_lt_card.2 ⟨k₁, mem_nbrs.2 h1, k₂, mem_nbrs.2 h2, hne⟩
  have hA2 : 2 ≤ A.card := hcard2 p hdp
  have hB2 : 2 ≤ B.card := hcard2 q hdq
  have hC2 : 2 ≤ C.card := hcard2 r hdr
  -- no vertex lies in all three neighbourhoods
  have hnot3 : ∀ k : α, k ∈ A → k ∈ B → k ∈ C → False := by
    intro k h1 h2 h3
    exact hnouniv k ⟨(mem_nbrs.1 h1).symm, (mem_nbrs.1 h2).symm, (mem_nbrs.1 h3).symm⟩
  have hdisj_card : ∀ S T : Finset α, S ∩ T = ∅ → (S ∪ T).card = S.card + T.card :=
    fun S T h => Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 h)
  have heq_of_small : ∀ S T : Finset α, 2 ≤ S.card → 2 ≤ T.card → (S ∪ T).card ≤ 2 → S = T := by
    intro S T hS hT hST
    have e1 : S = S ∪ T := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have e2 : T = S ∪ T := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact e1.trans e2.symm
  have h34 : ∀ S T : Finset α, 4 ≤ (S ∪ T).card → 3 ≤ (S ∪ T).card := fun S T h => by omega
  have hmono : ∀ S T U : Finset α, 4 ≤ (S ∪ T).card → 4 ≤ (S ∪ T ∪ U).card := by
    intro S T U h
    exact le_trans h (Finset.card_le_card Finset.subset_union_left)
  have hmono' : ∀ S T U : Finset α, 4 ≤ (S ∪ U).card → 4 ≤ (S ∪ T ∪ U).card := by
    intro S T U h
    refine le_trans h (Finset.card_le_card ?_)
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    tauto
  by_cases hAB : (A ∩ B).Nonempty
  · by_cases hBC : (B ∩ C).Nonempty
    · by_cases hCA : (C ∩ A).Nonempty
      · -- all three pairwise intersections are nonempty: use the interleaved pattern
        obtain ⟨k₃, hk₃⟩ := hAB
        obtain ⟨k₁, hk₁⟩ := hBC
        obtain ⟨k₂, hk₂⟩ := hCA
        rw [Finset.mem_inter] at hk₃ hk₁ hk₂
        refine exists_hamiltonian_triple hpq hpr hqr hclique hnpq hnpr hnqr
          (mem_nbrs.1 hk₃.1) (mem_nbrs.1 hk₃.2) (mem_nbrs.1 hk₁.1) (mem_nbrs.1 hk₁.2)
          (mem_nbrs.1 hk₂.1) ?_ ?_ ?_
        · rintro rfl
          exact hnot3 k₁ hk₂.2 hk₁.1 hk₁.2
        · rintro rfl
          exact hnot3 k₁ hk₃.1 hk₁.1 hk₁.2
        · rintro rfl
          exact hnot3 k₂ hk₂.2 hk₃.2 hk₂.1
      · -- `C ∩ A = ∅`
        rw [Finset.not_nonempty_iff_eq_empty] at hCA
        have h4CA : 4 ≤ (C ∪ A).card := by rw [hdisj_card C A hCA]; omega
        by_cases h3CB : 3 ≤ (C ∪ B).card
        · exact exists_hamiltonian_of_split_mid (p := p) (q := r) (r := q) hpr hpq hqr.symm
            hcl_prq hnpr hnpq (fun h => hnqr h.symm) hA2 hC2 hB2 (h34 _ _ h4CA) h3CB
            (hmono _ _ _ h4CA)
        · have hCB : C = B := heq_of_small C B hC2 hB2 (by omega)
          have hAB' : A ∩ B = ∅ := by
            rw [← hCB, Finset.inter_comm]
            exact hCA
          have h4AB : 4 ≤ (A ∪ B).card := by rw [hdisj_card A B hAB']; omega
          have h4AC : 4 ≤ (A ∪ C).card := by
            rw [hCB]
            exact h4AB
          exact exists_hamiltonian_of_split_mid (p := q) (q := p) (r := r) hpq.symm hqr hpr
            hcl_qpr (fun h => hnpq h.symm) hnqr hnpr hB2 hA2 hC2 (h34 _ _ h4AB) (h34 _ _ h4AC) (hmono _ _ _ h4AB)
    · -- `B ∩ C = ∅`
      rw [Finset.not_nonempty_iff_eq_empty] at hBC
      have h4BC : 4 ≤ (B ∪ C).card := by rw [hdisj_card B C hBC]; omega
      by_cases h3BA : 3 ≤ (B ∪ A).card
      · exact exists_hamiltonian_of_split_mid hpq hpr hqr hclique hnpq hnpr hnqr hA2 hB2 hC2
          h3BA (h34 _ _ h4BC) (hmono' _ _ _ h4BC)
      · have hBA : B = A := heq_of_small B A hB2 hA2 (by omega)
        have hAC : A ∩ C = ∅ := by rw [← hBA]; exact hBC
        have h4AC : 4 ≤ (A ∪ C).card := by rw [hdisj_card A C hAC]; omega
        have h4CA : 4 ≤ (C ∪ A).card := by rw [Finset.union_comm]; exact h4AC
        have h4CB : 4 ≤ (C ∪ B).card := by rw [hBA]; exact h4CA
        exact exists_hamiltonian_of_split_mid (p := p) (q := r) (r := q) hpr hpq hqr.symm
          hcl_prq hnpr hnpq (fun h => hnqr h.symm) hA2 hC2 hB2 (h34 _ _ h4CA) (h34 _ _ h4CB) (hmono _ _ _ h4CA)
  · -- `A ∩ B = ∅`
    rw [Finset.not_nonempty_iff_eq_empty] at hAB
    have h4AB : 4 ≤ (A ∪ B).card := by rw [hdisj_card A B hAB]; omega
    have h4BA : 4 ≤ (B ∪ A).card := by rw [Finset.union_comm]; exact h4AB
    by_cases h3BC : 3 ≤ (B ∪ C).card
    · exact exists_hamiltonian_of_split_mid hpq hpr hqr hclique hnpq hnpr hnqr hA2 hB2 hC2
        (h34 _ _ h4BA) h3BC (hmono _ _ _ h4BA)
    · have hBC : B = C := heq_of_small B C hB2 hC2 (by omega)
      have h4AC : 4 ≤ (A ∪ C).card := by rw [← hBC]; exact h4AB
      exact exists_hamiltonian_of_split_mid (p := q) (q := p) (r := r) hpq.symm hqr hpr
        hcl_qpr (fun h => hnpq h.symm) hnqr hnpr hB2 hA2 hC2 (h34 _ _ h4AB) (h34 _ _ h4AC) (hmono _ _ _ h4AB)

end SimpleGraph
