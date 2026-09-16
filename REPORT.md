# Written on the Wall II, Conjecture 198a — formalization report

## What is delivered

A complete, machine-checked Lean 4 proof of the Formal Conjectures target

```lean
theorem conjecture198a (G : SimpleGraph α) (h : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian
```

(with `variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]`), in
`RequestProject/Conjecture198a.lean`, namespace `WrittenOnTheWallII.GraphConjecture198a`.
The statement, the namespace, the variables and the invariants `SimpleGraph.b` and
`SimpleGraph.averageEccentricity` are reproduced verbatim from the Formal Conjectures file
`FormalConjectures/WrittenOnTheWallII/GraphConjecture198a.lean` (the definitions are copied,
with attribution, into `RequestProject/Defs.lean`, because this project depends on Mathlib
directly rather than on the Formal Conjectures utility library).

There are **no `sorry`s and no new axioms** anywhere in the project.

The informal source is Ben Cohen, *Average Eccentricity, Induced Bipartite Subgraphs, and
Hamiltonian Paths*, version 0.1 (July 21, 2026), supplied with the request; the file headers
record the attribution. Section 2 of the paper (the geodesic lemma) is formalized as given;
Section 3 is proved by a different, self-contained route, see "Departures" below.

## Versions and how to check

* Toolchain: `leanprover/lean4:v4.28.0` (`lean-toolchain`).
* Mathlib: `https://github.com/leanprover-community/mathlib4.git`, revision
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (pinned in `lake-manifest.json`; `lakefile.toml`
  requires tag `v4.28.0`).
* This is a **documented port**: the upstream Formal Conjectures repository is built against a
  different toolchain, so the statement was re-established against the Lean/Mathlib versions
  pinned here. No other change to the statement was made.

Commands used:

```
lake build                                 # builds all RequestProject.* modules
lake env lean RequestProject/<File>.lean   # checks a single file
```

`lake build` completes with no errors and no warnings.

## Axiom report

```
#print axioms WrittenOnTheWallII.GraphConjecture198a.conjecture198a
  → depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms SimpleGraph.geodesic_lemma
  → depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same holds for every intermediate result, e.g.

```
#print axioms SimpleGraph.selfCentered_bipartite_ge      → [propext, Classical.choice, Quot.sound]
#print axioms SimpleGraph.exists_hamiltonian_of_diam_two → [propext, Classical.choice, Quot.sound]
#print axioms SimpleGraph.exists_hamiltonian_of_split    → [propext, Classical.choice, Quot.sound]
#print axioms SimpleGraph.exists_hamiltonian_of_indep_le_two
                                                         → [propext, Classical.choice, Quot.sound]
```

No `native_decide`, `decide`-on-large-terms, `implemented_by` or trust-extending features are
used; the proofs are ordinary kernel-checkable terms.

## Dependency audit

Both external results named in the brief were checked for availability in the pinned
dependencies and **neither is present in Mathlib** at the pinned revision:

* **DeLaViña–Pepper–Waller radius bound `b(G) ≥ 2·rad(G)`** (and the induced-path theorem it
  relies on): not in Mathlib. Not assumed here.
* **Chvátal–Erdős path theorem** (`s = 2` case: a 2-connected graph with no independent set of
  four vertices has a Hamiltonian path): not in Mathlib. Not assumed here.

Neither is postulated as an axiom or as a hypothesis of the main theorem. Both uses were
replaced by self-contained proofs, described next.

## Departures from the paper's Section 3

After the geodesic lemma the argument shows that the graph is *self-centered*: every
eccentricity equals the diameter `D`, and `b(G) = D + 2`. The paper then uses the radius bound
to get `D ≤ 2`, and Chvátal–Erdős to finish the case `D = 2`. Here instead:

* `D ≥ 3` is excluded by `SimpleGraph.selfCentered_bipartite_ge`
  (`RequestProject/SelfCentered.lean`), proved from scratch: for a connected self-centered graph
  of diameter `D ≥ 3` one exhibits an induced bipartite subgraph on `D + 3` vertices, namely a
  geodesic plus two vertices whose neighbourhoods on it are "monochromatic" for the parity
  colouring. This is strictly enough for the application (the radius bound would give
  `b(G) ≥ 2D ≥ D + 3` in this situation).
* `D = 1` gives a complete graph, handled by the longest-path argument below.
* `D = 2` is handled by `SimpleGraph.exists_hamiltonian_of_diam_two`
  (`RequestProject/DiamTwo.lean`) without Chvátal–Erdős. Since `b(G) = 4`, the graph has no
  independent set of four vertices, and moreover if `{p, q, r}` is independent then the other
  vertices form a clique. Two cases:
  * no independent set of size three: the classical longest-path argument
    (`SimpleGraph.exists_hamiltonian_of_indep_le_two`, `RequestProject/AlphaTwo.lean`);
  * an independent `{p, q, r}` with a clique elsewhere (a split graph): an explicit Hamiltonian
    path is constructed (`SimpleGraph.exists_hamiltonian_of_split`,
    `RequestProject/SplitGraph.lean`) from the degree condition (every vertex has at least two
    neighbours, since the diameter is 2) and the fact that no vertex is adjacent to all of
    `p, q, r` (such a vertex would have eccentricity 1).

So: the theorem proved is exactly the requested one; Section 2 of the paper is formalized as
written, while Section 3 is replaced by the independent arguments above.

## File map

| File | Contents |
|---|---|
| `RequestProject/Defs.lean` | The Formal Conjectures definitions (`largestInducedBipartiteSubgraphSize`, `b`, `averageEccentricity`), the `Finset`-level bipartiteness predicate `BipFinset` with its equivalence to `(G.induce s).IsBipartite`, and a `ℕ`-valued eccentricity proved equal to `(G.eccent v).toNat` |
| `RequestProject/PathTools.lean` | Turning a chain of adjacent, duplicate-free vertices into a Hamiltonian path; geodesics as sequences `f : ℕ → α`, their existence and basic properties; parity colourings of a geodesic |
| `RequestProject/GeodesicLemma.lean` | **The geodesic lemma** (Cohen, Lemma 2): if `G` is connected and has no Hamiltonian path, then `ecc v + 2 ≤ b(G)` for every vertex `v`. Includes the parity, block-assignment, uniqueness and clique steps, and the assembly of the Hamiltonian path |
| `RequestProject/SelfCentered.lean` | Self-centered graphs of diameter `≥ 3` have an induced bipartite subgraph on `D + 3` vertices |
| `RequestProject/AlphaTwo.lean` | Connected graphs with no independent set of size three have a Hamiltonian path |
| `RequestProject/SplitGraph.lean` | Hamiltonian paths in split graphs with a three-element independent side |
| `RequestProject/DiamTwo.lean` | The diameter-two case |
| `RequestProject/Conjecture198a.lean` | The main theorem |
