module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity criteria for simple graphs

A criterion for connectivity that reduces to finitely many adjacency checks, convenient for fixed
small graphs such as Coxeter diagrams.

## Main statements

* `SimpleGraph.connected_of_exists_adj_rank_lt`: a graph is connected if, for some root and some
  rank function, every other vertex is adjacent to a vertex of smaller rank.
* `SimpleGraph.connected_of_exists_adj_lt`: a graph on `Fin (n + 1)` is connected if every
  nonzero vertex is adjacent to some smaller vertex.
-/

@[expose] public section

namespace SimpleGraph

/-- A graph is connected if, for some root `r` and rank function `rank`, every vertex other than
`r` is adjacent to a vertex of smaller rank: by strong induction on the rank, every vertex is then
reachable from `r`. -/
theorem connected_of_exists_adj_rank_lt {V : Type*} (G : SimpleGraph V) (r : V) (rank : V → ℕ)
    (h : ∀ i, i ≠ r → ∃ j, rank j < rank i ∧ G.Adj j i) : G.Connected := by
  have hr : ∀ k, ∀ i, rank i = k → G.Reachable r i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro i hik
        by_cases hi : i = r
        · rw [hi]
        · obtain ⟨j, hj, hadj⟩ := h i hi
          exact (ih (rank j) (hik ▸ hj) j rfl).trans hadj.reachable
  have : Nonempty V := ⟨r⟩
  exact ⟨fun u v ↦ (hr _ u rfl).symm.trans (hr _ v rfl)⟩

/-- A graph on `Fin (n + 1)` is connected if every nonzero vertex is adjacent to some smaller
vertex. -/
theorem connected_of_exists_adj_lt {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (h : ∀ i : Fin (n + 1), i ≠ 0 → ∃ j < i, G.Adj j i) : G.Connected :=
  G.connected_of_exists_adj_rank_lt 0 Fin.val fun i hi ↦
    let ⟨j, hj, hadj⟩ := h i hi
    ⟨j, hj, hadj⟩

end SimpleGraph
