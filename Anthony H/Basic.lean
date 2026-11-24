import Mathlib.Tactic.MinImports
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian


-- what is a circuit:
def IsCircuit {V : Type} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) : Prop :=
  w.support.length ≥ 2 ∧
  w.support.head? = w.support.getLast?

#eval [1,2,3,4].head?
#eval [1,2,3,4].getLast?
--p.head? returns the first item in the list, and p.getLast? returns the
-- last element of the list. This also works for trees, using nodes and leaves
-- instead of the #'s

-- an example of a single edge that works as a circuit
def singleEdge : SimpleGraph Bool := ⊤

-- old code, use to write the differences
---def singleEdge : Graph Bool where
--- Adj u v := u ≠ v
--- adj_symm := fun _ _ h => Ne.symm h

def singleEdgeWalk : singleEdge.Walk true true :=
  have h1 : singleEdge.Adj true false := by simp [singleEdge]
  have h2 : singleEdge.Adj false true := by simp [singleEdge]
  .cons h1 (.cons h2 .nil)

-- cannot traverse any edge more than once
-- but you can repeat the same node more than once if needed

-- Euler's circuit
-- requires that no edge is repeated and that every edge is used once
def walkEdges {V : Type} (p : List V) : List (Sym2 V) :=
  (p.zip p.tail).map (fun ab => s(ab.1, ab.2))

structure EulerCircuit {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  start : V
  target : V
  toWalk : G.Walk start target
  isCircuit : IsCircuit toWalk
  eachEdgeOnce : ∀ u v, G.Adj u v →
    (walkEdges toWalk.support).count s(u, v) = 1

-- proof that it has to be an even # of edges to make a circuit
--Math proof
-- assume C is a circuit in a graph G
-- pick any vtx to start
-- walk through a edge to another node, then leave through one more
-- notice that traversering the circuit, one in, one out, every single time,
-- (effectively, it is for any vtx v, the # of edges is 2v, which is always even)
-- at the end, the last edge that is used should be the edge used to go in
-- to the starting vtx,
-- hence it must be an even # of edges to make a circuit

-- example of eulers circuit
-- we use a triangle, by starting at an node, we go to one point,
-- from that point, we go to the other point, which uses the 2 edges of the
-- center node, the one used 2nd,
-- and then from the third node, we use the last remaining edge to go back
-- to the first node, showing that each node had only an even # of edges

def triangle : SimpleGraph (Fin 3) := ⊤

--def triangle : Graph (Fin 3) where
-- Adj u v := u ≠ v
-- adj_symm := fun _ _ h => Ne.symm h

def triangleWalk : triangle.Walk 0 0 :=
  have h01 : triangle.Adj 0 1 := by simp [triangle]
  have h12 : triangle.Adj 1 2 := by simp [triangle]
  have h20 : triangle.Adj 2 0 := by simp [triangle]
  .cons h01 (.cons h12 (.cons h20 .nil))

theorem triangleWalk_support : triangleWalk.support = [0, 1, 2, 0] := rfl

def triangleEuler : EulerCircuit triangle where
  start := 0
  target := 0
  toWalk := triangleWalk
  isCircuit := by
    unfold IsCircuit
    rw [triangleWalk_support]
    decide
  eachEdgeOnce := by
    intro u v h
    -- the following will prove that every edge is used once
    -- or in other words all pairs of distinct vertices are used exactly once
    have key : ∀ a b : Fin 3, a ≠ b →
        (walkEdges [0, 1, 2, 0]).count s(a, b) = 1 := by
      decide
    rw [triangleWalk_support]
    exact key u v (by simpa [triangle] using h)

-- next, hamiltonian cycles
-- unlike a Euler's circuit, which uses every edge once, a hamiltonian cycle
-- will hit every edge and vertex wihtout repeating any vertex.
-- the proof is that for a graph with of n vtx atleast 3 vtxs
-- if every vtx has atleast n/2 then it will have a hamiltonian cycle
-- the proof is usually a proof by contradiction
-- where assuming Ore's Thereom is false, which is that deg(u) +deg(v) ≥ n
-- for every pair of distinct non adj, vtx.

def IsHamiltonianWalk {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (vertices : List V) (w : G.Walk u v) : Prop :=
  IsCircuit w ∧ w.support.dropLast.Nodup ∧ w.support.dropLast.Perm vertices


def cyclicNext {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

structure GeneralHamiltonianCycle {V : Type} (adj : V → V → Prop) (n : Nat) where
  order : Fin n → V
  n_pos : 0 < n
  order_injective : ∀ i j, order i = order j → i = j
  every_vertex_appears : ∀ v, ∃ i, order i = v
  edge_to_next : ∀ i, adj (order i) (order (cyclicNext n_pos i))


/-- The triangle graph has a Hamiltonian cycle visiting `0`, `1`, and `2`. -/
def triangle_has_hamiltonian_cycle :
    GeneralHamiltonianCycle (fun x y : Fin 3 => x ≠ y) 3 := by
  exact {
    order := fun i => i
    n_pos := by decide
    order_injective := by
      intro i j h
      exact h
    every_vertex_appears := by
      intro v
      exact ⟨v, rfl⟩
    edge_to_next := by decide
  }

-- the difference here between the hamiltonian triangle and the eulers circuit triangle
-- is that the hamiltonian cycle tree shows that the 3 vtxs are distinct, and that
-- consecutive vtxs are connected, while the eulers proof focuses on
-- ensuring that every edge is used only once

--The square's perimeter visits every vertex once, but the graph also has a
--diagonal edge which the perimeter walk does not traverse. -/

def squareWithDiagonal : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(0, 2), s(1,3)}

-- the following 4 theroems are just there to
theorem sq_adj01 : squareWithDiagonal.Adj 0 1 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]
theorem sq_adj12 : squareWithDiagonal.Adj 1 2 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]
theorem sq_adj23 : squareWithDiagonal.Adj 2 3 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]
theorem sq_adj30 : squareWithDiagonal.Adj 3 0 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]
theorem sq_adj02 : squareWithDiagonal.Adj 0 2 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]
theorem sq_adj13 : squareWithDiagonal.Adj 1 3 := by
  simp [squareWithDiagonal, SimpleGraph.fromEdgeSet_adj]

def squarePerimeter : squareWithDiagonal.Walk 0 0 :=
  .cons sq_adj01 (.cons sq_adj12 (.cons sq_adj23 (.cons sq_adj30 .nil)))

theorem squarePerimeter_support : squarePerimeter.support = [0, 1, 2, 3, 0] := rfl

theorem square_perimeter_is_hamiltonian :
    IsHamiltonianWalk [0, 1, 2, 3] squarePerimeter := by
  simp [IsHamiltonianWalk, IsCircuit, squarePerimeter]

theorem square_perimeter_is_not_euler :
    ∀ c : EulerCircuit squareWithDiagonal,
      c.toWalk.support ≠ squarePerimeter.support := by
  intro c hc
  have hdiag := c.eachEdgeOnce 0 2 sq_adj02
  rw [hc, squarePerimeter_support] at hdiag
  simp [walkEdges] at hdiag
-- using s(1,3) would have also given a the same result
