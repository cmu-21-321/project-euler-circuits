import Mathlib.Tactic.MinImports
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian


-- what is a circuit:
structure Graph (V : Type) where
  Adj : V → V → Prop
  adj_symm : ∀ u v, Adj u v → Adj v u

-- This structure Graph is used because Mathlib's SimpleGraph does not include the
-- adj_symm part which I use in the single edges, the triangle case,
-- and the diagonal square

structure Walk {V : Type} (G : Graph V) where
  support : List V
  adj : ∀ (i : Nat) (h : i + 1 < support.length),
    G.Adj (support[i]'(by omega)) (support[i + 1]'h)

-- the structure Walk is defined here because the SimpleGraph.Walk structure
-- of mathlib has a type SimpleGraph, while the Walk's here have type Graph V

def IsCircuit {V : Type} {G : Graph V} (w : Walk G) : Prop :=
  w.support.length ≥ 2 ∧
  w.support.head? = w.support.getLast?

#eval [1,2,3,4].head?
#eval [1,2,3,4].getLast?
--p.head? returns the first item in the list, and p.getLast? returns the
-- last element of the list. This also works for trees, using nodes and leaves
-- instead of the #'s

-- an example of a single edge that works as a circuit

def singleEdge : Graph Bool where
  Adj u v := u ≠ v
  adj_symm := fun _ _ h => Ne.symm h

def singleEdgeWalk : Walk singleEdge where
  support := [true, false, true]
  adj := by
    intro i h
    have : i = 0 ∨ i = 1 := by
      simp at h
      omega
    rcases this with rfl | rfl <;> simp [singleEdge]

-- cannot traverse any edge more than once
-- but you can repeat the same node more than once if needed

-- Euler's circuit
-- requires that no edge is repeated and that every edge is used once
def walkEdges {V : Type} (p : List V) : List (Sym2 V) :=
  (p.zip p.tail).map (fun ab => s(ab.1, ab.2))

structure EulerCircuit {V : Type} [DecidableEq V] {G : Graph V} extends Walk G where
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


def triangle : Graph (Fin 3) where
  Adj u v := u ≠ v
  adj_symm := fun _ _ h => Ne.symm h

def triangleWalk : Walk triangle where
  support := [0, 1, 2, 0]
  adj := by
    intro i h
    have : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp at h
      omega
    rcases this with rfl | rfl | rfl <;> simp [triangle]

def triangleEuler : EulerCircuit (G := triangle) where
  toWalk := triangleWalk
  isCircuit := by
    unfold IsCircuit
    and_intros
    · decide
    · decide
  eachEdgeOnce := by
    intro u v h
    fin_cases u <;> fin_cases v <;>
      simp_all [triangle, triangleWalk, walkEdges]


-- next, hamiltonian cycles
-- unlike a Euler's circuit, which uses every edge once, a hamiltonian cycle
-- will hit every edge and vertex wihtout repeating any vertex.
-- the proof is that for a graph with of n vtx atleast 3 vtxs
-- if every vtx has atleast n/2 then it will have a hamiltonian cycle
-- the proof is usually a proof by contradiction
-- where assuming Ore's Thereom is false, which is that deg(u) +deg(v) ≥ n
-- for every pair of distinct non adj, vtx.

def IsHamiltonianWalk {V : Type} [DecidableEq V] {G : Graph V}
    (vertices : List V) (w : Walk G) : Prop :=
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

def squareEdges : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 2), (2, 3), (0, 3), (0, 2)]

def squareAdj (u v : Fin 4) : Prop :=
  (u, v) ∈ squareEdges ∨ (v, u) ∈ squareEdges

def squareWithDiagonal : Graph (Fin 4) where
  Adj := squareAdj
  adj_symm := by
    intro u v h
    exact Or.symm h

def squarePerimeter : Walk squareWithDiagonal where
  support := [0, 1, 2, 3, 0]
  adj := by
    intro i h
    have hi : i < 4 := by simp at h; omega
    interval_cases i <;> simp [squareWithDiagonal, squareAdj, squareEdges]

theorem square_perimeter_is_hamiltonian :
    IsHamiltonianWalk [0, 1, 2, 3] squarePerimeter := by
  simp [IsHamiltonianWalk, IsCircuit, squarePerimeter]

theorem square_perimeter_is_not_euler :
    ¬ ∃ c : EulerCircuit (G := squareWithDiagonal), c.toWalk = squarePerimeter := by
  rintro ⟨c, hc⟩
  have hdiag := c.eachEdgeOnce 0 2
    (by simp [squareWithDiagonal, squareAdj, squareEdges])
  rw [hc] at hdiag
  simp [squarePerimeter, walkEdges] at hdiag
