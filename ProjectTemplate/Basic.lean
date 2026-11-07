import Mathlib.Tactic.MinImports
import Mathlib.Tactic

-- what is a circuit:
structure Graph (V : Type) where
  Adj : V → V → Prop
  adj_symm : ∀ u v, Adj u v → Adj v u

structure Walk {V : Type} (G : Graph V) where
  support : List V
  adj : ∀ (i : Nat) (h : i + 1 < support.length),
    G.Adj (support[i]'(by omega)) (support[i + 1]'h)

def Walk.length {V : Type} {G : Graph V} (w : Walk G) : Nat :=
  w.support.length - 1

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

def IsEulerCircuit {V : Type} [DecidableEq V] {G : Graph V} (w : Walk G) : Prop :=
  IsCircuit w ∧
  ∀ u v, G.Adj u v → (walkEdges w.support).count s(u, v) = 1

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

example : triangleWalk.length = 3 := by decide

example : IsEulerCircuit triangleWalk := by
  unfold IsEulerCircuit
  constructor
  · -- it is a circuit
    unfold IsCircuit
    and_intros
    · decide
    · decide
  · -- every edge is used exactly once
    intro u v h
    fin_cases u <;> fin_cases v <;>
      simp_all [triangle, triangleWalk, walkEdges]
