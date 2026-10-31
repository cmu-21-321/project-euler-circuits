import Mathlib.Tactic

-- needs to start by defining what a tree is

inductive FullTree : Type where
  | leaf : FullTree
  | node : FullTree → FullTree → FullTree

def nodes : FullTree → Nat
  | .leaf => 1
  | .node left right => 1 + nodes left + nodes right

def leaves : FullTree → Nat
  | .leaf => 1
  | .node left right => leaves left + leaves right

def internalNodes : FullTree → Nat
  | .leaf => 0
  | .node left right =>
      1 + internalNodes left + internalNodes right

def edges : FullTree → Nat
  | .leaf => 0
  | .node left right =>
      2 + edges left + edges right

-- what is a circuit:
structure Graph (V : Type) where
  Adj : V → V → Prop
  adj_symm : ∀ u v, Adj u v → Adj v u

def IsWalk {V : Type} (G : Graph V) (p : List V) : Prop :=
  ∀ i : Fin (p.length - 1),
    G.Adj (p.get ⟨i.val, by omega⟩)
           (p.get ⟨i.val + 1, by omega⟩)

def IsCircuit {V : Type} (G : Graph V) (p : List V) : Prop :=
  p.length ≥ 2 ∧
  p.head? = p.getLast? ∧
  IsWalk G p

#eval [1,2,3,4].head?
#eval [1,2,3,4].getLast?
--p.head? returns the first item in the list, and p.getLast? returns the
-- last element of the list. This also works for trees, using nodes and leaves
-- instead of the #'s

-- an example of a single edge that works as a circuit

def singleEdge : Graph Bool where
  Adj u v := u ≠ v
  adj_symm := fun _ _ h => Ne.symm h

example : IsCircuit singleEdge [true, false, true] := by
  unfold IsCircuit
  and_intros
  · decide
  · decide
  · rintro ⟨i, hi⟩
    simp at hi
    interval_cases i <;> simp [singleEdge]

-- needs to be closed (the path starts and closes on the same vtx)
-- cannot traverse any edge more than once
-- but you can repeat the same node more than once if needed

-- Euler's circuit
-- requires that no edge is repeated and that every edge is used once

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
