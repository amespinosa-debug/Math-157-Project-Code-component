import MyProject.Basic
import Mathlib.Tactic.Lemma

/- My goal was to formalize the Handshaking Lemma and its proof using lists and induction rather than
Mathlib's graph functions. However, I made a few adjustments that don't necessarily adhere to the proof of
the Handshaking Lemma, but I believe demonstrates a very similar path. To find the total degree of a graph,
I base my function on edges rather than vertices. I believe this offers a valid representation. However, this
does result in the lack of use for my V (vertices) list. Furthermore, I assume a simple and undirected graph for
simplicity, since I was having a hard time with the self-loops. -/
/- Note: I did use ChatGPT to help create an outline of what structures, functions, and lemmas needed to
build up the Handshaking Lemma. -/

-- I define a graph as a structure with two fields: V (vertices) and E (edges).
structure aGraph where
    V : List Nat
    E : List (Nat × Nat)

/- This is a recursive function that takes a given vertex and a graph as an input and returns the degree of that
vertex. It ignores the vertices field and checks if the the edges field is empty, then it returns 0. Otherwise,
it goes through the list of edges, and checks if the vertex is connected to that edge. If it is, it returns 1 and
0 otherwise. Then it calls itself recursively.
-/
def degreeOfAVertex (v: Nat): aGraph → Nat
    | ⟨_, []⟩ => 0
    | ⟨vertex, (u, w) :: edgeTail⟩  =>
        let count := if v == u ∨ v == w then 1 else 0
        count + degreeOfAVertex v ⟨vertex, edgeTail⟩

/- This is another recursive function that finds the total degree using edges, rather than vertices. It takes a
vertex and a graph as an input and returns the total sum of the graph. If the edges field is empty,
then it returns 0. Otherwise, it goes through the list of edges, calls the degreeOfAVertex function to find
the degree of the vertices in that edge. Then it calls itself recursively. -/
def totalDegree (V: List Nat): aGraph → Nat
    | ⟨_ , []⟩ => 0
    | ⟨vertex, (u,w) :: edgeTail⟩ =>
        let count := degreeOfAVertex u ⟨vertex, [(u,w)]⟩ + degreeOfAVertex w ⟨vertex, [(u,w)]⟩
        count + totalDegree V ⟨vertex, edgeTail⟩

/- This lemma suggests that a single edge adds +2 to the sum of total degrees in the graph. -/
lemma singleAddEdge (u w : Nat)(V : List Nat) :
    totalDegree V ⟨V, [(u, w)]⟩ = 2 := by
      simp [totalDegree]
      simp [degreeOfAVertex]

/- This is the Handshaking Lemma in which the total degrees in a graph is twice the the number of edges
in the graph. I open the induction with E and prove the base case (nil). Then, I prove the inductive case (cons)
 by unpacking the edge, with vertices u w. -/
theorem handshakingLemma (V: List Nat)(E: List (Nat × Nat)):
    totalDegree V ⟨V, E⟩ = 2 * E.length := by
      induction E with
        | nil =>
            simp [totalDegree]
        | cons edge tail ih =>
          cases edge with
            | mk u w =>
              simp [totalDegree, degreeOfAVertex]
              simp [ih]
              simp [Nat.mul_add]
              omega


#check handshakingLemma
