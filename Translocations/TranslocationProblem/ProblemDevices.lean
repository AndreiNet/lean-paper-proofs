import TranslocationProblem.Hamilton
import TranslocationProblem.Translocations
import TranslocationProblem.B3

import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

def map_edge (v : Vector Int n) (p : Vector Int n) (u t : Fin n) : Int :=
  v.get t + p.get u - v.get u

def edge_vals (f : Fin n → Fin n → Int) :
  Sym2 (Fin n) → Finset Int :=
  Sym2.lift ⟨fun x y => {f x y, f y x},
   (by
    intro u v
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
   )⟩

structure InstanceWithParams (n : Nat) where
  inst : TranslocationProblemInstance (γ₁ := Finset Int) (γ₂ := Finset Int)
  b: B3Vec (2 * n)
  m : Int
  M : Int
  v : Vector Int n
  p : Vector Int n
  e : Finset Int

noncomputable def map_graph_to_translocation_pr_aux (g : SimpleGraph <| Fin n) (h : n > 0) :
  InstanceWithParams n :=
  have b := get_b3 (2 * n)
  let m := b.v.toList.maximum.getD 0
  let M := 4 * (m + 1)
  let v := @Vector.ofFn n _ (fun i => b.v[i])
  let p := @Vector.ofFn n _ (fun i => M + b.v[n + i.val])
  let e := g.edgeFinset.biUnion <| edge_vals <| map_edge v p
  {
    inst := {
      A := e ∪ {v[0], p[n - 1]}
      B := (v.toList.toFinset ∪ p.toList.toFinset) \ {v[0], p[n - 1]}
    }, m, M, v, p, e, b}

noncomputable def map_graph_to_translocation_pr (g : SimpleGraph <| Fin n) (h : n > 0)
  : TranslocationProblemInstance (γ₁ := Finset Int) (γ₂ := Finset Int) :=
  let inst := (map_graph_to_translocation_pr_aux g h).inst
  inst
