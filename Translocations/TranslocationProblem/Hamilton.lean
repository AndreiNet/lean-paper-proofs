import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

structure HamiltonianPath {u v : Fin n} (G : SimpleGraph (Fin n)) where
  w : G.Walk u v
  hamiltonianPath : w.IsPath ∧ ∀ v : Fin n, v ∈ w.support

private lemma unique_list_length [Fintype α] {l : List α} (no_dup : l.Nodup)
  (all_v : ∀ v : α, v ∈ l): l.length = Fintype.card α := by
  classical
  rw [←List.toFinset_card_of_nodup no_dup]
  congr
  ext x
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact all_v x

lemma hamilton_path_length {n} {u v} {g : SimpleGraph (Fin n)}
  (h : HamiltonianPath (u := u) (v := v) g) :
  h.w.support.length = n := by
  obtain ⟨w, hamiltonPath⟩ := h
  rw [SimpleGraph.Walk.isPath_def] at hamiltonPath
  have := unique_list_length hamiltonPath.left hamiltonPath.right
  rw [Fintype.card_fin] at this
  assumption

lemma isPath_length_impl_mem {n} {u v} {g : SimpleGraph (Fin n)} {w : g.Walk u v}
  (hn : n > 0)
  (hpath : w.IsPath) (hlen : w.length = n - 1) :
  ∀ v : Fin n, v ∈ w.support := by
  by_contra hx
  simp only [not_forall] at hx
  obtain ⟨x, hx⟩ := hx
  set wx := x :: w.support with hwx
  have : wx.Nodup := by
    rw [List.Nodup]
    apply List.Pairwise.cons
    · intro a ha hc
      rw [←hc] at ha
      contradiction
    · exact hpath.support_nodup
  have hlen_finset := List.toFinset_card_of_nodup this
  simp +arith only [hwx, List.toFinset_cons, List.length_cons, SimpleGraph.Walk.length_support,
    hlen] at hlen_finset
  have hlen_finset : (insert x w.support.toFinset).card = n + 1 := by omega
  have := Finset.card_le_univ (insert x w.support.toFinset)
  rw [Fintype.card_fin] at this
  omega
