import TranslocationProblem.Impl1
import TranslocationProblem.Impl2

theorem pr_equiv {inst} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (h : inst = map_graph_to_translocation_pr g hn) :
  (Nonempty <| HamiltonianPath (u := ⟨0, hn⟩) (v := sink hn) g)
    ↔ (∃S, Solution inst S ∧ S.length = n - 1) :=
      Iff.intro (hamilton_impl_trans_pr h) (trans_pr_imp_hamilton h)
