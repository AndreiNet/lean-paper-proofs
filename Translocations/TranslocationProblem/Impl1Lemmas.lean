import TranslocationProblem.ProblemDevices
import TranslocationProblem.Lemmas

lemma walk_support {n} {g : SimpleGraph (Fin n)} {u v} (w : g.Walk u v) :
  ∀ hi: i < w.support.length, w.support[i] = w.getVert i := by
  induction w generalizing i with
  | nil => simp only [SimpleGraph.Walk.support_nil, List.length_cons, List.length_nil, zero_add,
      Nat.lt_one_iff, List.getElem_singleton, SimpleGraph.Walk.getVert_nil, implies_true]
  | @cons u v w x xs ih =>
    simp only [SimpleGraph.Walk.support_cons, List.length_cons, SimpleGraph.Walk.length_support,
      Order.lt_add_one_iff]
    simp only [SimpleGraph.Walk.length_support, Order.lt_add_one_iff] at ih
    intro hi
    have : i - 1 ≤ xs.length := by omega
    specialize ih this
    cases i with
    | zero => simp only [List.getElem_cons_zero, SimpleGraph.Walk.getVert_zero]
    | succ j =>
      simp only [List.getElem_cons_succ, SimpleGraph.Walk.getVert_cons_succ]
      simp only [add_tsub_cancel_right] at ih
      exact ih

lemma zero_lt_v {g : SimpleGraph (Fin n)} {i : Fin n} {mg} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  0 < mg.v[i] := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton]
  have := (get_b3 (2 * n)).pos ⟨i.val, n_2n i.prop⟩
  simp only [Fin.getElem_fin, gt_iff_lt] at this
  exact this

lemma zero_lt_p {g : SimpleGraph (Fin n)} {i : Fin n} {mg} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  0 < mg.p[i] := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton]
  have := (get_b3 (2 * n)).pos ⟨n + i.val, n_add_n_2n i.prop⟩
  simp only [Fin.getElem_fin, gt_iff_lt] at this
  have h1 : (get_b3 (2 * n)).v[n + i] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_add_n_2n i.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  omega

lemma zero_lt_e {g : SimpleGraph (Fin n)} {u v : Fin n} {mg} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  0 < map_edge mg.v mg.p u v := by
  simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Vector.get_ofFn, Int.sub_pos]
  have := (get_b3 (2 * n)).pos
  simp only [Fin.getElem_fin, gt_iff_lt] at this
  have h1 : (get_b3 (2 * n)).v[u.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n u.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have hu := this ⟨u.val, n_2n u.prop⟩
  have hv := this ⟨v.val, n_2n v.prop⟩
  have hnu := this ⟨n + u.val, n_add_n_2n u.prop⟩
  simp only at hu hv hnu
  omega
