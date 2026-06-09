import TranslocationProblem.ProblemDevices
import TranslocationProblem.Impl1Lemmas
import TranslocationProblem.Lemmas
import TranslocationProblem.B3

lemma hamilton_impl_trans_pr {inst} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (h : inst = map_graph_to_translocation_pr g hn) :
  (Nonempty <| HamiltonianPath (u := ⟨0, hn⟩) (v := sink hn) g)
    → (∃S, Solution inst S ∧ S.length = n - 1) := by
  rw [sink]
  intro hx
  obtain ⟨hx⟩ := hx
  obtain ⟨w, hamiltonianPath⟩ := hx
  let l := w.support
  have sup_len := hamilton_path_length { w, hamiltonianPath }
  set mg := map_graph_to_translocation_pr_aux g hn with hmg
  have nm1 : n - 1 < n := by omega
  let get_elem {i} (hi : i < n - 1) :=
    (
    mg.v[w.support[i]'(by rw [sup_len] ; get_elem_tactic)],
    map_edge mg.v mg.p (w.support[i]'(by rw [sup_len] ; get_elem_tactic)) (w.support[i + 1]'(by
      rw [sup_len] ; get_elem_tactic))
    ) ⊢ (
      mg.v[w.support[i + 1]'(by rw [sup_len] ; get_elem_tactic)],
      mg.p[w.support[i]'(by rw [sup_len] ; get_elem_tactic)]
    ) | (by
      simp +arith [hmg, map_graph_to_translocation_pr_aux, map_edge]
    ) | (by {
      apply And.intro (zero_lt_v hmg)
      apply And.intro (zero_lt_e hmg)
      exact And.intro (zero_lt_v hmg) (zero_lt_p hmg)
    })
  let sol_vec_pref {d} (hd : d < n) :=
    (@Vector.ofFn d _ fun i => @get_elem i (by omega)).toList.reverse
  use sol_vec_pref nm1
  apply And.intro
  · unfold sol_vec_pref get_elem
    apply Solution.mk
    · simp +arith only [h, map_graph_to_translocation_pr, map_graph_to_translocation_pr_aux,
        Fin.getElem_fin, Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
        Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, Vector.mem_toList_iff,
        Vector.mem_ofFn, Int.reduceNeg, neg_mul, one_mul, Finset.mem_insert,
        Finset.mem_singleton, not_or, Finset.mem_biUnion, SimpleGraph.mem_edgeFinset,
        List.mem_reverse, exists_exists_eq_and, and_imp]
      intros x hx hh1 hh2
      cases hx with
      | inl hl =>
        obtain ⟨i, hi⟩ := hl
        have i_not_zero : i.val ≠ 0 := by
          by_contra
          simp only [this] at hi
          exact hh1 (Eq.symm hi)
        have zero_lt_i : 0 < i.val := by omega
        apply Or.inr
        simp only [hmg]
        simp +arith only [map_graph_to_translocation_pr_aux,
          Finset.union_insert, Finset.union_singleton]
        obtain ⟨j, hj1, hj2⟩ := List.getElem_of_mem (hamiltonianPath.right i)
        rw [←hj2] at zero_lt_i
        have : 0 < j := by
          by_contra
          simp only [not_lt, nonpos_iff_eq_zero] at this
          simp only [this, SimpleGraph.Walk.support_getElem_zero] at hj2
          have := Eq.symm <| congrArg Fin.val hj2
          contradiction
        rw [sup_len] at hj1
        use ⟨j - 1, by omega⟩
        apply Or.inl
        have : j - 1 + 1 = j := by omega
        simp only [this]
        rw [←hj2] at hi
        symm at hi
        simp only [Fin.getElem_fin, Vector.getElem_ofFn]
        exact hi
      | inr hr =>
        obtain ⟨i, hi⟩ := hr
        have i_not_n_sub_one : i.val ≠ n - 1 := by
          by_contra
          simp +arith only [this, Int.reduceNeg,
            neg_mul, one_mul] at hi
          simp +arith only [Int.reduceNeg, neg_mul, one_mul] at hh2
          apply hh2
          omega
        have i_lt_n_sub_one : i.val < n - 1 := by omega
        simp only [hmg]
        simp +arith only [map_graph_to_translocation_pr_aux,
          Finset.union_insert, Finset.union_singleton]
        apply Or.inr
        obtain ⟨j, hj1, hj2⟩ := List.getElem_of_mem (hamiltonianPath.right i)
        rw [←hj2] at i_lt_n_sub_one
        have  : j < n - 1 := by
          by_contra
          rw [sup_len] at hj1
          have  : j = n - 1 := by omega
          have hwl : w.length + 1 - 1 = w.length := by omega
          simp only [this, SimpleGraph.Walk.length_support,
            ←sup_len, hwl, SimpleGraph.Walk.support_getElem_length] at hj2
          have := Eq.symm <| congrArg Fin.val hj2
          simp only [SimpleGraph.Walk.length_support, ←sup_len] at i_not_n_sub_one
          contradiction
        use ⟨j, this⟩
        apply Or.inr
        simp only [Vector.getElem_ofFn]
        simp +arith only [← hj2, Int.reduceNeg, neg_mul, one_mul] at hi
        omega
    · let (m : Nat) (hm : m < n) : ValidOn inst.A (sol_vec_pref hm) := by
          induction m with
          | zero => exact .nil
          | succ d ih =>
            have hmd : d < n := by omega
            set xs := sol_vec_pref hmd with hxs
            set xt := sol_vec_pref hm with hxt
            have : (@get_elem d (by omega)) :: xs = xt := by
              ext i
              cases i with
              | zero => simp [hxs, hxt, sol_vec_pref]
              | succ j =>
                simp [hxt, hxs, sol_vec_pref]
                by_cases hj : j < d
                · have : d - 1 - j = d - (j + 1) := by omega
                  simp only [List.length_reverse, Vector.length_toList, hj, getElem?_pos,
                    List.getElem_reverse, this, Vector.getElem_toList, Vector.getElem_ofFn,
                    Option.some.injEq, Order.lt_add_one_iff, Order.add_one_le_iff,
                    add_tsub_cancel_right]
                · simp only [List.length_reverse, Vector.length_toList, hj, not_false_eq_true,
                  getElem?_neg, reduceCtorEq, Order.lt_add_one_iff, Order.add_one_le_iff]
            rw [←this]
            apply ValidOn.cons
            · unfold valid_translocation
              apply And.intro
              · by_cases hdv : d = 0
                · apply Or.inl
                  unfold get_elem
                  simp only [hdv, SimpleGraph.Walk.support_getElem_zero]
                  rw [h, hmg, map_graph_to_translocation_pr, map_graph_to_translocation_pr_aux]
                  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Finset.union_insert,
                    Finset.union_singleton, Finset.mem_insert, Finset.mem_biUnion,
                    SimpleGraph.mem_edgeFinset, true_or]
                · apply Or.inr
                  have : 0 < xs.length := by
                      have hh := hxs
                      simp only [sol_vec_pref] at hh
                      have := congrArg (fun l => l.length) hh
                      simp only at this
                      simp only [List.length_reverse, Vector.length_toList] at this
                      rw [this]
                      omega
                  use xs[0]'this
                  rw [List.mem_iff_getElem]
                  apply And.intro
                  · use 0
                    use this
                  · apply Or.inl
                    simp +arith only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
                      Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
                      hxs, List.getElem_reverse, Vector.length_toList, tsub_zero,
                      Vector.getElem_toList, sol_vec_pref, get_elem]
                    have : d - 1 + 1 = d := by omega
                    simp only [this]
              · apply Or.inl
                rw [h, map_graph_to_translocation_pr, map_graph_to_translocation_pr_aux]
                simp only [Fin.getElem_fin, Vector.getElem_ofFn, Finset.union_insert,
                  Finset.union_singleton, Finset.mem_insert, Finset.mem_biUnion,
                  SimpleGraph.mem_edgeFinset]
                apply Or.inr
                apply Or.inr
                use Sym2.mk (w.support[d]'(by rw [sup_len] ; get_elem_tactic),
                  w.support[d + 1]'(by rw [sup_len] ; get_elem_tactic))
                apply And.intro
                · simp only [SimpleGraph.mem_edgeSet]
                  have hdl : d < w.length := by
                    rw [←sup_len] at hm
                    simp only at hm
                    rw [SimpleGraph.Walk.length_support] at hm
                    omega
                  have hdl1 : d < w.support.length := by
                    rw [←sup_len] at hmd
                    exact hmd
                  rw [walk_support _ (by rw [←sup_len] at hmd ; exact hmd)]
                  rw [walk_support _ (by rw [←sup_len] at hm ; exact hm)]
                  exact w.adj_getVert_succ hdl
                · simp only [edge_vals, map_edge, Vector.get_ofFn, Sym2.lift_mk, Finset.mem_insert,
                    Finset.mem_singleton, get_elem]
                  rw [hmg, map_graph_to_translocation_pr_aux]
                  simp only [Fin.getElem_fin, Vector.get_ofFn, true_or]
            · specialize ih hmd
              rw [←hxs] at ih
              exact ih
      exact this (n - 1) nm1
  · simp only [List.length_reverse, Vector.length_toList, sol_vec_pref]
