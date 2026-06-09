import TranslocationProblem.ProblemDevices
import TranslocationProblem.Impl2Lemmas
import TranslocationProblem.B3
import TranslocationProblem.SetArguments
import TranslocationProblem.TranslocationIsEdge

lemma v_in_tail {α} {v : α} {l : List α} (hl : l ≠ []) (hv : v ∈ l) (hv1 : v ≠ l.head hl)
  : v ∈ l.tail := by
  classical
  cases l with
  | cons x xs =>
    rw [List.mem_cons] at hv
    cases hv with
    | inl => contradiction
    | inr =>
      rw [List.tail_cons]
      assumption
  | nil => contradiction

lemma v_in_A_impl_zero {mg} {hn : n > 0} {g : SimpleGraph <| Fin n} {u : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (h : mg.v[u] ∈ mg.inst.A) : u.val = 0 := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.mem_insert, Finset.mem_biUnion,
    SimpleGraph.mem_edgeFinset] at h
  cases h with
  | inl h =>
    have := @b1_of_b3_2 (2 * n) ⟨u.val, n_2n u.prop⟩ ⟨0, n_2n hn⟩ (by linarith only [hn])
      (get_b3 (2 * n)) h
    simp only [Fin.mk.injEq] at this
    exact this
  | inr h =>
    cases h with
    | inl h =>
      have := @v_neq_p _ _ _ u (sink hn) _ hmg
      simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, ne_eq] at this
      contradiction
    | inr h =>
      obtain ⟨a, ha⟩ := h
      obtain ⟨x, y, hxy⟩ := exists_pair a
      simp only [hxy.left, SimpleGraph.mem_edgeSet, edge_vals, map_edge, Vector.get_ofFn,
        Sym2.lift_mk, Finset.mem_insert, Finset.mem_singleton] at ha
      cases ha.right with
      | inl ha =>
        have := @v_neq_e _ _ _ u hn x y hmg
        simp [hmg, map_graph_to_translocation_pr_aux, map_edge, edge_vals] at this
        contradiction
      | inr ha =>
        have := @v_neq_e _ _ _ u hn y x hmg
        simp [hmg, map_graph_to_translocation_pr_aux, map_edge, edge_vals] at this
        contradiction

lemma head_in_head_cons {α} (s : α) (S' : List α) : s ∈ s :: S' :=
  Iff.mpr List.mem_cons (Or.inl rfl)

theorem build_inductive_step_goal_one_way {n} {u v nd : Fin n} {mg} {hn : n > 0}
  {s1 : Translocation}
  {g : SimpleGraph <| Fin n}
  {w : g.Walk ⟨0, hn⟩ nd}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hs1 : valid_translocation mg.inst.A (s :: S') s1 ∧
    ∃ u v_1, g.Adj u v_1 ∧ (s1.x = mg.v[u] ∧ s1.y = map_edge mg.v mg.p u v_1
    ∨ s1.x = map_edge mg.v mg.p u v_1 ∧ s1.y = mg.v[u]) ∧
    (s1.u = mg.v[v_1] ∧ s1.v = mg.p[u] ∨ s1.u = mg.p[u] ∧ s1.v = mg.v[v_1]))
  (hedg_r : s.u = mg.p[u] ∧ s.v = mg.v[v])
  (ih1 : (List.map (fun s ↦ s.u) S').toFinset ∪ (List.map (fun s ↦ s.v) S').toFinset =
    (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset
    ∪ (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset) :
  ((s1.x = mg.v[↑v] ∨ ∃ a ∈ w.support, mg.v[↑a] = s1.x) ∨ s1.y = mg.v[↑v] ∨
    ∃ a ∈ w.support, mg.v[↑a] = s1.y) ∨ s1.x ∈ mg.e := by
  obtain ⟨u', v', huv'⟩ := hs1.right
  have h_cvalid := hs1.left
  simp [valid_translocation] at h_cvalid
  cases h_cvalid.left with
  | inl h_inA =>
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
      Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
      Finset.mem_insert, Finset.mem_biUnion, SimpleGraph.mem_edgeFinset] at h_inA
    cases h_inA with
    | inl h_inA =>
      refine Or.inl (Or.inl (Or.inr ?_))
      use ⟨0, hn⟩
      apply And.intro
      · exact w.start_mem_support
      · simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
        Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
        exact Eq.symm h_inA
    | inr h_inA =>
      cases h_inA with
      | inl h_inA =>
        have h_u'v'_adj := huv'.left
        cases huv'.right.left with
        | inl huv' =>
          rw [huv'.left] at h_inA
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert,
            Finset.union_singleton] at h_inA
          have := @v_neq_p _ _ _ u' (sink hn) _ hmg
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
            ne_eq] at this
          contradiction
        | inr huv' =>
          rw [huv'.left] at h_inA
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert,
            Finset.union_singleton] at h_inA
          have := @p_neq_e _ _ _ (sink hn) _ u' v' hmg
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert,
            Finset.union_singleton] at this
          have := this (Eq.symm h_inA)
          rw [this] at h_u'v'_adj
          have := g.irrefl h_u'v'_adj
          contradiction
      | inr h_inA =>
        apply Or.inr
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
          Finset.union_insert, Finset.union_singleton, Finset.mem_biUnion,
          SimpleGraph.mem_edgeFinset]
        exact h_inA
  | inr hr =>
    cases hr with
    | inl h_at_head =>
      rw [hedg_r.left, hedg_r.right] at h_at_head
      have h_u'v'_adj := huv'.left
      cases huv'.right.left with
      | inl huv' =>
        cases h_at_head with
        | inl h_at_head =>
          rw [huv'.left] at h_at_head
          have := v_neq_p hmg h_at_head
          contradiction
        | inr h_at_head =>
          exact Or.inl (Or.inl (Or.inl h_at_head))
      | inr huv' =>
        cases h_at_head with
        | inl h_at_head =>
          rw [h_at_head] at huv'
          have := p_neq_e hmg huv'.left
          rw [this] at h_u'v'_adj
          have := g.irrefl h_u'v'_adj
          contradiction
        | inr h_at_head =>
          rw [h_at_head] at huv'
          have := v_neq_e hmg huv'.left
          contradiction
    | inr h_in_tail =>
      have := ih1
      simp only [Fin.getElem_fin, List.map_tail, List.map_dropLast] at this
      have hh: s1.x ∈ (List.map (fun s ↦ s.u) S').toFinset ∪
        (List.map (fun s ↦ s.v) S').toFinset := by
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_map]
        obtain ⟨a, ha⟩ := h_in_tail
        cases ha.right with
        | inl ha1 => exact Or.inl (Exists.intro a (And.intro ha.left (Eq.symm ha1)))
        | inr ha1 => exact Or.inr (Exists.intro a (And.intro ha.left (Eq.symm ha1)))
      rw [this] at hh
      simp only [Finset.mem_union, List.mem_toFinset] at hh
      cases hh with
      | inl hh =>
        have hh := List.mem_of_mem_tail hh
        simp only [List.mem_map] at hh
        exact Or.inl (Or.inl (Or.inr hh))
      | inr hh =>
        have hh := List.mem_of_mem_dropLast hh
        simp only [List.mem_map] at hh
        obtain ⟨a, ha⟩ := hh
        have h_u'v'_adj := huv'.left
        cases huv'.right.left with
        | inl huv' =>
          rw [huv'.left] at ha
          have := v_neq_p hmg (Eq.symm ha.right)
          contradiction
        | inr huv' =>
          rw [huv'.left] at ha
          have := p_neq_e hmg ha.right
          rw [this] at h_u'v'_adj
          have := g.irrefl h_u'v'_adj
          contradiction

theorem build_inductive_step_goal {n} {u v nd : Fin n} {mg} {hn : n > 0}
  {s1 : Translocation}
  {g : SimpleGraph <| Fin n}
  {w : g.Walk ⟨0, hn⟩ nd}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hs1 : valid_translocation mg.inst.A (s :: S') s1 ∧
    ∃ u v_1, g.Adj u v_1 ∧ (s1.x = mg.v[u] ∧ s1.y = map_edge mg.v mg.p u v_1
    ∨ s1.x = map_edge mg.v mg.p u v_1 ∧ s1.y = mg.v[u]) ∧
    (s1.u = mg.v[v_1] ∧ s1.v = mg.p[u] ∨ s1.u = mg.p[u] ∧ s1.v = mg.v[v_1]))
  (hedg_r : s.u = mg.p[u] ∧ s.v = mg.v[v])
  (ih1 : (List.map (fun s ↦ s.u) S').toFinset ∪ (List.map (fun s ↦ s.v) S').toFinset =
    (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset
    ∪ (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset) :
  (s1.x = mg.v[↑v] ∨ ∃ a ∈ w.support, mg.v[↑a] = s1.x) ∨ s1.y = mg.v[↑v] ∨
    ∃ a ∈ w.support, mg.v[↑a] = s1.y := by
  have way_one := build_inductive_step_goal_one_way hmg hs1 hedg_r ih1
  cases way_one with
  | inl => assumption
  | inr he1 =>
    set s1' := translocation_symm_left s1 with hs1'
    have hsb := translocation_symm_left_inv hs1'
    simp only [hsb, translocation_symm_left] at hs1
    have way_two := build_inductive_step_goal_one_way (s1 := s1') hmg ?_ hedg_r ih1
    rotate_left 1
    · convert hs1 using 0
      apply Iff.intro
      · intro hh
        have := hh.left
        rw [hs1', ←valid_translocation_symm_left_iff] at this
        simp only [hsb, translocation_symm_left] at this
        apply And.intro this
        obtain ⟨u, v1, huv1⟩ := hh.right
        use u, v1
        apply And.intro huv1.left
        refine And.intro ?_ huv1.right.right
        cases huv1.right.left with
        | inl huv1 => exact Or.inr (And.symm huv1)
        | inr huv1 => exact Or.inl (And.symm huv1)
      · intro hh
        have := hh.left
        rw [hs1', ←valid_translocation_symm_left_iff]
        simp only [hsb, translocation_symm_left, Fin.getElem_fin]
        apply And.intro this
        obtain ⟨u, v1, huv1⟩ := hh.right
        use u, v1
        apply And.intro huv1.left
        refine And.intro ?_ huv1.right.right
        cases huv1.right.left with
        | inl huv1 => exact Or.inr (And.symm huv1)
        | inr huv1 => exact Or.inl (And.symm huv1)
    cases way_two with
    | inl he2 =>
      simp only [hs1', translocation_symm_left ] at he2
      cases he2 <;> rename_i he2 <;> cases he2 <;> rename_i he2 <;> clear * - he2 <;> grind only
    | inr he2 =>
      obtain ⟨u, v1, huv1⟩ := hs1.right
      have huv1 := huv1.right.left
      simp only [hs1', translocation_symm_left] at huv1 he2
      cases huv1 with
      | inl huv1 =>
        rw [huv1.left] at he1
        have := v_nmem_e hmg he1
        contradiction
      | inr huv1 =>
        rw [huv1.right] at he2
        have := v_nmem_e hmg he2
        contradiction

theorem solution_impl_inductive_step {n} {u v nd : Fin n} {mg} {hn : n > 0}
  {g : SimpleGraph <| Fin n}
  {w : g.Walk ⟨0, hn⟩ nd}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hcons_adj : s.x ∈ (List.map (fun v ↦ mg.v[v]) w.support).toFinset
    ∨ s.y ∈ (List.map (fun v ↦ mg.v[v]) w.support).toFinset)
  (diff_curr : ∀ a' ∈ S', s.u ≠ a'.u ∧ s.v ≠ a'.v ∧ s.u ≠ a'.v ∧ s.v ≠ a'.u)
  (huv : g.Adj u v ∧
    (s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v ∨ s.x = map_edge mg.v mg.p u v ∧ s.y = mg.v[u]) ∧
    (s.u = mg.v[v] ∧ s.v = mg.p[u] ∨ s.u = mg.p[u] ∧ s.v = mg.v[v]))
  (h_u_v_in_B : ∀ s_1 ∈ s :: S', (s_1.u ∈ mg.inst.B \ mg.inst.A
    ∧ s_1.v ∈ mg.inst.B \ mg.inst.A) ∧ s_1.u ≠ s_1.v)
  (hedg : s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v)
  (hedg_r : s.u = mg.p[u] ∧ s.v = mg.v[v])
  (ih1 : (List.map (fun s ↦ s.u) S').toFinset ∪ (List.map (fun s ↦ s.v) S').toFinset =
    (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset
    ∪ (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset)
  (ih2 : w.IsPath)
  (ih3 : w.length = S'.length)
  (ih4 : sink hn ∉ w.support.dropLast)
  -- end of hypotheses
  :
  -- start of the result
  ∃w : g.Walk ⟨0, hn⟩ v, (∀ (s_1 : Translocation),
    (valid_translocation mg.inst.A (s :: S') s_1 ∧ ∃ u v, g.Adj u v ∧
      (s_1.x = mg.v[u] ∧ s_1.y = map_edge mg.v mg.p u v ∨
      s_1.x = map_edge mg.v mg.p u v ∧ s_1.y = mg.v[u]) ∧
      (s_1.u = mg.v[v] ∧ s_1.v = mg.p[u] ∨ s_1.u = mg.p[u] ∧ s_1.v = mg.v[v])) →
    s_1.x ∈ (List.map (fun v ↦ mg.v[v]) w.support).toFinset ∨
      s_1.y ∈ (List.map (fun v ↦ mg.v[v]) w.support).toFinset)
    ∧ (List.map (fun s ↦ s.u) (s :: S')).toFinset ∪ (List.map (fun s ↦ s.v) (s :: S')).toFinset =
    (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset ∪
    (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset ∧
    w.IsPath ∧ w.length = (s :: S').length ∧ sink hn ∉ w.support.dropLast := by
  have : w.support.getLast (by simp only [ne_eq, SimpleGraph.Walk.support_ne_nil,
    not_false_eq_true]) = nd := by
    exact w.getLast_support
  by_cases h_selv : s.x = mg.v[w.support.getLast (by simp only [ne_eq,
    SimpleGraph.Walk.support_ne_nil, not_false_eq_true])]
  · simp only [this] at h_selv
    have : mg.v[u] = mg.v[nd] := by
      rw [hedg.left] at h_selv
      exact h_selv
    have h_u_nd := v_eq_v hmg this
    by_cases hv : v ∈ w.support
    · by_cases hv1 : v = w.support.head (by simp only [ne_eq,
      SimpleGraph.Walk.support_ne_nil, not_false_eq_true])
      · rw [w.head_support] at hv1
        rw [hv1] at hedg_r
        specialize h_u_v_in_B s (by simp only [List.mem_cons, true_or])
        rw [hedg_r.right] at h_u_v_in_B
        have := h_u_v_in_B.left.right
        have := (Iff.mp Finset.mem_sdiff this).left
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
          Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
          Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, Vector.mem_toList_iff,
          Vector.mem_ofFn, Finset.mem_insert, Finset.mem_singleton, true_or,
          not_true_eq_false, and_false] at this
      · have hv_in_tail := v_in_tail w.support_ne_nil hv hv1
        have : mg.v[v] ∈ w.support.tail.map (fun v ↦ mg.v[v]) := by
          rw [List.mem_map]
          use v
        rw [←hedg_r.right] at this
        have : s.v ∈ (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset := by
          rw [List.mem_toFinset]
          assumption
        have : s.v ∈ (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset ∪
          (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset := by
          simp only [Finset.mem_union]
          exact Or.inl (by assumption)
        rw [←ih1, Finset.mem_union, List.mem_toFinset] at this
        simp only [List.mem_map, List.mem_toFinset] at this
        cases this with
        | inl hthis =>
          obtain ⟨a, ha⟩ := hthis
          specialize diff_curr a ha.left
          have := diff_curr.right.right.right (Eq.symm ha.right)
          contradiction
        | inr hthis =>
          obtain ⟨a, ha⟩ := hthis
          specialize diff_curr a ha.left
          have := diff_curr.right.left (Eq.symm ha.right)
          contradiction
    · have : nd = u := by symm ; ext ; assumption
      subst this
      rw [this] at huv
      use w.concat huv.left
      apply And.intro
      · intro s1 hs1
        simp only [Fin.getElem_fin, SimpleGraph.Walk.support_concat,
          List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
          List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.union_singleton, Finset.mem_insert, List.mem_toFinset, List.mem_map]
        exact build_inductive_step_goal hmg hs1 hedg_r ih1
      · apply And.intro
        · simp only [List.map_cons, hedg_r.left, Fin.getElem_fin,
          List.toFinset_cons, hedg_r.right, Finset.union_insert, Finset.insert_union,
          SimpleGraph.Walk.support_concat, List.concat_eq_append, ne_eq,
          SimpleGraph.Walk.support_ne_nil, not_false_eq_true, List.tail_append_of_ne_nil,
          List.map_append, List.map_tail, List.map_nil, List.toFinset_append,
          List.toFinset_nil, insert_empty_eq, Finset.union_singleton, List.cons_ne_self,
          List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
          have := List.dropLast_append_getLast w.support_ne_nil
          rw [w.getLast_support] at this
          nth_rewrite 2 [←this]
          simp [ih1]
        · apply And.intro
          · rw [w.concat_isPath_iff]
            exact And.intro ih2 hv
          · apply And.intro
            · simp only [SimpleGraph.Walk.length_concat, List.length_cons,
              Nat.add_right_cancel_iff]
              exact ih3
            · intro hsink
              simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append, ne_eq,
                List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil,
                List.dropLast_singleton, List.append_nil] at hsink
              have : sink hn = w.support.getLast w.support_ne_nil := by
                by_contra
                have := List.mem_dropLast_of_mem_of_ne_getLast hsink this
                exact ih4 this
              rw [w.getLast_support] at this
              rw [←this] at hedg_r
              specialize h_u_v_in_B s (head_in_head_cons _ _)
              have := h_u_v_in_B.left.left
              rw [hedg_r.left] at this
              have := (Iff.mp Finset.mem_sdiff this).left
              simp [hmg, map_graph_to_translocation_pr_aux, sink] at this
  · cases hcons_adj with
    | inl hcons_adj =>
      simp only [Fin.getElem_fin, List.mem_toFinset, List.mem_map] at hcons_adj
      obtain ⟨a, ha⟩ := hcons_adj
      have : a ≠ w.support.getLast w.support_ne_nil := by
        rw [←ha.right] at h_selv
        by_contra
        rw [this] at h_selv
        contradiction
      have := List.mem_dropLast_of_mem_of_ne_getLast ha.left this
      have : mg.p[a] ∈ (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset := by
        simp only [Fin.getElem_fin, List.map_dropLast, List.mem_toFinset]
        rw [←List.map_dropLast, List.mem_map]
        use a
      have : mg.p[a] ∈ (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset := by
        simp only [Fin.getElem_fin, List.map_dropLast, List.mem_toFinset]
        rw [←List.map_dropLast, List.mem_map]
        use a
      have : mg.p[a] ∈ (List.map (fun v ↦ mg.v[v]) w.support.tail).toFinset  ∪
        (List.map (fun v ↦ mg.p[v]) w.support.dropLast).toFinset:= by
        exact Iff.mpr Finset.mem_union (Or.inr this)
      rw [←ih1] at this
      rw [←ha.right] at hedg
      have h_ax := v_eq_v hmg hedg.left
      have h_ax : a = u := by ext ; assumption
      rw [h_ax] at this
      simp only [Fin.getElem_fin, Finset.mem_union, List.mem_toFinset, List.mem_map] at this
      cases this with
      | inl hh =>
        obtain ⟨a, ha⟩ := hh
        have := diff_curr a ha.left
        simp only [Fin.getElem_fin] at hedg_r
        rw [←hedg_r.left] at ha
        have := this.left (Eq.symm ha.right)
        contradiction
      | inr hh =>
        obtain ⟨a, ha⟩ := hh
        have := diff_curr a ha.left
        simp only [Fin.getElem_fin] at hedg_r
        rw [←hedg_r.left] at ha
        have := this.right.right.left (Eq.symm ha.right)
        contradiction
    | inr hcons_adj =>
      simp only [Fin.getElem_fin, List.mem_toFinset, List.mem_map] at hcons_adj
      rw [hedg.right] at hcons_adj
      obtain ⟨a, ha⟩ := hcons_adj
      have ha := ha.right
      have := v_neq_e hmg ha
      contradiction

theorem solution_impl_path {n S} {mg} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  (Solution mg.inst S ∧ S.length = n - 1) →
    ∃ nd : Fin n, ∃ w : g.Walk ⟨0, hn⟩ nd,
    (∀ s : Translocation, valid_translocation mg.inst.A S s ∧ (∃ u v,
    g.Adj u v ∧
      (s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v ∨ s.x = map_edge mg.v mg.p u v ∧ s.y = mg.v[u])
        ∧ (s.u = mg.v[v] ∧ s.v = mg.p[u] ∨ s.u = mg.p[u] ∧ s.v = mg.v[v])) →
    s.x ∈ (w.support.map (fun v => mg.v[v])).toFinset
    ∨ s.y ∈ (w.support.map (fun v => mg.v[v])).toFinset)
    ∧ (S.map (fun s => s.u)).toFinset ∪ (S.map (fun s => s.v)).toFinset =
    (w.support.tail.map (fun v => mg.v[v])).toFinset ∪
    (w.support.dropLast.map (fun v => mg.p[v])).toFinset
    ∧ w.IsPath ∧ w.length = S.length ∧ sink hn ∉  w.support.dropLast := by
  intro hS
  set inst := map_graph_to_translocation_pr g hn with h
  have hmgi : mg.inst = inst := by simp only [hmg, h, map_graph_to_translocation_pr]
  simp only [←hmgi] at h hS
  clear hmgi
  have hedges := S_contains_edges hmg hS
  have hIsValid := hS.left.isValid
  have pw_diff := (u_v_in_B_2 hS.left (sdiff_AB_legth h hS.left hS.right)).right
  have h_u_v_in_B := (u_v_in_B_2 hS.left (sdiff_AB_legth h hS.left hS.right)).left
  clear hS
  induction hIsValid with
  | nil =>
    use ⟨0, hn⟩
    use .nil
    apply And.intro
    · intro t hvt
      simp only [valid_translocation, List.not_mem_nil, false_and, exists_false, or_false,
        Fin.getElem_fin] at hvt
      simp only [Fin.getElem_fin, SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton]
      obtain ⟨u, v, huv⟩ := hvt.right
      cases huv.right.left with
      | inl huv =>
        have := hvt.left.left
        have hxeq := huv.left
        rw [hxeq] at this
        have := v_in_A_impl_zero hmg this
        simp only [this] at hxeq
        exact Or.inl hxeq
      | inr huv =>
        have := hvt.left.right
        have hxeq := huv.right
        rw [hxeq] at this
        have := v_in_A_impl_zero hmg this
        simp only [this] at hxeq
        exact Or.inr hxeq
    · apply And.intro
      · simp only [List.map_nil, List.toFinset_nil, Finset.union_idempotent, Fin.getElem_fin,
        SimpleGraph.Walk.support_nil, List.tail_cons, List.dropLast_singleton]
      · apply And.intro
        · simp only [SimpleGraph.Walk.isPath_iff_eq_nil]
        · apply And.intro
          · simp only [SimpleGraph.Walk.length_nil, List.length_nil]
          · simp only [SimpleGraph.Walk.support_nil, List.dropLast_singleton, List.not_mem_nil,
            not_false_eq_true]
  | @cons S' s hx _ ih =>
    have hedges_all := hedges
    rw [←List.forall_iff_forall_mem] at hedges
    rw [List.forall_cons] at hedges
    rw [List.forall_iff_forall_mem] at hedges
    have huv_in_B_all := h_u_v_in_B
    rw [←List.forall_iff_forall_mem] at huv_in_B_all
    rw [List.forall_cons] at huv_in_B_all
    rw [List.forall_iff_forall_mem] at huv_in_B_all
    cases pw_diff with
    | cons diff_curr pw_diff =>
      specialize ih hedges.right pw_diff huv_in_B_all.right
      obtain ⟨nd, w, ih⟩ := ih
      have hcons_adj := ih.left
      specialize hedges_all s (head_in_head_cons s S')
      specialize hcons_adj s (And.intro hx hedges_all)
      obtain ⟨u, v, huv⟩ := hedges_all
      use v
      have : w.support.getLast (by simp only [ne_eq, SimpleGraph.Walk.support_ne_nil,
        not_false_eq_true]) = nd := by
        exact w.getLast_support
      cases huv.right.left with
      | inl hedg =>
        cases huv.right.right with
        | inr hedg_r =>
          exact solution_impl_inductive_step hmg
            hcons_adj diff_curr huv h_u_v_in_B hedg hedg_r
            ih.right.left ih.right.right.left ih.right.right.right.left
            ih.right.right.right.right
        | inl hedg_r =>
          set s' := translocation_symm_right s with hs'
          have hsb := translocation_symm_right_inv hs'
          simp only [hsb, translocation_symm_right]
            at hcons_adj diff_curr huv h_u_v_in_B hedg hedg_r
          have := @solution_impl_inductive_step S' s' _ _ _ _ _ _ _ _ hmg
            hcons_adj ?diff_curr ?huv ?h_u_v_in_B hedg ?hedg_r
            ih.right.left ih.right.right.left ih.right.right.right.left
            ih.right.right.right.right
          rotate_left 1
          · convert diff_curr using 0
            apply Iff.intro
            all_goals
            intro ha a' hamem
            specialize ha a' hamem
            obtain ⟨_, _, _, _⟩ := ha
            exact And.intro (by assumption) (And.intro (by assumption)
              (And.intro (by assumption) (by assumption)))
          · convert huv using 0
            apply Iff.intro
            all_goals
            intro hh
            apply And.intro hh.left
            apply And.intro hh.right.left
            cases hh.right.right with
            | inl hhh => exact Or.inr (And.symm hhh)
            | inr hhh => exact Or.inl (And.symm hhh)
          · convert h_u_v_in_B using 0
            apply Iff.intro
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s' (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by symm ; assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s
                simp only [hsb, translocation_symm_right] at hh
                specialize hh (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by symm ; assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
          · convert hedg_r using 0
            apply Iff.intro
            all_goals
            intro hh
            obtain ⟨_, _⟩ := hh
            exact And.intro (by assumption) (by assumption)
          obtain ⟨w, hw⟩ := this
          use w
          apply And.intro
          · intro s1
            have hw1 := hw.left s1
            rw [valid_translocation_symm_right_head_iff _ _ s', ←hsb] at hw1
            exact hw1
          · apply And.intro
            · have hw1 := hw.right.left
              simp only [List.map_cons, List.toFinset_cons, Finset.union_insert,
                Finset.insert_union, Fin.getElem_fin, List.map_tail, List.map_dropLast]
              simp only [hs', translocation_symm_right, List.map_cons, List.toFinset_cons,
                Finset.union_insert, Finset.insert_union, Fin.getElem_fin, List.map_tail,
                List.map_dropLast] at hw1
              rw [Finset.insert_comm]
              exact hw1
            · apply And.intro hw.right.right.left
              have := hw.right.right.right
              simp only [List.length_cons]
              simp only [List.length_cons] at this
              exact this
      | inr hedg =>
        cases huv.right.right with
        | inr hedg_r =>
          set s' := translocation_symm_left s with hs'
          have hsb := translocation_symm_left_inv hs'
          simp only [hsb, translocation_symm_left] at hcons_adj diff_curr huv h_u_v_in_B hedg hedg_r
          have := solution_impl_inductive_step
            hmg
            ?hcons_adj1 diff_curr ?huv1 ?h_u_v_in_B1 ?hedg1 hedg_r
            ih.right.left ih.right.right.left ih.right.right.right.left
            ih.right.right.right.right
          rotate_left 1
          · convert hcons_adj using 0
            apply Iff.intro
            all_goals
            exact Or.symm
          · convert huv using 0
            apply Iff.intro
            all_goals
            intro hh
            apply And.intro hh.left
            apply And.intro ?_ hh.right.right
            cases hh.right.left with
            | inl hhh => exact Or.inr (And.symm hhh)
            | inr hhh => exact Or.inl (And.symm hhh)
          · convert h_u_v_in_B using 0
            apply Iff.intro
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s' (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s
                simp only [hsb, translocation_symm_left] at hh
                specialize hh (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
          · convert hedg using 0
            apply Iff.intro
            all_goals
            intro hh
            obtain ⟨_, _⟩ := hh
            exact And.intro (by assumption) (by assumption)
          obtain ⟨w, hw⟩ := this
          use w
          apply And.intro
          · intro s1
            have hw1 := hw.left s1
            rw [valid_translocation_symm_left_head_iff _ _ s', ←hsb] at hw1
            exact hw1
          · apply And.intro
            · have hw1 := hw.right.left
              simp only [List.map_cons, List.toFinset_cons, Finset.union_insert,
                Finset.insert_union, Fin.getElem_fin, List.map_tail, List.map_dropLast]
              simp only [hs', translocation_symm_left, List.map_cons, List.toFinset_cons,
                Finset.union_insert, Finset.insert_union, Fin.getElem_fin, List.map_tail,
                List.map_dropLast] at hw1
              exact hw1
            · apply And.intro hw.right.right.left
              have := hw.right.right.right
              simp only [List.length_cons]
              simp only [List.length_cons] at this
              exact this
        | inl hedg_r =>
          set s' := translocation_symm_left (translocation_symm_right s) with hs'
          have hsbi := translocation_symm_left_inv hs'
          have hsb := translocation_symm_right_inv (Eq.symm hsbi)
          rw [hsb, valid_translocation_symm_left_iff, translocation_symm_comm,
            translocation_symm_left_cancel] at hx
          simp only [hsb, translocation_symm_left] at hcons_adj diff_curr huv h_u_v_in_B hedg hedg_r
          have := @solution_impl_inductive_step S' s' _ u v _ _ _ _ _
            hmg
            ?hcons_adj2 ?diff_curr2 ?huv2 ?h_u_v_in_B2 ?hedg2 ?hedg_r2
            ih.right.left ih.right.right.left ih.right.right.right.left
            ih.right.right.right.right
          rotate_left 1
          · convert hcons_adj using 0
            apply Iff.intro
            all_goals
            exact Or.symm
          · convert diff_curr using 0
            apply Iff.intro
            all_goals
            intro ha a' hamem
            specialize ha a' hamem
            obtain ⟨_, _, _, _⟩ := ha
            exact And.intro (by assumption) (And.intro (by assumption)
              (And.intro (by assumption) (by assumption)))
          · convert huv using 0
            apply Iff.intro
            all_goals
            intro hh
            apply And.intro hh.left
            apply And.intro
            · cases hh.right.left with
              | inl hhh => exact Or.inr (And.symm hhh)
              | inr hhh => exact Or.inl (And.symm hhh)
            · cases hh.right.right with
              | inl hhh => exact Or.inr (And.symm hhh)
              | inr hhh => exact Or.inl (And.symm hhh)
          · convert h_u_v_in_B using 0
            apply Iff.intro
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s' (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by symm ; assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
            · intros hh s1
              intro hs1
              rw [List.mem_cons] at hs1
              cases hs1 with
              | inl hseq =>
                specialize hh s
                simp only [hsb, translocation_symm_left] at hh
                specialize hh (head_in_head_cons _ _)
                simp only [hseq]
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by symm ; assumption)
              | inr hmem_cons =>
                specialize hh s1 (Iff.mpr List.mem_cons (Or.inr hmem_cons))
                obtain ⟨⟨_, _⟩, _⟩ := hh
                exact And.intro (And.intro (by assumption) (by assumption)) (by assumption)
          · convert hedg using 0
            apply Iff.intro
            all_goals
            intro hh
            obtain ⟨_, _⟩ := hh
            exact And.intro (by assumption) (by assumption)
          · convert hedg_r using 0
            apply Iff.intro
            all_goals
            intro hh
            obtain ⟨_, _⟩ := hh
            exact And.intro (by assumption) (by assumption)
          obtain ⟨w, hw⟩ := this
          use w
          apply And.intro
          · intro s1
            have hw1 := hw.left s1
            rw [hsb, valid_translocation_symm_left_head_iff, translocation_symm_comm,
              translocation_symm_left_cancel, ←valid_translocation_symm_right_head_iff]
            exact hw1
          · apply And.intro
            · have hw1 := hw.right.left
              simp only [List.map_cons, List.toFinset_cons, Finset.union_insert,
                Finset.insert_union, Fin.getElem_fin, List.map_tail, List.map_dropLast]
              simp only [hs', translocation_symm_left, translocation_symm_right, List.map_cons,
                List.toFinset_cons, Finset.union_insert, Finset.insert_union, Fin.getElem_fin,
                List.map_tail, List.map_dropLast] at hw1
              rw [Finset.insert_comm]
              exact hw1
            · apply And.intro hw.right.right.left
              have := hw.right.right.right
              simp only [List.length_cons]
              simp only [List.length_cons] at this
              exact this


theorem trans_pr_imp_hamilton {inst} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (h : inst = map_graph_to_translocation_pr g hn) :
  (∃S, Solution inst S ∧ S.length = n - 1) →
  (Nonempty <| HamiltonianPath (u := ⟨0, hn⟩) (v := sink hn) g) := by
  set mg := map_graph_to_translocation_pr_aux g hn with hmg
  intro hS
  obtain ⟨S, hS⟩ := hS
  have hmgi : mg.inst = inst := by simp only [hmg, h, map_graph_to_translocation_pr]
  rw [←hmgi] at hS
  obtain ⟨nd, w, hw⟩ := solution_impl_path hmg hS
  have hpath := hw.right.right.left
  have hlen := hw.right.right.right.left
  have hsink := hw.right.right.right.right
  rw [hS.right] at hlen
  have hforall_mem := isPath_length_impl_mem hn hpath hlen
  have sink_mem := hforall_mem (sink hn)
  have : sink hn = w.support.getLast w.support_ne_nil := by
    by_contra
    have := List.mem_dropLast_of_mem_of_ne_getLast sink_mem this
    contradiction
  rw [w.getLast_support] at this
  subst this
  apply Nonempty.intro
  exact HamiltonianPath.mk w (And.intro hpath hforall_mem)
