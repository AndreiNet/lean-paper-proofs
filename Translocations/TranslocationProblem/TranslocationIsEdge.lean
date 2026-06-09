import TranslocationProblem.ProblemDevices
import TranslocationProblem.Impl2Lemmas
import TranslocationProblem.SetArguments

lemma A_union_B_aux [DecidableEq α] {A B C : Finset α} {x y : α}
  (hx : x ∈ B) (hy : y ∈ C) : (A ∪ {x, y}) ∪ ((B ∪ C) \ {x, y}) = A ∪ B ∪ C := by
  grind only [= Finset.union_insert, = Finset.insert_eq_of_mem, = Finset.insert_union,
    = Finset.mem_singleton, = Finset.mem_union, = Finset.mem_insert, = Finset.mem_sdiff]

lemma A_union_B {n} {mg} {hn : n > 0} {g}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.inst.A ∪ mg.inst.B = mg.e ∪ (mg.v.toList.toFinset ∪ mg.p.toList.toFinset) := by
  have hv : mg.v[0] ∈ mg.v.toList.toFinset := by simp only [List.mem_toFinset,
    Vector.mem_toList_iff, Vector.getElem_mem]
  have hp : mg.p[n - 1] ∈ mg.p.toList.toFinset := by simp only [List.mem_toFinset,
    Vector.mem_toList_iff, Vector.getElem_mem]
  have := @A_union_B_aux _ _ mg.e _ _ mg.v[0] mg.p[n - 1] hv hp
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.insert_union]
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.insert_union, Finset.union_assoc] at this
  exact this

lemma B_minus_A_eq_B {n} {mg} {hn : n > 0} {g : SimpleGraph <| Fin n}
    (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
    mg.inst.B \ mg.inst.A = mg.inst.B := by
    have A_int_B := A_intersect_B_eq_emptyset hmg
    simp only [sdiff_eq_left]
    rw [Finset.inter_comm] at A_int_B
    exact Iff.mpr Finset.disjoint_iff_inter_eq_empty A_int_B

lemma sdiff_AB_legth {n} {inst} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (h : inst = map_graph_to_translocation_pr g hn) :
  Solution inst S → S.length = n - 1 → (inst.B \ inst.A).card = 2 * S.length := by
  intro hS hlen
  have sol := hS
  obtain ⟨isSolution, isValid⟩ := hS
  set mg := map_graph_to_translocation_pr_aux g hn with hmg
  have hv_nodup : mg.v.toList.Nodup := v_nodup hmg
  have hp_nodup : mg.p.toList.Nodup := p_nodup hmg
  have hvp : {mg.v[0], mg.p[n - 1]} ∩
    (mg.v.toList.toFinset ∪ mg.p.toList.toFinset) = {mg.v[0], mg.p[n - 1]} := by
    simp only [Finset.mem_union, List.mem_toFinset, Vector.mem_toList_iff, Vector.getElem_mem,
      true_or, Finset.insert_inter_of_mem, or_true, Finset.singleton_inter_of_mem]
  have hvp1 : ({mg.v[0], mg.p[n - 1]} : Finset _ ).card = 2 := by
    have : mg.v[(⟨0, hn⟩ : Fin n)] ≠ mg.p[sink hn] := v_neq_p hmg
    simp only [Fin.getElem_fin, ne_eq, sink] at this
    simp only [Finset.mem_singleton, this, not_false_eq_true, Finset.card_insert_of_notMem,
      Finset.card_singleton, Nat.reduceAdd]
  have hvp2 : mg.v.toList.toFinset ∩ mg.p.toList.toFinset = ∅ := by
    ext v
    simp only [Finset.mem_inter, List.mem_toFinset, Vector.mem_toList_iff, Finset.notMem_empty,
      iff_false, not_and]
    intro hv hp
    apply Vector.getElem_of_mem at hv
    apply Vector.getElem_of_mem at hp
    obtain ⟨i, hi, hv⟩ := hv
    obtain ⟨j, hj, hp⟩ := hp
    have := @v_neq_p _ _ _ ⟨i, hi⟩ ⟨j, hj⟩ hn hmg
    rw [←hp] at hv
    contradiction
  have hvp2 : (mg.v.toList.toFinset ∪ mg.p.toList.toFinset).card =
    mg.v.toList.toFinset.card + mg.p.toList.toFinset.card := by
    have := Finset.card_union_add_card_inter mg.v.toList.toFinset mg.p.toList.toFinset
    rw [hvp2] at this
    simp only [Finset.card_empty, add_zero] at this
    assumption
  have Bcard : inst.B.card = 2 * (n - 1) := by
    simp only [h, map_graph_to_translocation_pr, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
      Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn]
      at hvp hvp1 hvp2 hv_nodup hp_nodup
    simp only [Finset.card_sdiff, hvp2, hvp, hvp1]
    have dv := Iff.mpr List.dedup_eq_self hv_nodup
    have dp := Iff.mpr List.dedup_eq_self hp_nodup
    rw [List.card_toFinset, List.card_toFinset, dv, dp]
    simp only [Vector.length_toList]
    omega
  have hmgi : mg.inst = inst := by simp only [h, hmg, map_graph_to_translocation_pr]
  have B_minus_A_card1 : (inst.B \ inst.A).card = inst.B.card := by
    rw [←hmgi, B_minus_A_eq_B hmg]
  rw [B_minus_A_card1, hlen]
  exact Bcard

lemma get_edge_1 {n} {mg} {hn : n > 0} {g} {s : Translocation} {ux vx uy i1 i2 : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (heq : map_edge mg.v mg.p ux vx + mg.v[uy] = mg.v[i1] + mg.p[i2])
  (ha : s.x = map_edge mg.v mg.p ux vx)
  (huy : mg.v[uy] = s.y)
  (hi1 : mg.v[i1] = s.u)
  (hi2 : mg.p[i2] = s.v)
  (h_adj_ux_vx : g.Adj ux vx)
  : ∃ u v,
  g.Adj u v ∧
  (s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v ∨ s.x = map_edge mg.v mg.p u v ∧ s.y = mg.v[u]) ∧
  (s.u = mg.v[v] ∧ s.v = mg.p[u] ∨ s.u = mg.p[u] ∧ s.v = mg.v[v]) := by
  simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Vector.get_ofFn] at heq ha huy hi1 hi2
  by_cases h1 : (⟨vx.val, n_2n vx.prop⟩ : Fin (2 * n)) ≤ ⟨uy.val, n_2n uy.prop⟩
  · by_cases h2 : (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) ≤ ⟨i1.val, n_2n i1.prop⟩
    · -- vx ≤ uy ≤ n + ux, ux ≤ i1 ≤ n + i2
      have h3 : (⟨uy.val, n_2n uy.prop⟩ : Fin (2 * n)) ≤ ⟨n + ux.val, n_add_n_2n ux.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have h4 : (⟨i1.val, n_2n i1.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have := (get_b3 (2 * n)).isB3 h1 h3 h2 h4 ?_
      rotate_left 1
      · convert heq using 0
        simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
      have : ux = vx := by ext ; symm ; exact this.left
      rw [this] at h_adj_ux_vx
      have := g.irrefl h_adj_ux_vx
      contradiction
    · -- vx ≤ uy ≤ n + ux, i1 ≤ ux ≤ n + i2
      have h2 :  ⟨i1.val, n_2n i1.prop⟩ ≤ (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) := by
        simp only [Fin.mk_le_mk] at h2
        simp only [Fin.mk_le_mk]
        linarith only [h2]
      have h3 : (⟨uy.val, n_2n uy.prop⟩ : Fin (2 * n)) ≤ ⟨n + ux.val, n_add_n_2n ux.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have h4 : (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have := (get_b3 (2 * n)).isB3 h1 h3 h2 h4 ?_
      rotate_left 1
      · convert heq using 0
        simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
      have heq1 : ux = i2 := by ext ; exact this.right.right
      have heq2 : vx = i1 := by ext ; exact this.left
      have heq3 : uy = i2 := by ext ; rw [this.right.left] ; exact this.right.right
      use i2, i1
      rw [heq1, heq2] at h_adj_ux_vx ha
      rw [heq3] at huy
      apply And.intro h_adj_ux_vx
      apply And.intro
      · apply Or.inr
        simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
          Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
          Vector.get_ofFn]
        exact And.intro ha (Eq.symm huy)
      · apply Or.inl
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
          Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
        exact And.intro (Eq.symm hi1) (Eq.symm hi2)
  · have h1 : ⟨uy.val, n_2n uy.prop⟩ ≤ (⟨vx.val, n_2n vx.prop⟩ : Fin (2 * n)) := by
      simp only [Fin.mk_le_mk] at h1
      simp only [Fin.mk_le_mk]
      linarith only [h1]
    by_cases h2 : (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) ≤ ⟨i1.val, n_2n i1.prop⟩
    · -- uy ≤ vx ≤ n + ux, ux ≤ i1 ≤ n + i2
      have h3 : (⟨vx.val, n_2n vx.prop⟩ : Fin (2 * n)) ≤ ⟨n + ux.val, n_add_n_2n ux.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have h4 : (⟨i1.val, n_2n i1.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have := (get_b3 (2 * n)).isB3 h1 h3 h2 h4 ?_
      rotate_left 1
      · convert heq using 0
        simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
      have heq1 : ux = i2 := by ext ; exact this.right.right
      have heq2 : vx = i1 := by ext ; exact this.right.left
      have heq3 : uy = i2 := by ext ; rw [this.left] ; exact this.right.right
      use i2, i1
      rw [heq1, heq2] at h_adj_ux_vx ha
      rw [heq3] at huy
      apply And.intro h_adj_ux_vx
      apply And.intro
      · apply Or.inr
        simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
          Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
          Vector.get_ofFn]
        exact And.intro ha (Eq.symm huy)
      · apply Or.inl
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
          Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
        exact And.intro (Eq.symm hi1) (Eq.symm hi2)
    · -- uy ≤ vx ≤ n + ux, i1 ≤ ux ≤ n + i2
      have h2 :  ⟨i1.val, n_2n i1.prop⟩ ≤ (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) := by
        simp only [Fin.mk_le_mk] at h2
        simp only [Fin.mk_le_mk]
        linarith only [h2]
      have h3 : (⟨vx.val, n_2n vx.prop⟩ : Fin (2 * n)) ≤ ⟨n + ux.val, n_add_n_2n ux.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have h4 : (⟨ux.val, n_2n ux.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
        simp only [Fin.mk_le_mk]
        omega
      have := (get_b3 (2 * n)).isB3 h1 h3 h2 h4 ?_
      rotate_left 1
      · convert heq using 0
        simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
      have : ux = vx := by ext ; symm ; exact this.right.left
      rw [this] at h_adj_ux_vx
      have := g.irrefl h_adj_ux_vx
      contradiction

lemma right_not_v_v {n} {mg} {hn : n > 0} {g} {s : Translocation} {i1 i2 : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hs : s ∈ S)
  (hS : Solution mg.inst S ∧ S.length = n - 1)
  (hax : s.x ∈ mg.e ∪ (mg.v.toList.toFinset ∪ mg.p.toList.toFinset))
  (hay : s.y ∈ mg.e ∪ (mg.v.toList.toFinset ∪ mg.p.toList.toFinset))
  (hi1 : mg.v[i1] = s.u)
  (hi2 : mg.v[i2] = s.v)
  : False := by
  obtain ⟨hS, hlen⟩ := hS
  set inst := map_graph_to_translocation_pr g hn with h
  have hmgi : mg.inst = inst := by simp only [hmg, h, map_graph_to_translocation_pr]
  rw [hmgi] at hS
  have h_AB_sdiff_length := sdiff_AB_legth h hS hlen
  have heq := s.h
  rw [←hi1, ←hi2] at heq
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.mem_union, Finset.mem_biUnion,
    SimpleGraph.mem_edgeFinset, List.mem_toFinset, Vector.mem_toList_iff,
    Vector.mem_ofFn] at hax hay hi1 hi2 heq
  cases hax with
  | inl hh =>
    obtain ⟨a, ha⟩ := hh
    obtain ⟨x, y, hxy⟩ := exists_pair a
    simp [hxy, edge_vals, map_edge] at ha
    cases ha.right with
    | inl hh1 =>
      have zero_lt_y := s.ge_zero.right.left
      rw [hh1] at heq
      have := @v_plus_v_neq_e_plus_gt_zero _ i1 i2 x y _ _ _ hn hmg zero_lt_y
      simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
      symm at heq
      contradiction
    | inr hh1 =>
      rw [hh1] at heq
      have zero_lt_y := s.ge_zero.right.left
      have := @v_plus_v_neq_e_plus_gt_zero _ i1 i2 y x _ _ _ hn hmg zero_lt_y
      simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
      symm at heq
      contradiction
  | inr hhx =>
    cases hay with
    | inl hhy =>
      obtain ⟨a, ha⟩ := hhy
      obtain ⟨x, y, hxy⟩ := exists_pair a
      simp [hxy, edge_vals, map_edge] at ha
      cases ha.right with
      | inl hh1 =>
        rw [hh1] at heq
        have zero_lt_x := s.ge_zero.left
        have := @v_plus_v_neq_e_plus_gt_zero _ i1 i2 x y _ _ _ hn hmg zero_lt_x
        simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
        symm at heq
        omega
      | inr hh1 =>
        rw [hh1] at heq
        have zero_lt_x := s.ge_zero.left
        have := @v_plus_v_neq_e_plus_gt_zero _ i1 i2 y x _ _ _ hn hmg zero_lt_x
        simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
        symm at heq
        omega
    | inr hhy =>
      cases hhx with
      | inl hhx =>
        cases hhy with
        | inl hhy =>
          obtain ⟨i3, hi3⟩ := hhx
          obtain ⟨i4, hi4⟩ := hhy
          rw [←hi3, ←hi4] at heq
          by_cases hl1 : Fin.castLE n_le_2n i1 ≤ Fin.castLE n_le_2n i2
          · by_cases hl2 : Fin.castLE n_le_2n i3 ≤ Fin.castLE n_le_2n i4
            · have := b2_of_b3 (by omega) (get_b3 (2 * n)) hl1 hl2 (Eq.symm heq)
              simp only [Fin.castLE_inj] at this
              rw [hi1, hi2, hi3, hi4] at heq
              rw [this.left, hi3] at hi1
              rw [this.right, hi4] at hi2
              have hc := And.intro hi1 hi2
              have := diff_output hS h_AB_sdiff_length s hs |> And.left
              contradiction
            · simp only [not_le] at hl2
              have : Fin.castLE n_le_2n i4 ≤ Fin.castLE n_le_2n i3 := by omega
              nth_rewrite 1 [Int.add_comm] at heq
              have := b2_of_b3 (by omega) (get_b3 (2 * n)) hl1 this (Eq.symm heq)
              simp only [Fin.castLE_inj] at this
              rw [hi1, hi2, hi3, hi4] at heq
              rw [this.left, hi4] at hi1
              rw [this.right, hi3] at hi2
              have hc := And.intro hi2 hi1
              have := diff_output hS h_AB_sdiff_length s hs |> And.right
              contradiction
          · simp only [not_le] at hl1
            have hl1 : Fin.castLE n_le_2n i2 ≤ Fin.castLE n_le_2n i1 := by omega
            nth_rewrite 2 [Int.add_comm] at heq
            by_cases hl2 : Fin.castLE n_le_2n i3 ≤ Fin.castLE n_le_2n i4
            · have := b2_of_b3 (by omega) (get_b3 (2 * n)) hl1 hl2 (Eq.symm heq)
              simp only [Fin.castLE_inj] at this
              rw [hi1, hi2, hi3, hi4] at heq
              rw [this.right, hi4] at hi1
              rw [this.left, hi3] at hi2
              have hc := And.intro hi2 hi1
              have := diff_output hS h_AB_sdiff_length s hs |> And.right
              contradiction
            · simp only [not_le] at hl2
              have : Fin.castLE n_le_2n i4 ≤ Fin.castLE n_le_2n i3 := by omega
              nth_rewrite 1 [Int.add_comm] at heq
              have := b2_of_b3 (by omega) (get_b3 (2 * n)) hl1 this (Eq.symm heq)
              simp only [Fin.castLE_inj] at this
              rw [hi1, hi2, hi3, hi4] at heq
              rw [this.right, hi3] at hi1
              rw [this.left, hi4] at hi2
              have hc := And.intro hi1 hi2
              have := diff_output hS h_AB_sdiff_length s hs |> And.left
              contradiction
        | inr hhy =>
          obtain ⟨i4, hi4⟩ := hhy
          rw [←hi4] at heq
          have zero_ge_x := s.ge_zero.left
          have zero_gt_1 := (get_b3 (2 * n)).pos ⟨n + i4.val, n_add_n_2n i4.prop⟩
          have : i1 < 2 * n := by omega
          have le_max_1 := inst_max hmg this
          have : i2 < 2 * n := by omega
          have le_max_2 := inst_max hmg this
          have zero_le_m := inst_zero_le_max hmg
          simp [hmg, map_graph_to_translocation_pr_aux] at le_max_1 le_max_2
          simp only [Fin.getElem_fin, gt_iff_lt] at zero_gt_1
          nlinarith only [le_max_1, le_max_2, zero_ge_x, zero_gt_1, zero_le_m, heq]
      | inr hhx =>
        obtain ⟨i3, hi3⟩ := hhx
        rw [←hi3] at heq
        have zero_ge_y := s.ge_zero.right.left
        have zero_gt_1 := (get_b3 (2 * n)).pos ⟨n + i3.val, n_add_n_2n i3.prop⟩
        have : i1 < 2 * n := by omega
        have le_max_1 := inst_max hmg this
        have : i2 < 2 * n := by omega
        have le_max_2 := inst_max hmg this
        have zero_le_m := inst_zero_le_max hmg
        simp [hmg, map_graph_to_translocation_pr_aux] at le_max_1 le_max_2
        simp only [Fin.getElem_fin, gt_iff_lt] at zero_gt_1
        nlinarith only [le_max_1, le_max_2, zero_ge_y, zero_gt_1, zero_le_m, heq]

lemma get_right_v_p {n} {mg} {hn : n > 0} {g} {s : Translocation} {i1 i2 : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hs : s ∈ S)
  (hS : Solution mg.inst S ∧ S.length = n - 1)
  (hax : s.x ∈ mg.e ∪ (mg.v.toList.toFinset ∪ mg.p.toList.toFinset))
  (hay : s.y ∈ mg.e ∪ (mg.v.toList.toFinset ∪ mg.p.toList.toFinset))
  (hi1 : mg.v[i1] = s.u)
  (hi2 : mg.p[i2] = s.v)
  : ∃ u v: Fin n, g.Adj u v ∧ (s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v
    ∨ s.x = map_edge mg.v mg.p u v ∧ s.y = mg.v[u]) ∧
    (s.u = mg.v[v] ∧ s.v = mg.p[u] ∨ s.u = mg.p[u] ∧ s.v = mg.v[v]) := by
  obtain ⟨hS, hlen⟩ := hS
  set inst := map_graph_to_translocation_pr g hn with h
  have hmgi : mg.inst = inst := by simp only [hmg, h, map_graph_to_translocation_pr]
  rw [hmgi] at hS
  have h_AB_sdiff_length := sdiff_AB_legth h hS hlen
  have heq := s.h
  rw [←hi1, ←hi2] at heq
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.mem_union, Finset.mem_biUnion,
    SimpleGraph.mem_edgeFinset, List.mem_toFinset, Vector.mem_toList_iff,
    Vector.mem_ofFn] at hax hay hi1 hi2 heq
  cases hax with
  | inl hax =>
    simp only [edge_vals, map_edge, Vector.get_ofFn] at hax
    obtain ⟨a, ha⟩ := hax
    obtain ⟨ux, vx, huvx⟩ := exists_pair a
    rw [huvx.left] at ha
    simp only [SimpleGraph.mem_edgeSet, Sym2.lift_mk, Finset.mem_insert,
      Finset.mem_singleton] at ha
    cases hay with
    | inl hay =>
      simp only [edge_vals, map_edge, Vector.get_ofFn] at hay
      obtain ⟨a', ha'⟩ := hay
      obtain ⟨uy, vy, huvy⟩ := exists_pair a'
      rw [huvy.left] at ha'
      simp only [SimpleGraph.mem_edgeSet, Sym2.lift_mk, Finset.mem_insert,
        Finset.mem_singleton] at ha'
      cases ha.right with
      | inl ha =>
        cases ha'.right with
        | inl ha' =>
          rw [ha, ha'] at heq
          symm at heq
          have := v_plus_p_neq_e_plus_e (i1 := i1) (i2 := i2) (x := ux)
            (y := vx) (u := uy) (v := vy) hmg
          simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
          contradiction
        | inr ha' =>
          rw [ha, ha'] at heq
          symm at heq
          have := v_plus_p_neq_e_plus_e (i1 := i1) (i2 := i2) (x := ux)
            (y := vx) (u := vy) (v := uy) hmg
          simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
          contradiction
      | inr ha =>
        cases ha'.right with
        | inl ha' =>
          rw [ha, ha'] at heq
          symm at heq
          have := v_plus_p_neq_e_plus_e (i1 := i1) (i2 := i2) (x := vx)
            (y := ux) (u := uy) (v := vy) hmg
          simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
          contradiction
        | inr ha' =>
          rw [ha, ha'] at heq
          symm at heq
          have := v_plus_p_neq_e_plus_e (i1 := i1) (i2 := i2) (x := vx)
            (y := ux) (u := vy) (v := uy) hmg
          simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
          contradiction
    | inr hay =>
      have h_adj_ux_vx := ha.left
      cases ha.right with
      | inl ha =>
        cases hay with
        | inl hay =>
          obtain ⟨uy, huy⟩ := hay
          rw [←huy, ha] at heq
          exact get_edge_1 hmg
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact heq)
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact ha)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact huy)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi1)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi2)
            h_adj_ux_vx
        | inr hay =>
          obtain ⟨uy, huy⟩ := hay
          rw [←huy, ha] at heq
          have := v_plus_p_neq_e_plus_p (i1 := i1) (i2 := i2) (u := uy) (x := ux) (y := vx) hmg
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, map_edge,
            Vector.get_ofFn, ne_eq] at this
          have := this ?_
          rotate_left 1
          · convert heq using 0
            omega
          contradiction
      | inr ha =>
        cases hay with
        | inl hay =>
          obtain ⟨uy, huy⟩ := hay
          rw [←huy, ha] at heq
          exact get_edge_1 hmg
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact heq)
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact ha)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact huy)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi1)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi2)
            (g.adj_symm h_adj_ux_vx)
        | inr hay =>
          obtain ⟨uy, huy⟩ := hay
          rw [←huy, ha] at heq
          have := v_plus_p_neq_e_plus_p (i1 := i1) (i2 := i2) (u := uy) (x := vx) (y := ux) hmg
          simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
            Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, map_edge,
            Vector.get_ofFn, ne_eq] at this
          have := this ?_
          rotate_left 1
          · convert heq using 0
            omega
          contradiction
  | inr hax =>
    cases hax with
    | inl ha =>
      obtain ⟨x, hx⟩ := ha
      rw [←hx] at heq
      cases hay with
      | inl hay =>
        obtain ⟨a, ha⟩ := hay
        obtain ⟨u, v, huv⟩ := exists_pair a
        rw [huv.left] at ha
        simp [edge_vals, map_edge] at ha
        have h_adj_ux_vx := ha.left
        cases ha.right with
        | inl hy =>
          rw [hy] at heq
          set s' := translocation_symm_left s with hs'
          have hinv := translocation_symm_left_inv hs'
          simp only [hinv, translocation_symm_left] at hx hy hi1 hi2
          have := get_edge_1 hmg (s := s') ?_
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact hy)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hx)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi1)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi2)
            h_adj_ux_vx
          rotate_left 1
          · convert heq using 0
            simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
            omega
          obtain ⟨ru, rv, huvr⟩ := this
          simp only [hs', translocation_symm_left] at huvr
          use ru, rv
          apply And.intro huvr.left
          refine And.intro ?_ (huvr.right.right)
          cases huvr.right.left with
          | inl hh => exact Or.inr (And.symm hh)
          | inr hh => exact Or.inl (And.symm hh)
        | inr hy =>
          rw [hy] at heq
          set s' := translocation_symm_left s with hs'
          have hinv := translocation_symm_left_inv hs'
          simp only [hinv, translocation_symm_left] at hx hy hi1 hi2
          have := get_edge_1 hmg (s := s') ?_
            (by simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
                exact hy)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hx)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi1)
            (by simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton] ; exact hi2)
            (g.adj_symm h_adj_ux_vx)
          rotate_left 1
          · convert heq using 0
            simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
            omega
          obtain ⟨ru, rv, huvr⟩ := this
          simp only [hs', translocation_symm_left] at huvr
          use ru, rv
          apply And.intro huvr.left
          refine And.intro ?_ (huvr.right.right)
          cases huvr.right.left with
          | inl hh => exact Or.inr (And.symm hh)
          | inr hh => exact Or.inl (And.symm hh)
      | inr hay =>
        cases hay with
        | inl hy =>
          obtain ⟨y, hy⟩ := hy
          rw [←hy] at heq
          have := v_plus_v_neq_v_plus_p hmg (i1 := x) (i2 := y) (x := i1) (y := i2)
          have := this ?_
          rotate_left 1
          · convert heq using 0
            simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
          contradiction
        | inr hy =>
          obtain ⟨y, hy⟩ := hy
          rw [←hy] at heq
          have hr1 : (⟨x.val, n_2n x.prop⟩ : Fin (2 * n)) ≤ ⟨n + y.val, n_add_n_2n y.prop⟩ := by
            simp only [Fin.mk_le_mk] ; omega
          have hr2 : (⟨i1.val, n_2n i1.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
            simp only [Fin.mk_le_mk] ; omega
          have := b2_of_b3_2 (n_2n hn) (get_b3 (2 * n)) hr1 hr2 ?_
          rotate_left 1
          · convert heq using 0
            simp only [Fin.getElem_fin]
            omega
          simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
          simp only [this.left, hi1] at hx
          simp only [this.right, hi2] at hy
          have := diff_output hS h_AB_sdiff_length s hs
          have := this.left (And.intro (Eq.symm hx) (Eq.symm hy))
          contradiction
    | inr ha =>
      obtain ⟨x, hx⟩ := ha
      rw [←hx] at heq
      cases hay with
      | inl hay =>
        obtain ⟨a, ha⟩ := hay
        obtain ⟨u, v, huv⟩ := exists_pair a
        rw [huv.left] at ha
        simp only [SimpleGraph.mem_edgeSet, edge_vals, map_edge, Vector.get_ofFn, Sym2.lift_mk,
          Finset.mem_insert, Finset.mem_singleton] at ha
        cases ha.right with
        | inl hy =>
          rw [hy] at heq
          have := v_plus_p_neq_e_plus_p hmg (i1 := i1) (i2 := i2) (x := u) (y := v) (u := x)
          have := this ?_
          rotate_left 1
          · convert heq using 0
            simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, map_edge,
              Vector.get_ofFn]
            omega
          contradiction
        | inr hy =>
          rw [hy] at heq
          have := v_plus_p_neq_e_plus_p hmg (i1 := i1) (i2 := i2) (x := v) (y := u) (u := x)
          have := this ?_
          rotate_left 1
          · convert heq using 0
            simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, map_edge,
              Vector.get_ofFn]
            omega
          contradiction
      | inr hay =>
        cases hay with
        | inl hay =>
          obtain ⟨y, hy⟩ := hay
          rw [←hy] at heq
          have hr1 : (⟨y.val, n_2n y.prop⟩ : Fin (2 * n)) ≤ ⟨n + x.val, n_add_n_2n x.prop⟩ := by
            simp only [Fin.mk_le_mk] ; omega
          have hr2 : (⟨i1.val, n_2n i1.prop⟩ : Fin (2 * n)) ≤ ⟨n + i2.val, n_add_n_2n i2.prop⟩ := by
            simp only [Fin.mk_le_mk] ; omega
          have := b2_of_b3_2 (n_2n hn) (get_b3 (2 * n)) hr1 hr2 ?_
          rotate_left 1
          · convert heq using 0
            simp only [Fin.getElem_fin]
            omega
          simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
          simp only [this.left, hi1] at hy
          simp only [this.right, hi2] at hx
          have := diff_output hS h_AB_sdiff_length s hs
          have := this.right (And.intro (Eq.symm hx) (Eq.symm hy))
          contradiction
        | inr hay =>
          obtain ⟨y, hy⟩ := hay
          rw [←hy] at heq
          have := p_plus_p_neq_v_plus_p hmg (i1 := x) (i2 := y) (x := i1) (y := i2)
          have := this ?_
          rotate_left 1
          · convert heq using 0
            simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
              Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton]
          contradiction

lemma separate_B {n} {mg} {hn : n > 0} {g}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  : mg.inst.B = (mg.v.toList.toFinset \ {mg.v[0]}) ∪
  (mg.p.toList.toFinset \ {mg.p[n - 1]'(by omega)}) := by
  have hB : mg.inst.B = (mg.v.toList.toFinset ∪ mg.p.toList.toFinset) \ {mg.v[0], mg.p[n - 1]} := by
    simp only [hmg, map_graph_to_translocation_pr_aux]
  have hnmem1 := v_nmem_p hmg (u := ⟨0, hn⟩)
  simp only [Fin.getElem_fin] at hnmem1
  have hnmem2 := p_nmem_v hmg (u := ⟨n - 1, by omega⟩)
  simp only [Fin.getElem_fin] at hnmem2
  rw [hB]
  ext
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, Vector.mem_toList_iff,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  aesop

lemma card_left {n} {mg} {hn : n > 0} {g}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  : (mg.p.toList.toFinset \ {mg.p[n - 1]}).card = n - 1 := by
  have : {mg.p[n - 1]} ∩ mg.p.toList.toFinset = {mg.p[n - 1]} := by
    ext
    simp only [List.mem_toFinset, Vector.mem_toList_iff, Vector.getElem_mem,
      Finset.singleton_inter_of_mem, Finset.mem_singleton]
  rw [Finset.card_sdiff, this]
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Finset.card_singleton]
  rw [List.card_toFinset]
  have : mg.p.toList.Nodup := by
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton]
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Vector.length_toList] at hi hj
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, ne_eq, add_right_inj]
    have := b1_of_b3_2 (i₁ := ⟨n + i, n_add_n_2n hi⟩) (i₂ := ⟨n + j, n_add_n_2n hj⟩)
      (n_2n hn) (get_b3 (2 * n))
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
    intro x
    specialize this x
    linarith only [this, hij]
  rw [←List.dedup_eq_self] at this
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton] at this
  rw [this]
  simp only [Vector.length_toList]

lemma S_contains_edges {n} {mg} {hn} {g}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  Solution mg.inst S ∧ S.length = n - 1 →
  ∀ s ∈ S, ∃ u v: Fin n, g.Adj u v ∧ (s.x = mg.v[u] ∧ s.y = map_edge mg.v mg.p u v
    ∨ s.x = map_edge mg.v mg.p u v ∧ s.y = mg.v[u]) ∧
    (s.u = mg.v[v] ∧ s.v = mg.p[u] ∨ s.u = mg.p[u] ∧ s.v = mg.v[v])
    := by
  have b3 := get_b3 (2 * n)
  intro hS
  obtain ⟨hS, hlen⟩ := hS
  set inst := map_graph_to_translocation_pr g hn with h
  have hmgi : mg.inst = inst := by simp only [hmg, h, map_graph_to_translocation_pr]
  rw [hmgi] at hS
  have h_AB_sdiff_length := sdiff_AB_legth h hS hlen
  have h_right_in_B := u_v_in_B_2 hS h_AB_sdiff_length
  have h_left_in_AB := x_y_in_A_union_B hS h_AB_sdiff_length
  intro s hs
  have hc := h_right_in_B.left s hs
  have hsu := mem_superset hc.left.left
  have hsv := mem_superset hc.left.right
  simp only [h, map_graph_to_translocation_pr, map_graph_to_translocation_pr_aux, Fin.getElem_fin,
    Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton, Finset.mem_sdiff,
    Finset.mem_union, List.mem_toFinset, Vector.mem_toList_iff, Vector.mem_ofFn,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hsu hsv
  have hsu : (∃ i : Fin n, mg.v[i] = s.u) ∨ (∃ i : Fin n, mg.p[i] = s.u) := by
    cases hsu.left with
    | inl hsu =>
      obtain ⟨i, hi⟩ := hsu
      apply Or.inl
      use i
      convert hi using 0
      simp [hmg, map_graph_to_translocation_pr_aux]
    | inr hsu =>
      obtain ⟨i, hi⟩ := hsu
      apply Or.inr
      use i
      convert hi using 0
      simp [hmg, map_graph_to_translocation_pr_aux]
  have hsv : (∃ i : Fin n, mg.v[i] = s.v) ∨ (∃ i : Fin n, mg.p[i] = s.v) := by
    cases hsv.left with
    | inl hsv =>
      obtain ⟨i, hi⟩ := hsv
      apply Or.inl
      use i
      convert hi using 0
      simp [hmg, map_graph_to_translocation_pr_aux]
    | inr hsv =>
      obtain ⟨i, hi⟩ := hsv
      apply Or.inr
      use i
      convert hi using 0
      simp [hmg, map_graph_to_translocation_pr_aux]
  rw [←hmgi] at h_left_in_AB
  rw [A_union_B hmg] at h_left_in_AB
  have h_left_in_AB_2 := h_left_in_AB
  specialize h_left_in_AB s hs
  obtain ⟨hax, hay⟩ := h_left_in_AB
  cases hsu with
  | inl hsul =>
    cases hsv with
    | inl hsvl =>
      obtain ⟨i1, hi1⟩ := hsul
      obtain ⟨i2, hi2⟩ := hsvl
      have := right_not_v_v hmg hs ⟨by rw [←hmgi] at hS ; exact hS, hlen⟩ hax hay hi1 hi2
      contradiction
    | inr hsvl =>
      obtain ⟨i1, hi1⟩ := hsul
      obtain ⟨i2, hi2⟩ := hsvl
      exact get_right_v_p hmg hs ⟨by rw [←hmgi] at hS ; exact hS, hlen⟩ hax hay hi1 hi2
  | inr hsul =>
    cases hsv with
    | inl hsvl =>
      set s' := translocation_symm_right s with hs'
      have hinv := translocation_symm_right_inv hs'
      obtain ⟨i1, hi1⟩ := hsul
      obtain ⟨i2, hi2⟩ := hsvl
      have hsol_rep := solution_replace_symm_right hS s
      have h_mem_s' := list_mem_replace hs (s' := (translocation_symm_right s))
      have hlen1: (S.replace s (translocation_symm_right s)).length = n - 1 := by
        simp only [List.length_replace]
        exact hlen
      have := get_right_v_p (S := S.replace s (translocation_symm_right s))
        (s := translocation_symm_right s)
        hmg h_mem_s' ⟨by rw [←hmgi] at hsol_rep ; exact hsol_rep, hlen1⟩ (by
          simp only [translocation_symm_right]
          exact hax
        ) (by
          simp only [translocation_symm_right]
          exact hay
        ) (by
          simp only [translocation_symm_right]
          exact hi2
        ) (by
          simp only [translocation_symm_right]
          exact hi1
        )
      simp only [translocation_symm_right, Fin.getElem_fin] at this
      simp only [Fin.getElem_fin]
      obtain ⟨u, v, huv⟩ := this
      use u, v
      apply And.intro huv.left
      apply And.intro huv.right.left
      cases huv.right.right with
      | inl hh => exact Or.inr (And.symm hh)
      | inr hh => exact Or.inl (And.symm hh)
    | inr hsvl =>
      have hr : ∀ s ∈ S, s.u ∈ inst.B ∧ s.v ∈ inst.B := by
        intro s hs
        have := h_right_in_B.left s hs
        simp at this
        exact And.intro this.left.left.left this.left.right.left
      have hd : ∀ s ∈ S, s.u ≠ s.v := by
        intro s hs
        have := h_right_in_B.left s hs
        simp at this
        exact this.right
      rw [← hmgi, separate_B hmg, Finset.union_comm] at hr
      have hcard_left := card_left hmg
      have := translocation_comp hr hd hs ?_ ?_ h_right_in_B.right hcard_left hlen
      rotate_left 1
      · simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, Finset.mem_sdiff, List.mem_toFinset,
        Vector.mem_toList_iff, Vector.mem_ofFn, Finset.mem_singleton] at ⊢ hsul
        apply And.intro hsul
        exact hsu.right.right
      · simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, Finset.mem_sdiff, List.mem_toFinset,
        Vector.mem_toList_iff, Vector.mem_ofFn, Finset.mem_singleton] at ⊢ hsvl
        apply And.intro hsvl
        exact hsv.right.right
      obtain ⟨s', hs'⟩ := this
      simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, Finset.mem_sdiff, List.mem_toFinset,
        Vector.mem_toList_iff, Vector.mem_ofFn, Finset.mem_singleton] at hs'
      have hi1 := hs'.right.left
      have hi2 := hs'.right.right
      obtain ⟨i1, hi1⟩ := hi1.left
      obtain ⟨i2, hi2⟩ := hi2.left
      specialize h_left_in_AB_2 s' hs'.left
      have := right_not_v_v hmg hs'.left ⟨by rw [←hmgi] at hS ; exact hS, hlen⟩
        h_left_in_AB_2.left h_left_in_AB_2.right (by
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
          Finset.union_insert, Finset.union_singleton]
        exact hi1
      ) (by
        simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
          Finset.union_insert, Finset.union_singleton]
        exact hi2
      )
      contradiction
