import TranslocationProblem.ProblemDevices
import TranslocationProblem.Lemmas

lemma inst_zero_le_max {g} {mg} {h : n > 0} (hmg : mg = map_graph_to_translocation_pr_aux g h) :
  0 ≤ (get_b3 (2 * n)).v.toList.maximum.getD 0 := by
  have h1 : (get_b3 (2 * n)).v[0] ≤ (get_b3 (2 * n)).v.toList.maximum.getD 0 := by
    have : 0 < 2 * n := by omega
    have := inst_max hmg this
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have h2 : 0 ≤ (get_b3 (2 * n)).v[0] := by
    have := (get_b3 (2 * n)).pos ⟨0, n_2n h⟩
    simp only [Fin.getElem_fin, gt_iff_lt] at this
    omega
  omega

theorem v_eq_v {g} {mg} {i j : Fin n} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i] = mg.v[j] → i.val = j.val := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton]
  intro h
  have := @b1_of_b3_2 _ ⟨i.val, n_2n i.prop⟩ ⟨j.val, n_2n j.prop⟩ (by linarith only [hn])
    (get_b3 (2 * n)) h
  simp only [Fin.mk.injEq] at this
  exact this

theorem v_neq_e {g} {mg} {i : Fin n} {hn} {u v}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i] ≠ map_edge mg.v mg.p u v := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn, ne_eq]
  intro h
  have h : (get_b3 (2 * n)).v[↑i] + -(get_b3 (2 * n)).v[↑v] +
    -(get_b3 (2 * n)).v[n + ↑u] + (get_b3 (2 * n)).v[↑u]  =
    4 * (Option.getD (get_b3 (2 * n)).v.toList.maximum 0 + 1) := by
    simp +arith only [Int.reduceNeg, neg_mul, one_mul] at h
    simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
    exact h
  rename_i c
  clear c
  have h1 : (get_b3 (2 * n)).v[i] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n i.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have h2 : -(get_b3 (2 * n)).v[↑v] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have hm := inst_max hmg (n_2n v.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at hm
    have ge_0 := (get_b3 (2 * n)).pos (v.castLE n_le_2n)
    have : -(get_b3 (2 * n)).v[v.castLE n_le_2n] ≤
      (get_b3 (2 * n)).v[v.castLE n_le_2n] := by omega
    have := Int.le_trans this hm
    assumption
  have h3 : -(get_b3 (2 * n)).v[n + ↑u] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have hu := u.prop
    have hnu : n + u.val < 2 * n := by linarith
    have hm := inst_max hmg hnu
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at hm
    have ge_0 := (get_b3 (2 * n)).pos ⟨n + u, n_add_n_2n u.prop⟩
    have : -(get_b3 (2 * n)).v[(⟨n + u, n_add_n_2n u.prop⟩ : Fin (2 * n))] ≤
      (get_b3 (2 * n)).v[(⟨n + u, n_add_n_2n u.prop⟩ : Fin (2 * n))] := by omega
    have := Int.le_trans this hm
    assumption
  have h4 : (get_b3 (2 * n)).v[u] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (u.castLE n_le_2n).prop
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton, Fin.castLE] at this
    exact this
  nlinarith

theorem v_nmem_e {g} {mg} {hn} {u : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[u] ∉ mg.e := by
  intro h
  simp only [hmg, map_graph_to_translocation_pr_aux, edge_vals, map_edge, Fin.getElem_fin,
    Vector.get_ofFn, Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
    Finset.mem_biUnion, SimpleGraph.mem_edgeFinset] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨x, y, hxy⟩ := exists_pair a
  simp [hxy.left] at ha
  have := ha.right
  cases this with
  | inl hc1 =>
    have := @v_neq_e _ _ _ u hn x y hmg
    simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
    contradiction
  | inr hc1 =>
    have := @v_neq_e _ _ _ u hn y x hmg
    simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
    contradiction

lemma v_neq_p {g} {mg} {i j : Fin n} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i] ≠ mg.p[j] := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, ne_eq]
  have h1 : (get_b3 (2 * n)).v[i] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (i.castLE n_le_2n).prop
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton, Fin.castLE] at this
    exact this
  have gt_0 : 0 < Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := (get_b3 (2 * n)).pos ⟨i.val, n_2n i.prop⟩
    simp only [Fin.getElem_fin, gt_iff_lt] at this
    exact Int.lt_of_lt_of_le this h1
  have hg : (get_b3 (2 * n)).v[i] ≤ 4 * Option.getD (get_b3 (2 * n)).v.toList.maximum 0 + 3 := by
    nlinarith
  intro h
  simp only [Fin.getElem_fin, h] at hg
  have h2 : (get_b3 (2 * n)).v[n + ↑j] > 0 := (get_b3 (2 * n)).pos ⟨n + j, n_add_n_2n j.prop⟩
  nlinarith

lemma p_neq_e {g} {mg} {i : Fin n} {hn} {u v}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (h : mg.p[i] = map_edge mg.v mg.p u v) : u = v := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at h
  have h : (get_b3 (2 * n)).v[0] + (get_b3 (2 * n)).v[u] + (get_b3 (2 * n)).v[n + i] =
    (get_b3 (2 * n)).v[0] + (get_b3 (2 * n)).v[v] + (get_b3 (2 * n)).v[n + u] := by
    simp +arith only [Int.reduceNeg, neg_mul, one_mul] at h
    simp +arith only [Fin.getElem_fin, Int.reduceNeg, neg_mul, one_mul]
    exact h
  rename_i c
  clear c
  have zero_le_u : (⟨0, n_2n hn⟩ : Fin (2 * n)) ≤ ⟨_, n_2n u.prop⟩ := by
    simp only [Fin.mk_le_mk, zero_le]
  have u_le_ni : (⟨_, n_2n u.prop⟩  : Fin (2 * n)) ≤ ⟨_, n_add_n_2n i.prop⟩ := by
    have hu := u.prop
    simp only [Fin.mk_le_mk]
    linarith
  have zero_le_v : (⟨0, n_2n hn⟩ : Fin (2 * n)) ≤ ⟨_, n_2n v.prop⟩ := by
    simp only [Fin.mk_le_mk, zero_le]
  have v_le_nu : (⟨_, n_2n v.prop⟩ : Fin (2 * n)) ≤ ⟨_, n_add_n_2n u.prop⟩ := by
    have hu := v.prop
    simp only [Fin.mk_le_mk]
    linarith
  obtain ⟨_, hp, _⟩ := (get_b3 (2 * n)).isB3 zero_le_u u_le_ni zero_le_v v_le_nu h
  simp only [Fin.mk.injEq] at hp
  -- TODO: replace this
  grind only

lemma v_nodup {g : SimpleGraph (Fin n)} {mg} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v.toList.Nodup := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, List.nodup_iff_getElem?_ne_getElem?,
    Vector.length_toList, Vector.getElem?_toList, Vector.getElem?_ofFn, ne_eq]
  intro i j hij hj
  have hi : i < n := by omega
  simp only [hi, ↓reduceDIte, hj, Option.some.injEq, ne_eq]
  intro heq
  have := @b1_of_b3 _ ⟨i, n_2n hi⟩ ⟨j, n_2n hj⟩ (n_2n hn) (get_b3 (2 * n)) heq
  simp only [Fin.mk.injEq] at this
  omega

lemma p_nodup {g : SimpleGraph (Fin n)} {mg} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.p.toList.Nodup := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, List.nodup_iff_getElem?_ne_getElem?,
    Vector.length_toList, Vector.getElem?_toList, Vector.getElem?_ofFn, ne_eq]
  intro i j hij hj
  have hi : i < n := by omega
  simp only [hi, ↓reduceDIte, hj, Option.some.injEq, add_right_inj, ne_eq]
  intro heq
  have := @b1_of_b3 _ ⟨n + i, n_add_n_2n hi⟩ ⟨n + j, n_add_n_2n hj⟩ (n_2n hn) (get_b3 (2 * n)) heq
  simp only [Fin.mk.injEq] at this
  omega

lemma wtv {a b c : Int} (hbc : b < c) (ha : 0 < a) :
    b < c + a := by
  apply lt_of_lt_of_le hbc
  omega

lemma edge_lemma {mg} {g : SimpleGraph (Fin n)} {hn}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn)
  (hv : v ∈ mg.e) : ∃ x y, g.Adj x y ∧ v = map_edge mg.v mg.p x y := by
  rw [hmg, map_graph_to_translocation_pr_aux] at hv
  simp only [Fin.getElem_fin, Finset.mem_biUnion, SimpleGraph.mem_edgeFinset] at hv
  obtain ⟨a, ha⟩ := hv
  obtain ⟨ha, hv⟩ := ha
  obtain ⟨x, y, hxy⟩ := exists_pair a
  have ha1 := ha
  rw [hxy.left] at ha hv
  rw [hxy.right] at ha1
  simp at ha1 ha
  simp only [edge_vals, map_edge, Vector.get_ofFn, Sym2.lift_mk, Finset.mem_insert,
    Finset.mem_singleton] at hv
  simp only [map_edge, hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, Vector.get_ofFn]
  cases hv with
  | inl hv => use x, y
  | inr hv => use y, x

lemma v_plus_v_neq_e_plus_gt_zero {i1 i2 x y : Fin n} {val : Int} {g : SimpleGraph (Fin n)}
  {mg} {hn} (hmg : mg = map_graph_to_translocation_pr_aux g hn) (hval : 0 < val) :
  mg.v[i1] + mg.v[i2] ≠ map_edge mg.v mg.p x y + val := by
  intro heq
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at heq
  have h_le_1: (get_b3 (2 * n)).v[i1.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i1_n : i1 < 2 * n := n_2n i1.prop
    have := inst_max hmg h_i1_n
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have h_le_2: (get_b3 (2 * n)).v[i2.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i2_n : i2.val < 2 * n := n_2n i2.prop
    have := inst_max hmg (h_i2_n)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have h_le_3: (get_b3 (2 * n)).v[x.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i2_n : x.val < 2 * n := n_2n x.prop
    have := inst_max hmg h_i2_n
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have zero_le_max := inst_zero_le_max hmg
  have h_pos_x := (get_b3 (2 * n)).pos ⟨y.val, n_2n y.prop⟩
  have h_pos_y := (get_b3 (2 * n)).pos ⟨n + x.val, n_add_n_2n x.prop⟩
  simp only [Fin.getElem_fin, gt_iff_lt] at h_pos_x h_pos_y heq h_le_1 h_le_2
  nlinarith only [h_le_1, h_le_2, h_pos_x, h_pos_y, heq, zero_le_max, hval, h_le_3]

lemma v_plus_v_neq_v_plus_p {i1 i2 x y : Fin n} {g : SimpleGraph (Fin n)}
  {mg} {hn} (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i1] + mg.v[i2] ≠ mg.v[x] + mg.p[y] := by
  intro heq
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton] at heq
  have : (get_b3 (2 * n)).v[i1.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i1_n : i1 < 2 * n := n_2n i1.prop
    have := inst_max hmg h_i1_n
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : (get_b3 (2 * n)).v[i2.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i2_n : i2.val < 2 * n := n_2n i2.prop
    have := inst_max hmg (h_i2_n)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : 0 < (get_b3 (2 * n)).v[x.val] := (get_b3 (2 * n)).pos ⟨x.val, n_2n x.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + y.val] := (get_b3 (2 * n)).pos ⟨n + y.val, n_add_n_2n y.prop⟩
  have zero_le_max := inst_zero_le_max hmg
  nlinarith

lemma p_plus_p_neq_v_plus_p {i1 i2 x y : Fin n} {g : SimpleGraph (Fin n)}
  {mg} {hn} (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.p[i1] + mg.p[i2] ≠ mg.v[x] + mg.p[y] := by
  intro heq
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton] at heq
  have : (get_b3 (2 * n)).v[x.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i1_n : x < 2 * n := n_2n x.prop
    have := inst_max hmg h_i1_n
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : (get_b3 (2 * n)).v[n + y.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have h_i2_n : n + y < 2 * n := n_add_n_2n y.prop
    have := inst_max hmg (h_i2_n)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : 0 < (get_b3 (2 * n)).v[n + i1.val] := (get_b3 (2 * n)).pos ⟨n + i1.val, n_add_n_2n i1.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + i2.val] := (get_b3 (2 * n)).pos ⟨n + i2.val, n_add_n_2n i2.prop⟩
  have zero_le_max := inst_zero_le_max hmg
  nlinarith

lemma v_plus_p_neq_e_plus_e {i1 i2 x y u v : Fin n} {g : SimpleGraph (Fin n)}
  {mg} {hn} (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i1] + mg.p[i2] ≠ map_edge mg.v mg.p x y + map_edge mg.v mg.p u v := by
  intro h
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at h
  have : (get_b3 (2 * n)).v[i1.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n i1.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : (get_b3 (2 * n)).v[n + i2.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_add_n_2n i2.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : 0 ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := inst_zero_le_max hmg
  have : 0 < (get_b3 (2 * n)).v[y.val] := (get_b3 (2 * n)).pos ⟨y.val, n_2n y.prop⟩
  have : 0 < (get_b3 (2 * n)).v[v.val] := (get_b3 (2 * n)).pos ⟨v.val, n_2n v.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + x.val] := (get_b3 (2 * n)).pos ⟨n + x.val, n_add_n_2n x.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + u.val] := (get_b3 (2 * n)).pos ⟨n + u.val, n_add_n_2n u.prop⟩
  have : (get_b3 (2 * n)).v[x.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n x.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : (get_b3 (2 * n)).v[u.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n u.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  nlinarith


lemma v_plus_p_neq_e_plus_p {i1 i2 x y u : Fin n} {g : SimpleGraph (Fin n)}
  {mg} {hn} (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[i1] + mg.p[i2] ≠ map_edge mg.v mg.p x y + mg.p[u] := by
  intro h
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at h
  have : (get_b3 (2 * n)).v[i1.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n i1.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : (get_b3 (2 * n)).v[n + i2.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_add_n_2n i2.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  have : 0 ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := inst_zero_le_max hmg
  have : 0 < (get_b3 (2 * n)).v[y.val] := (get_b3 (2 * n)).pos ⟨y.val, n_2n y.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + x.val] := (get_b3 (2 * n)).pos ⟨n + x.val, n_add_n_2n x.prop⟩
  have : 0 < (get_b3 (2 * n)).v[n + u.val] := (get_b3 (2 * n)).pos ⟨n + u.val, n_add_n_2n u.prop⟩
  have : (get_b3 (2 * n)).v[x.val] ≤ Option.getD (get_b3 (2 * n)).v.toList.maximum 0 := by
    have := inst_max hmg (n_2n x.prop)
    simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
      Finset.union_insert, Finset.union_singleton] at this
    exact this
  nlinarith

lemma A_intersect_B_eq_emptyset {n} {mg} {hn : n > 0} {g : SimpleGraph <| Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) : mg.inst.A ∩ mg.inst.B = ∅ := by
  ext e
  simp only [hmg, map_graph_to_translocation_pr_aux, edge_vals,
    map_edge, Fin.getElem_fin, Vector.get_ofFn, Vector.getElem_ofFn, Finset.union_insert,
    Finset.union_singleton, Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset,
    Vector.mem_toList_iff, Vector.mem_ofFn, Finset.mem_insert, Finset.mem_singleton, true_or,
    not_true_eq_false, and_false, not_false_eq_true, Finset.insert_inter_of_notMem,
    add_right_inj, or_true, Finset.mem_inter, Finset.mem_biUnion, SimpleGraph.mem_edgeFinset,
    not_or, Finset.notMem_empty, iff_false, not_and, Decidable.not_not, forall_exists_index,
    and_imp]
  intro edg hedg hel hi hel2
  by_contra
  cases hi with
  | inl hi =>
    obtain ⟨i, hi⟩ := hi
    have := exists_pair edg
    obtain ⟨x, y, hxy⟩ := this
    have hxyl := hxy.left
    subst hxyl
    simp only [Sym2.lift_mk, Finset.mem_insert, Finset.mem_singleton] at hel
    cases hel with
    | inl hel =>
      rw [←hi] at hel
      have := @v_neq_e _ _ _ i _ x y hmg
      simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
      contradiction
    | inr hel =>
      rw [←hi] at hel
      have := @v_neq_e _ _ _ i _ y x hmg
      simp [hmg, map_graph_to_translocation_pr_aux, map_edge] at this
      contradiction
  | inr hi =>
    obtain ⟨i, hi⟩ := hi
    have := exists_pair edg
    obtain ⟨x, y, hxy⟩ := this
    have hxyl := hxy.left
    subst hxyl
    simp only [Sym2.lift_mk, Finset.mem_insert, Finset.mem_singleton] at hel
    cases hel with
    | inl hel =>
      rw [←hi] at hel
      have := @p_neq_e _ _ _ i _ x y hmg
      simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at this
      have eq := this hel
      rw [SimpleGraph.mem_edgeSet] at hedg
      exact g.ne_of_adj hedg eq
    | inr hel =>
      rw [←hi] at hel
      have := @p_neq_e _ _ _ i _ y x hmg
      simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
        Finset.union_insert, Finset.union_singleton, map_edge, Vector.get_ofFn] at this
      have eq := this hel
      rw [SimpleGraph.mem_edgeSet] at hedg
      exact g.ne_of_adj (Iff.mp (g.adj_comm x y) hedg) eq


theorem v_nmem_p {g} {mg} {hn} {u : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.v[u] ∉ mg.p.toList.toFinset := by
  intro h
  simp only [hmg, map_graph_to_translocation_pr_aux, edge_vals, map_edge, Fin.getElem_fin,
    Vector.get_ofFn, Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
    List.mem_toFinset, Vector.mem_toList_iff, Vector.mem_ofFn] at h
  obtain ⟨i, h⟩ := h
  have := v_neq_p hmg (i := u) (j := i)
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, ne_eq] at this
  have := Ne.symm this
  contradiction

theorem p_nmem_v {g} {mg} {hn} {u : Fin n}
  (hmg : mg = map_graph_to_translocation_pr_aux g hn) :
  mg.p[u] ∉ mg.v.toList.toFinset := by
  intro h
  simp only [hmg, map_graph_to_translocation_pr_aux, edge_vals, map_edge, Fin.getElem_fin,
    Vector.get_ofFn, Vector.getElem_ofFn, Finset.union_insert, Finset.union_singleton,
    List.mem_toFinset, Vector.mem_toList_iff, Vector.mem_ofFn] at h
  obtain ⟨i, h⟩ := h
  have := v_neq_p hmg (i := i) (j := u)
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton, ne_eq] at this
  have := Ne.symm this
  contradiction
