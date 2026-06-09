import TranslocationProblem.ProblemDevices
import TranslocationProblem.B3

def sink (h : n > 0) : Fin n := ⟨n - 1, by omega⟩

lemma n_2n (h : i < n) : i < 2 * n := by linarith only [h]
lemma n_add_n_2n (h : i < n) : n + i < 2 * n := by linarith only [h]
lemma n_le_2n : n ≤ 2 * n := by linarith only

theorem exists_pair (a : Sym2 V) : ∃ x y : V, a = s(x, y) ∧ a = s(y, x) := by
  refine Quot.inductionOn a ?_
  rintro ⟨x, y⟩
  use x, y
  exact And.intro rfl (by simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
    or_true])


lemma inst_max {g} {mg} {h : n > 0} (hmg : mg = map_graph_to_translocation_pr_aux g h)
  (hi : i < 2 * n) : mg.b.v[i] ≤ mg.m := by
  simp only [hmg, map_graph_to_translocation_pr_aux, Fin.getElem_fin, Vector.getElem_ofFn,
    Finset.union_insert, Finset.union_singleton]
  have hnl: (get_b3 (2 * n)).v.toList.length = 2 * n := Vector.length_toList
  have hilen := hi
  rw [←hnl] at hilen
  rw [←Vector.getElem_toList hilen]
  have hmem := List.getElem_mem hilen
  cases hm : (get_b3 (2 * n)).v.toList.maximum with
  | bot =>
    have := Iff.mp List.maximum_eq_bot hm
    simp [this, Option.getD]
    rw [this] at hnl
    simp only [List.length_nil, zero_eq_mul, OfNat.ofNat_ne_zero, false_or] at hnl
    rw [hnl] at hi
    simp +arith only [mul_zero, not_lt_zero] at hi
  | coe m =>
    have := List.le_maximum_of_mem hmem hm
    simp only [Option.getD, this]
