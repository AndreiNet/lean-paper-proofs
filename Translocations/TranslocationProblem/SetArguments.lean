import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import TranslocationProblem.Translocations


theorem sdiff_comm [DecidableEq α] (A B D : Finset α) : (A \ B) \ D = (A \ D) \ B := by
  aesop

lemma finset_union_diff {α} [DecidableEq α] {A B C : Finset α} : (A ⊆ B ∪ C) ↔ (A \ B ⊆ C) := by
  grind only [= Finset.subset_iff, = Finset.mem_sdiff, = Finset.mem_union]

lemma length_dedup_eq_self {α} [DecidableEq α] {l : List α} :
  l.dedup.length = l.length → l.dedup = l := by
  intro h
  exact List.Sublist.eq_of_length l.dedup_sublist h

lemma length_dedup_nodup {α} [DecidableEq α] {l : List α} :
  l.dedup.length = l.length → l.Nodup := by
  intro h
  have := length_dedup_eq_self h
  exact Iff.mp List.dedup_eq_self this

lemma mem_superset {α} [DecidableEq α] {A B : Finset α} {x : α} (h : x ∈ A \ B) : x ∈ A := by
  rw [Finset.mem_sdiff] at h
  exact h.left

theorem u_v_in_B_2 {inst : TranslocationProblemInstance (γ₁ := Finset Int)}
  (sol : (Solution inst S)) : (inst.B \ inst.A).card = 2 * S.length →
  (∀s ∈ S, (s.u ∈ inst.B \ inst.A ∧ s.v ∈ inst.B \ inst.A) ∧ s.u ≠ s.v)
  ∧ S.Pairwise (fun s1 s2 => s1.u ≠ s2.u ∧ s1.v ≠ s2.v
    ∧ s1.u ≠ s2.v ∧ s1.v ≠ s2.u) := by
  obtain ⟨A, B⟩ := inst
  obtain ⟨hcovers, hIsValid⟩ := sol
  simp only at *
  set su := S.map (fun s => s.u) |> List.toFinset with hsu
  set sv := S.map (fun s => s.v) |> List.toFinset with hsv
  intro hAB
  have : B ⊆ A ∪ (su ∪ sv) := by
    apply Iff.mpr Finset.subset_iff
    intro x hx
    simp only [hsu, hsv, Finset.mem_union, List.mem_toFinset, List.mem_map]
    specialize hcovers hx
    cases hcovers with
    | inl hcovers => exact Or.inl hcovers
    | inr hcovers =>
      apply Or.inr
      obtain ⟨s, hS⟩ := hcovers
      cases hS.right with
      | inl hS1 =>
        apply Or.inl
        use s, hS.left
        exact Eq.symm hS1
      | inr hS2 =>
        apply Or.inr
        use s, hS.left
        exact Eq.symm hS2
  have hsubset := Iff.mp finset_union_diff this
  have := Finset.card_le_card hsubset
  rw [hAB] at this
  have h_su_card : su.card ≤ S.length := by
    rw [hsu]
    have := List.toFinset_card_le <| List.map (fun s ↦ s.u) S
    simp only [List.length_map] at this
    exact this
  have h_sv_card : sv.card ≤ S.length := by
    rw [hsv]
    have := List.toFinset_card_le <| List.map (fun s ↦ s.v) S
    simp only [List.length_map] at this
    exact this
  rw [Finset.card_union] at this
  have h_su_card_1 : su.card = S.length := by omega
  have h_sv_card_1 : sv.card = S.length := by omega
  rw [h_su_card_1, h_sv_card_1] at this
  simp +arith at this
  have h_suv_union_card : (su ∩ sv).card = 0 := by
    by_cases hsu_1 : su = ∅
    · rw [←Finset.card_empty, hsu_1]
      rw [Finset.empty_inter, Finset.card_empty]
    · have : S.length > 0 := by
        grind only [usr Finset.card_ne_zero_of_mem, ← Finset.notMem_empty, #ff30]
      omega
  have h_uv_card : (su ∪ sv).card ≤ (B \ A).card := by
    rw [Finset.card_union]
    omega
  have heq := Iff.mp (Finset.subset_iff_eq_of_card_le h_uv_card) hsubset
  apply And.intro
  · intro s hs
    have h_su_mem : s.u ∈ su := by simp only [hsu, List.mem_toFinset, List.mem_map] ; use s
    have h_sv_mem : s.v ∈ sv := by simp only [hsv, List.mem_toFinset, List.mem_map] ; use s
    apply And.intro
    · apply And.intro
      · grind only [= Finset.subset_iff, = Finset.mem_union, = Finset.mem_sdiff]
      · grind only [= Finset.subset_iff, = Finset.mem_union, = Finset.mem_sdiff]
    · by_contra h_uv_eq
      rw [h_uv_eq] at h_su_mem
      rw [Finset.card_eq_zero] at h_suv_union_card
      have : s.v ∈ su ∩ sv := by
        simp only [Finset.mem_inter]
        exact And.intro h_su_mem h_sv_mem
      have := Finset.ne_empty_of_mem this
      contradiction
  · apply Iff.mpr List.pairwise_iff_get
    intro i j hij
    simp only [List.get_eq_getElem, ne_eq]
    -- Prove for s.u
    rw [hsu, List.card_toFinset] at h_su_card_1
    nth_rewrite 2 [←List.length_map (fun s ↦ s.u)] at h_su_card_1
    have := length_dedup_nodup h_su_card_1
    rw [List.Nodup] at this
    apply Iff.mp List.pairwise_iff_get at this
    specialize this ⟨i, by rw [List.length_map] ; get_elem_tactic⟩
      ⟨j, by rw [List.length_map] ; get_elem_tactic⟩ hij
    simp only [List.get_eq_getElem, List.getElem_map, ne_eq] at this
    have h_uv_neq := this
    -- Prove for s.v
    rw [hsv, List.card_toFinset] at h_sv_card_1
    nth_rewrite 2 [←List.length_map (fun s ↦ s.v)] at h_sv_card_1
    have := length_dedup_nodup h_sv_card_1
    rw [List.Nodup] at this
    apply Iff.mp List.pairwise_iff_get at this
    specialize this ⟨i, by rw [List.length_map] ; get_elem_tactic⟩
      ⟨j, by rw [List.length_map] ; get_elem_tactic⟩ hij
    simp only [List.get_eq_getElem, List.getElem_map, ne_eq] at this
    apply And.intro h_uv_neq (And.intro this ?_)
    -- Prove u ≠ v
    have hsu_mem: ∀ i : Fin S.length, S[i].u ∈ su := by aesop
    have hsv_mem: ∀ i : Fin S.length, S[i].v ∈ sv := by aesop
    have hr1 : ¬S[↑i].u = S[↑j].v := by
      specialize hsu_mem i
      specialize hsv_mem j
      intro heq
      rw [heq] at hsu_mem
      have : S[j].v ∈ su ∩ sv := by
        simp only [Fin.getElem_fin, Finset.mem_inter]
        exact And.intro (by assumption) (by assumption)
      have := Finset.card_ne_zero_of_mem this
      contradiction
    have hr2 : ¬S[↑i].v = S[↑j].u := by
      specialize hsu_mem j
      specialize hsv_mem i
      intro heq
      rw [heq] at hsv_mem
      have : S[j].u ∈ su ∩ sv := by
        simp only [Fin.getElem_fin, Finset.mem_inter]
        exact And.intro (by assumption) (by assumption)
      have := Finset.card_ne_zero_of_mem this
      contradiction
    exact And.intro hr1 hr2

lemma translocation_comp {n : Nat} {S : List Translocation} {s : Translocation}
  {A : Finset Int} {B : Finset Int}
  (h : ∀ s' ∈ S, s'.u ∈ A ∪ B ∧ s'.v ∈ A ∪ B)
  (hd : ∀ s' ∈ S, s'.u ≠ s'.v)
  (hmem : s ∈ S)
  (hu : s.u ∈ A)
  (hv : s.v ∈ A)
  (hpw : S.Pairwise (fun s1 s2 => s1.u ≠ s2.u ∧ s1.v ≠ s2.v
    ∧ s1.u ≠ s2.v ∧ s1.v ≠ s2.u))
  (hcardA : A.card = n)
  (hlen : S.length = n)
  : ∃ s ∈ S, s.u ∈ B ∧ s.v ∈ B := by
  by_contra
  simp only [not_exists, not_and] at this
  set mapped := S.map (fun s => if s.u ∈ A then s.u else s.v) with hm
  have hsub : mapped.toFinset ⊆ A := by
    rw [hm]
    rw [Finset.subset_iff]
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨s1, hs1⟩ := hx
    specialize this s1 hs1.left
    specialize h s1 hs1.left
    by_cases hinA : s1.u ∈ A
    · simp [hinA] at hs1
      rw [hs1.right] at hinA
      exact hinA
    · simp [hinA] at hs1
      simp at h
      cases h.left with
      | inl => contradiction
      | inr humem =>
        specialize this humem
        cases h.right with
        | inr => contradiction
        | inl hvmem =>
          rw [hs1.right] at hvmem
          exact hvmem
  have hnodup : mapped.Nodup := by
    rw [List.pairwise_iff_getElem] at hpw
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [hm, List.length_map] at hi hj
    specialize hpw i j hi hj hij
    simp only [hm, List.getElem_map, ne_eq]
    grind only
  have h_u_or_v : s.u ∉ mapped.toFinset ∨ s.v ∉ mapped.toFinset := by
    by_contra
    simp only [hm, List.mem_toFinset, List.mem_map, not_exists, not_and, not_or, not_forall,
      Decidable.not_not] at this
    obtain ⟨a1, hh1, ha1⟩ := this.left
    obtain ⟨a2, hh2, ha2⟩ := this.right
    have heq1 : a1 = s := by
      have hi1 := List.getElem_of_mem hmem
      obtain ⟨i1, hi1, hs1⟩ := hi1
      have hi2 := List.getElem_of_mem hh1
      obtain ⟨i2, hi2, hs2⟩ := hi2
      rw [List.pairwise_iff_getElem] at hpw
      by_cases hh : a1.u ∈ A
      · simp only [hh, ↓reduceIte] at ha1
        by_cases idx1 : i1 < i2
        · specialize hpw i1 i2 hi1 hi2 idx1
          rw [hs1, hs2] at hpw
          have := hpw.left (Eq.symm ha1)
          contradiction
        · by_cases idx2 : i2 < i1
          · specialize hpw i2 i1 hi2 hi1 idx2
            rw [hs1, hs2] at hpw
            have := hpw.left ha1
            contradiction
          · have : i1 = i2 := by linarith only [idx1, idx2]
            simp only [this] at hs1
            rw [hs2] at hs1
            exact hs1
      · simp only [hh, ↓reduceIte] at ha1
        by_cases idx1 : i1 < i2
        · specialize hpw i1 i2 hi1 hi2 idx1
          rw [hs1, hs2] at hpw
          have := hpw.right.right.left (Eq.symm ha1)
          contradiction
        · by_cases idx2 : i2 < i1
          · specialize hpw i2 i1 hi2 hi1 idx2
            rw [hs1, hs2] at hpw
            have := hpw.right.right.right ha1
            contradiction
          · have : i1 = i2 := by linarith only [idx1, idx2]
            simp only [this] at hs1
            rw [hs2] at hs1
            exact hs1
    have heq2 : a2 = s := by
      have hi1 := List.getElem_of_mem hmem
      obtain ⟨i1, hi1, hs1⟩ := hi1
      have hi2 := List.getElem_of_mem hh2
      obtain ⟨i2, hi2, hs2⟩ := hi2
      rw [List.pairwise_iff_getElem] at hpw
      by_cases hh : a2.u ∈ A
      · simp only [hh, ↓reduceIte] at ha2
        by_cases idx1 : i1 < i2
        · specialize hpw i1 i2 hi1 hi2 idx1
          rw [hs1, hs2] at hpw
          have := hpw.right.right.right (Eq.symm ha2)
          contradiction
        · by_cases idx2 : i2 < i1
          · specialize hpw i2 i1 hi2 hi1 idx2
            rw [hs1, hs2] at hpw
            have := hpw.right.right.left ha2
            contradiction
          · have : i1 = i2 := by linarith only [idx1, idx2]
            simp only [this] at hs1
            rw [hs2] at hs1
            exact hs1
      · simp only [hh, ↓reduceIte] at ha2
        by_cases idx1 : i1 < i2
        · specialize hpw i1 i2 hi1 hi2 idx1
          rw [hs1, hs2] at hpw
          have := hpw.right.left (Eq.symm ha2)
          contradiction
        · by_cases idx2 : i2 < i1
          · specialize hpw i2 i1 hi2 hi1 idx2
            rw [hs1, hs2] at hpw
            have := hpw.right.left ha2
            contradiction
          · have : i1 = i2 := by linarith only [idx1, idx2]
            simp only [this] at hs1
            rw [hs2] at hs1
            exact hs1
    rw [heq1] at ha1
    rw [heq2] at ha2
    simp only [hu, ↓reduceIte] at ha2
    have := hd s hmem ha2
    contradiction
  rw [←List.dedup_eq_self] at hnodup
  have hcard1 := List.card_toFinset mapped
  rw [hnodup] at hcard1
  nth_rewrite 2 [hm] at hcard1
  rw [List.length_map, hlen] at hcard1
  cases h_u_or_v with
  | inl hnmem =>
    have hcard2 := Finset.card_insert_of_notMem hnmem
    rw [hcard1] at hcard2
    have : insert s.u mapped.toFinset ⊆ A := by
      rw [Finset.subset_iff]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      apply And.intro hu
      rw [Finset.subset_iff] at hsub
      intro a ha
      specialize hsub ha
      exact hsub
    have := Finset.card_le_card this
    rw [hcard2] at this
    linarith only [hcardA, this]
  | inr hnmem =>
    have hcard2 := Finset.card_insert_of_notMem hnmem
    rw [hcard1] at hcard2
    have : insert s.v mapped.toFinset ⊆ A := by
      rw [Finset.subset_iff]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      apply And.intro hv
      rw [Finset.subset_iff] at hsub
      intro a ha
      specialize hsub ha
      exact hsub
    have := Finset.card_le_card this
    rw [hcard2] at this
    linarith only [hcardA, this]

theorem x_y_in_A_union_B {inst : TranslocationProblemInstance (γ₁ := Finset Int)}
  (sol : (Solution inst S)) : (inst.B \ inst.A).card = 2 * S.length →
  (∀s ∈ S, s.x ∈ inst.A ∪ inst.B ∧ s.y ∈ inst.A ∪ inst.B) := by
  intro hlen
  have hB := (u_v_in_B_2 sol hlen).left
  obtain ⟨_, isValid⟩ := sol
  rename_i c
  clear c hlen
  induction S with
  | nil => simp only [List.not_mem_nil, Finset.mem_union, IsEmpty.forall_iff, implies_true]
  | cons x xs ih =>
    have hvalid_tail := valid_imp_tail_valid isValid
    rw [←List.forall_iff_forall_mem, List.forall_cons] at hB
    have h := hB.right
    rw [List.forall_iff_forall_mem] at h
    specialize ih h hvalid_tail
    intro s hs
    cases hs with
    | head =>
      cases isValid with
      | cons hv =>
        simp only [Finset.mem_union]
        rw [valid_translocation] at hv
        apply And.intro
        · cases hv.left with
          | inl hin_A => exact Or.inl hin_A
          | inr hc =>
            obtain ⟨s, hs⟩ := hc
            specialize h s hs.left
            cases hs.right with
            | inl h1 =>
              rw [←h1] at h
              exact Or.inr (mem_superset h.left.left)
            | inr h1 =>
              rw [←h1] at h
              exact Or.inr (mem_superset h.left.right)
        · cases hv.right with
          | inl hin_A => exact Or.inl hin_A
          | inr hc =>
            obtain ⟨s, hs⟩ := hc
            specialize h s hs.left
            cases hs.right with
            | inl h1 =>
              rw [←h1] at h
              exact Or.inr (mem_superset h.left.left)
            | inr h1 =>
              rw [←h1] at h
              exact Or.inr (mem_superset h.left.right)
    | tail _ hs =>
      exact ih s hs

lemma diff_output {inst : TranslocationProblemInstance (γ₁ := Finset Int)}
  (sol : (Solution inst S)) : (inst.B \ inst.A).card = 2 * S.length →
  (∀s ∈ S, ¬(s.x = s.u ∧ s.y = s.v) ∧ ¬(s.x = s.v ∧ s.y = s.u)) := by
  intro h s hs
  have hIsValid := sol.isValid
  have right_in_b := u_v_in_B_2 sol h |> And.left
  have pairwise_diff := u_v_in_B_2 sol h |> And.right
  clear sol h
  apply And.intro
  · intro heq
    induction hIsValid with
    | nil => simp only [List.not_mem_nil] at hs
    | @cons S' s' hx hxs ih =>
      simp only [List.mem_cons] at hs
      cases hs with
      | inl hss' =>
        rw [←hss', valid_translocation] at hx
        rw [heq.left, heq.right] at hx
        have hrb := right_in_b s
        rw [←hss'] at hrb
        specialize hrb (by aesop)
        simp only [Finset.mem_sdiff, ne_eq] at hrb
        have h_not_in_A := hrb.left.left.right
        cases hx.left with
        | inl hx => contradiction
        | inr hx1 =>
          cases pairwise_diff with
          | cons ha =>
            obtain ⟨ss, hss⟩ := hx1
            specialize ha ss hss.left
            rw [←hss'] at ha
            cases hss.right with
            | inl hc => exact ha.left hc
            | inr hc => exact ha.right.right.left hc
      | inr hss' =>
        specialize ih hss'
        rw [List.forall_mem_cons] at right_in_b
        cases pairwise_diff with
        | cons h hxs => exact ih right_in_b.right hxs
  · intro heq
    induction hIsValid with
    | nil => simp only [List.not_mem_nil] at hs
    | @cons S' s' hx hxs ih =>
      simp only [List.mem_cons] at hs
      cases hs with
      | inl hss' =>
        rw [←hss', valid_translocation] at hx
        rw [heq.left, heq.right] at hx
        have hrb := right_in_b s
        rw [←hss'] at hrb
        specialize hrb (by aesop)
        simp only [Finset.mem_sdiff, ne_eq] at hrb
        have h_not_in_A := hrb.left.right.right
        cases hx.left with
        | inl hx => contradiction
        | inr hx1 =>
          cases pairwise_diff with
          | cons ha =>
            obtain ⟨ss, hss⟩ := hx1
            specialize ha ss hss.left
            rw [←hss'] at ha
            cases hss.right with
            | inl hc => exact ha.right.right.right hc
            | inr hc => exact ha.right.left hc
      | inr hss' =>
        specialize ih hss'
        rw [List.forall_mem_cons] at right_in_b
        cases pairwise_diff with
        | cons h hxs => exact ih right_in_b.right hxs
