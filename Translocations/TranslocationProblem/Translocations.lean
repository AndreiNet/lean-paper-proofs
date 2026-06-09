import Mathlib.Data.Set.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finset.Basic

structure Translocation where
  x : Int
  y : Int
  u : Int
  v : Int
  h : x + y = u + v
  ge_zero : 0 < x ∧ 0 < y ∧ 0 < u ∧ 0 < v
  deriving DecidableEq

notation "(" x ", " y ")" "⊢" "(" u ", " v ")" "|" h "|" ge_zero =>
  Translocation.mk x y u v h ge_zero

#check ((4,4) ⊢ (3, 5) | by trivial | by trivial : Translocation)

def valid_translocation [Membership Int γ] (A : γ) (S : List Translocation) (s : Translocation)
  : Prop :=
  (s.x ∈ A ∨ ∃s' ∈ S, s.x = s'.u ∨ s.x = s'.v) ∧
  (s.y ∈ A ∨ ∃s' ∈ S, s.y = s'.u ∨ s.y = s'.v)

inductive ValidOn [Membership Int γ] (A : γ) : List Translocation → Prop where
  | nil : ValidOn A []
  | cons {s} : valid_translocation A S' s → ValidOn A S' → ValidOn A (s :: S')

structure TranslocationProblemInstance {γ₁ γ₂} [Membership Int γ₁] [Membership Int γ₂] where
  A : γ₁
  B : γ₂

structure Solution {γ₁ γ₂} [Membership Int γ₁] [Membership Int γ₂]
  (inst : TranslocationProblemInstance (γ₁ := γ₁) (γ₂ := γ₂))
  (S : List Translocation) where
  h : x ∈ inst.B → (x ∈ inst.A ∨ ∃s ∈ S, x = s.u ∨ x = s.v)
  isValid : ValidOn inst.A S

-- Helpers for Solution

lemma valid_imp_tail_valid [Membership Int γ] {A : γ} : ValidOn A (x :: S) → ValidOn A S := by
  intro hv
  cases hv with
  | cons _ validS =>
    exact validS

lemma solution_tail [Membership Int γ] {inst}
  : Solution (γ₁ := γ) (γ₂ := (Finset Int)) inst (s :: S) →
    Solution (γ₁ := γ) (γ₂ := (Finset Int)) { A := inst.A, B := inst.B \ {s.u, s.v}} S := by
  intro sol
  obtain ⟨h, isValid⟩ := sol
  apply Solution.mk
  · intro x hx
    specialize @h x
    have := Iff.mp Finset.mem_sdiff hx
    specialize h this.left
    cases h with
    | inl hxA => exact Or.inl hxA
    | inr hxS =>
      simp only [List.mem_cons, exists_eq_or_imp] at hxS
      have := this.right
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
      apply Iff.mpr not_or at this
      cases hxS with
      | inl => contradiction
      | inr =>
        apply Or.inr
        assumption
  · exact valid_imp_tail_valid isValid

-- Helpers for valid_translocation and symmetry

def valid_translocation_2 (A : Finset Int) (S : List Translocation) (s : Translocation) : Prop :=
  s.x ∈ A ∪ ((S.map (fun s => s.u)).toFinset ∪ (S.map (fun s => s.v)).toFinset) ∧
  s.y ∈ A ∪ ((S.map (fun s => s.u)).toFinset ∪ (S.map (fun s => s.v)).toFinset)

def translocation_symm_right (s : Translocation) : Translocation :=
  (s.x, s.y) ⊢ (s.v, s.u) | by
      have := s.h
      omega
    | (by
      obtain ⟨_, _, _, _⟩ := s.ge_zero
      apply And.intro (by assumption)
      apply And.intro (by assumption)
      apply And.intro (by assumption) (by assumption))

def translocation_symm_right_inv (h : s' = translocation_symm_right s)
  : s = translocation_symm_right s' := by aesop

def translocation_symm_left (s : Translocation) : Translocation :=
  (s.y, s.x) ⊢ (s.u, s.v) | by
      have := s.h
      omega
    | (by
      obtain ⟨_, _, _, _⟩ := s.ge_zero
      apply And.intro (by assumption)
      apply And.intro (by assumption)
      apply And.intro (by assumption) (by assumption))

def translocation_symm_left_inv (h : s' = translocation_symm_left s)
  : s = translocation_symm_left s' := by aesop

def translocation_symm_comm : translocation_symm_left (translocation_symm_right s) =
  translocation_symm_right (translocation_symm_left s) := by aesop

def translocation_symm_left_cancel : translocation_symm_left (translocation_symm_left s) = s := by
  aesop

lemma valid_translocation_iff (A : Finset Int) (S : List Translocation) (s : Translocation) :
  valid_translocation A S s ↔ valid_translocation_2 A S s := by
  simp only [valid_translocation, valid_translocation_2, Finset.mem_union, List.mem_toFinset,
    List.mem_map]
  apply Iff.intro <;> aesop

lemma valid_translocation_symm_right_head_iff (A : Finset Int) (S : List Translocation)
  (s : Translocation) : valid_translocation A (s :: S) s'
  ↔ valid_translocation A ((translocation_symm_right s) :: S) s' := by
  apply Iff.intro <;> simp only [valid_translocation, List.mem_cons, exists_eq_or_imp,
    translocation_symm_right, and_imp] <;> aesop

lemma valid_translocation_symm_left_head_iff (A : Finset Int) (S : List Translocation)
  (s : Translocation) : valid_translocation A (s :: S) s'
  ↔ valid_translocation A ((translocation_symm_left s) :: S) s' := by
  apply Iff.intro <;> simp only [valid_translocation, List.mem_cons, exists_eq_or_imp,
    translocation_symm_left, and_imp] <;> aesop

lemma valid_translocation_symm_left_iff (A : Finset Int) (S : List Translocation)
  (s : Translocation) : valid_translocation A S s
  ↔ valid_translocation A S (translocation_symm_left s) := by
  apply Iff.intro <;> simp only [valid_translocation, translocation_symm_left] <;> aesop

lemma list_mem_replace {α} [DecidableEq α] {l : List α} {s s' : α}
  (h : s ∈ l) : (s' ∈ l.replace s s') := by
  induction l with
  | nil =>
    simp only [List.not_mem_nil] at h
  | cons x xs ih =>
    by_cases heq : s = x
    · simp [heq]
    · unfold List.replace
      have : (s == x) = false := by aesop
      simp only [this, List.mem_cons]
      simp only [List.mem_cons, heq, false_or] at h
      specialize ih h
      exact Or.inr ih

lemma list_mem_replace_of_neq {α} [DecidableEq α] {l : List α} {s s' s1 : α}
  (h : s ≠ s1) (hmem : s1 ∈ l) : (s1 ∈ l.replace s s') := by
  induction l with
  | nil =>
    simp only [List.not_mem_nil] at hmem
  | cons x xs ih =>
    rw [List.mem_cons] at hmem
    cases hmem with
    | inl heq =>
      simp only [heq, ne_eq] at ⊢ h
      unfold List.replace
      have : (s == x) = false := by aesop
      simp [this]
    | inr hmem =>
      specialize ih hmem
      unfold List.replace
      by_cases heq : (s == x) = false
      all_goals
      simp only [heq, List.mem_cons]
      exact Or.inr (by assumption)

lemma solution_replace_symm_left {γ₁ γ₂} [Membership Int γ₁] [Membership Int γ₂]
  {inst : TranslocationProblemInstance (γ₁ := γ₁) (γ₂ := γ₂)}
  (sol : Solution inst S) (s : Translocation) :
  Solution inst (S.replace s (translocation_symm_left s)) := by
  obtain ⟨hcovers, hIsValid⟩ := sol
  apply Solution.mk
  · intro x hx
    specialize hcovers hx
    cases hcovers with
    | inl => exact Or.inl (by assumption)
    | inr h =>
      apply Or.inr
      obtain ⟨s1, hs1⟩ := h
      by_cases heq : s1 = s
      · rw [heq] at hs1
        have := list_mem_replace hs1.left (s' := translocation_symm_left s)
        use translocation_symm_left s
        apply And.intro this
        simp only [translocation_symm_left]
        exact hs1.right
      · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left (s' := translocation_symm_left s)
        use s1
        apply And.intro this
        exact hs1.right
  · clear hcovers
    induction hIsValid with
    | nil =>
      simp only [List.not_mem_nil, not_false_eq_true, List.replace_of_not_mem]
      exact .nil
    | @cons S' s' x xs ih =>
      by_cases heq : s = s'
      · simp only [heq, List.replace_cons_self]
        apply ValidOn.cons
        · simp only [valid_translocation, translocation_symm_left] at ⊢ x
          exact And.symm x
        · exact xs
      · unfold List.replace
        have : (s == s') = false := by aesop
        simp only [this]
        apply ValidOn.cons
        · simp only [valid_translocation] at ⊢ x
          apply And.intro
          · cases x.left with
            | inl hh => exact Or.inl hh
            | inr hh =>
              obtain ⟨s1, hs1⟩ := hh
              apply Or.inr
              by_cases heq : s1 = s
              · rw [heq] at hs1
                have := list_mem_replace hs1.left (s' := translocation_symm_left s)
                use translocation_symm_left s
                apply And.intro this
                simp only [translocation_symm_left]
                exact hs1.right
              · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left
                  (s' := translocation_symm_left s)
                use s1
                apply And.intro this
                exact hs1.right
          · cases x.right with
            | inl hh => exact Or.inl hh
            | inr hh =>
              obtain ⟨s1, hs1⟩ := hh
              apply Or.inr
              by_cases heq : s1 = s
              · rw [heq] at hs1
                have := list_mem_replace hs1.left (s' := translocation_symm_left s)
                use translocation_symm_left s
                apply And.intro this
                simp only [translocation_symm_left]
                exact hs1.right
              · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left
                  (s' := translocation_symm_left s)
                use s1
                apply And.intro this
                exact hs1.right
        · exact ih

lemma solution_replace_symm_right {γ₁ γ₂} [Membership Int γ₁] [Membership Int γ₂]
  {inst : TranslocationProblemInstance (γ₁ := γ₁) (γ₂ := γ₂)}
  (sol : Solution inst S) (s : Translocation) :
  Solution inst (S.replace s (translocation_symm_right s)) := by
  obtain ⟨hcovers, hIsValid⟩ := sol
  apply Solution.mk
  · intro x hx
    specialize hcovers hx
    cases hcovers with
    | inl => exact Or.inl (by assumption)
    | inr h =>
      apply Or.inr
      obtain ⟨s1, hs1⟩ := h
      by_cases heq : s1 = s
      · rw [heq] at hs1
        have := list_mem_replace hs1.left (s' := translocation_symm_right s)
        use translocation_symm_right s
        apply And.intro this
        simp only [translocation_symm_right]
        exact Or.symm hs1.right
      · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left (s' := translocation_symm_right s)
        use s1
        apply And.intro this
        exact hs1.right
  · clear hcovers
    induction hIsValid with
    | nil =>
      simp only [List.not_mem_nil, not_false_eq_true, List.replace_of_not_mem]
      exact .nil
    | @cons S' s' x xs ih =>
      by_cases heq : s = s'
      · simp only [heq, List.replace_cons_self]
        apply ValidOn.cons
        · simp only [valid_translocation, translocation_symm_right] at ⊢ x
          exact x
        · exact xs
      · unfold List.replace
        have : (s == s') = false := by aesop
        simp only [this]
        apply ValidOn.cons
        · simp only [valid_translocation] at ⊢ x
          apply And.intro
          · cases x.left with
            | inl hh => exact Or.inl hh
            | inr hh =>
              obtain ⟨s1, hs1⟩ := hh
              apply Or.inr
              by_cases heq : s1 = s
              · rw [heq] at hs1
                have := list_mem_replace hs1.left (s' := translocation_symm_right s)
                use translocation_symm_right s
                apply And.intro this
                simp only [translocation_symm_right]
                exact Or.symm hs1.right
              · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left
                  (s' := translocation_symm_right s)
                use s1
                apply And.intro this
                exact hs1.right
          · cases x.right with
            | inl hh => exact Or.inl hh
            | inr hh =>
              obtain ⟨s1, hs1⟩ := hh
              apply Or.inr
              by_cases heq : s1 = s
              · rw [heq] at hs1
                have := list_mem_replace hs1.left (s' := translocation_symm_right s)
                use translocation_symm_right s
                apply And.intro this
                simp only [translocation_symm_right]
                exact Or.symm hs1.right
              · have := list_mem_replace_of_neq (Ne.symm heq) hs1.left
                  (s' := translocation_symm_right s)
                use s1
                apply And.intro this
                exact hs1.right
        · exact ih
