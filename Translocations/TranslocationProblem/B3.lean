import Mathlib

structure B3Vec (n : Nat) where
  v : Vector Int n
  isB3 {i₁ j₁ k₁ i₂ j₂ k₂ : Fin n} :
    i₁ ≤ j₁ → j₁ ≤ k₁ → i₂ ≤ j₂ → j₂ ≤ k₂ →
    v[i₁] + v[j₁] + v[k₁] = v[i₂] + v[j₂] + v[k₂] →
    (i₁ = i₂ ∧ j₁ = j₂ ∧ k₁ = k₂)
  pos : ∀ (i : Fin n), v[i] > 0

private theorem k_le_k
  {i₁ j₁ k₁ i₂ j₂ k₂ : Nat} :
    i₁ ≤ j₁ → j₁ ≤ k₁ → i₂ ≤ j₂ → j₂ ≤ k₂ →
  (4 : Int) ^ i₁ + 4 ^ j₁ + 4 ^ k₁ = 4 ^ i₂ + 4 ^ j₂ + 4 ^ k₂ →
  (k₁ ≥ k₂) := by
  intros h1ij h1jk h2ij h2jk
  have h1ik : i₁ ≤ k₁ := le_trans h1ij h1jk
  have h2il : i₂ ≤ k₂ := le_trans h2ij h2jk
  have h4gt1 : (1 : Int) ≤ 4 := by trivial
  intros h
  contrapose h
  rw [ge_iff_le, not_le] at h
  intros hx
  have hpik : (4 : Int) ^ i₁ ≤ 4 ^ k₁ := by
    exact pow_le_pow_right₀ h4gt1 h1ik
  have hpjk : (4 : Int)  ^ j₁ ≤ 4 ^ k₁ := by
    exact pow_le_pow_right₀ h4gt1 h1jk
  have h3x : (4 : Int) ^ i₁ + 4 ^ j₁ + 4 ^ k₁ ≤ 3 * (4 ^ k₁) := by omega
  have hv : (3 : Int) * 4 ^ k₁ < 4 ^ (k₂) := by
    cases hk₂ : k₂ with
    | zero =>
      simp only [pow_zero]
      rw [hk₂] at h
      contradiction
    | succ d =>
      rw [Int.pow_succ]
      have hx : k₁ ≤ d := by omega
      nth_rewrite 3 [(by omega : (4 : Int) = 3 + 1)]
      rw [Int.mul_add, Int.mul_one]
      have h__1: (3 : Int) * 4 ^ k₁ ≤ 4 ^ d * 3 := by
        rw [mul_comm]
        simp only [Nat.ofNat_pos, mul_le_mul_iff_left₀]
        exact pow_le_pow_right₀ h4gt1 hx
      have h__2 : (4 : Int) ^ d > 0 := by
        simp
      rw [gt_iff_lt, Int.lt_iff_add_one_le, zero_add] at h__2
      have := add_le_add h__1 h__2
      rw [Int.lt_iff_add_one_le]
      assumption
  have := add_le_add hpik hpjk
  have := Iff.mpr (add_le_add_iff_right (4 ^ k₁)) this
  nth_rewrite 2 3 4 [←Int.mul_one (4 ^ k₁)] at this
  rw [←Int.mul_add, ←Int.mul_add] at this
  simp only [Int.reduceAdd] at this
  rw [Int.mul_comm] at this
  have := Int.lt_of_le_of_lt this hv
  rw [hx] at this
  nth_rewrite 2 [←Int.zero_add (4 ^ k₂)] at this
  have := Iff.mp (add_lt_add_iff_right (4 ^ k₂)) this
  contradiction

def get_b3 (n : Nat) : B3Vec n := by
  use Vector.ofFn (fun i => 4 ^ i.val)
  · intros i₁ j₁ k₁ i₂ j₂ k₂
    intros h1ij h1jk h2ij h2jk
    have h1ik : i₁ ≤ k₁ := le_trans h1ij h1jk
    have h2il : i₂ ≤ k₂ := le_trans h2ij h2jk
    intros h
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at h
    have k₁_ge_k₂ : k₁.val ≥ k₂.val := by
      exact k_le_k h1ij h1jk h2ij h2jk h
    have k₂_ge_k₁ : k₂.val ≥ k₁.val := by
      exact k_le_k h2ij h2jk h1ij h1jk (Eq.symm h)
    have k₁_eq_k₂ : k₁.val = k₂.val := by
      exact Iff.mpr Nat.eq_iff_le_and_ge (And.intro (Iff.mp ge_iff_le k₂_ge_k₁)
        (Iff.mp ge_iff_le k₁_ge_k₂))
    rw [k₁_eq_k₂, add_right_cancel_iff] at h
    rw [←@add_left_cancel_iff _ _ _ (4 ^ 0), ←Int.add_assoc, ←Int.add_assoc] at h
    have j₁_ge_j₂ : j₁.val ≥ j₂.val := by
      exact k_le_k (Nat.zero_le i₁) h1ij (Nat.zero_le i₂) h2ij h
    have j₂_ge_j₁ : j₂.val ≥ j₁.val := by
      exact k_le_k (Nat.zero_le i₂) h2ij (Nat.zero_le i₁) h1ij (Eq.symm h)
    have j₁_eq_j₂ : j₁.val = j₂.val := by
      exact Iff.mpr Nat.eq_iff_le_and_ge (And.intro (Iff.mp ge_iff_le j₂_ge_j₁)
        (Iff.mp ge_iff_le j₁_ge_j₂))
    rw [j₁_eq_j₂, add_right_cancel_iff] at h
    rw [add_left_cancel_iff] at h
    have h1lt4 : 1 < 4 := by trivial
    have i₁_eq_i₂ : i₁.val = i₂.val := by
      exact Int.pow_right_injective (by omega) h
    apply And.intro
    · exact Fin.ext i₁_eq_i₂
    · apply And.intro
      · exact Fin.ext j₁_eq_j₂
      · exact Fin.ext k₁_eq_k₂
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, gt_iff_lt, Nat.ofNat_pos, pow_pos,
    implies_true]

lemma b2_of_b3 {i₁ j₁ i₂ j₂ : Fin n} (hn : n > 0) (b : B3Vec n)
  (h1ij : i₁.val ≤ j₁.val) (h2ij : i₂.val ≤ j₂.val) (h : b.v[i₁] + b.v[j₁] = b.v[i₂] + b.v[j₂]) :
  i₁ = i₂ ∧ j₁ = j₂ := by
  have h_zero_le_i₁ : 0 ≤ i₁.val := by simp only [zero_le]
  have h_zero_le_i₂ : 0 ≤ i₂.val := by simp only [zero_le]
  have h1 := congrArg (fun x => b.v[(⟨0, by omega⟩ : Fin n)] + x) h
  simp only [←Int.add_assoc] at h1
  obtain ⟨_, hl, hr⟩ := b.isB3 h_zero_le_i₁ h1ij h_zero_le_i₂ h2ij h1
  exact And.intro hl hr

lemma b2_of_b3_2 {i₁ j₁ i₂ j₂ : Fin n} (hn : n > 0) (b : B3Vec n)
  (h1ij : i₁.val ≤ j₁.val) (h2ij : i₂.val ≤ j₂.val) (h : b.v[i₁] + b.v[j₁] = b.v[i₂] + b.v[j₂]) :
  i₁ = i₂ ∧ j₁ = j₂ := by
  have h_zero_le_i₁ : 0 ≤ i₁.val := by simp only [zero_le]
  have h_zero_le_i₂ : 0 ≤ i₂.val := by simp only [zero_le]
  have h1 := congrArg (fun x => b.v[(⟨0, by omega⟩ : Fin n)] + x) h
  simp only [←Int.add_assoc] at h1
  obtain ⟨_, hl, hr⟩ := b.isB3 h_zero_le_i₁ h1ij h_zero_le_i₂ h2ij h1
  exact And.intro hl hr

lemma b1_of_b3 {i₁ i₂ : Fin n} (hn : n > 0) (b : B3Vec n) (h : b.v[i₁] = b.v[i₂]) : i₁ = i₂ := by
  have h_zero_zero : (⟨0, by omega⟩ : Fin n) ≤ (⟨0, by omega⟩ : Fin n)  := by trivial
  have h_zero_le_i₁ : 0 ≤ i₁.val := by simp only [zero_le]
  have h_zero_le_i₂ : 0 ≤ i₂.val := by simp only [zero_le]
  have h1 := congrArg (fun x => b.v[0] + b.v[0] + x) h
  simp only at h1
  obtain ⟨_, _, hr⟩ := b.isB3 h_zero_zero h_zero_le_i₁ h_zero_zero h_zero_le_i₂ h1
  exact hr

lemma b1_of_b3_2 {i₁ i₂ : Fin n} (hn : n > 0) (b : B3Vec n) (h : b.v[i₁.val] = b.v[i₂.val])
  : i₁ = i₂ := by
  have h_zero_zero : (⟨0, by omega⟩ : Fin n) ≤ (⟨0, by omega⟩ : Fin n)  := by trivial
  have h_zero_le_i₁ : 0 ≤ i₁.val := by simp only [zero_le]
  have h_zero_le_i₂ : 0 ≤ i₂.val := by simp only [zero_le]
  have h1 := congrArg (fun x => b.v[0] + b.v[0] + x) h
  simp only at h1
  obtain ⟨_, _, hr⟩ := b.isB3 h_zero_zero h_zero_le_i₁ h_zero_zero h_zero_le_i₂ h1
  exact hr

-- lemma b3_index {i₁ j₁ k₁ i₂ j₂ k₂ : Fin n} (b : B3Vec n) :
--   i₁.val ≤ j₁.val → j₁.val ≤ k₁.val → i₂.val ≤ j₂.val → j₂.val ≤ k₂.val →
--    b.v[i₁] + b.v[j₁] + b.v[k₁] = b.v[i₂] + b.v[j₂] + b.v[k₂] →
--     (i₁.val = i₂.val ∧ j₁.val = j₂.val ∧ k₁.val = k₂.val) := by
--   intro hij1 hjk1 hij2 hjk2 hsum
--   have i₁ ≤
--   have := b.isB3 (b)
