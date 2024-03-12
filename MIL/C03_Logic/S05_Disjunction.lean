import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match le_or_gt 0 x with
  | Or.inl h => 
    rw [abs_of_nonneg h]
  | Or.inr h => 
    rw [abs_of_neg h]
    apply le_trans
    . apply le_of_lt
      . apply h
    . linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  match le_or_gt 0 x with
  | Or.inl h =>
    rw [abs_of_nonneg h]
    linarith
  | Or.inr h =>
    rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  match le_or_gt 0 x with
  | Or.inl h => 
    rw [abs_of_nonneg h]
    match le_or_gt 0 y with
    | Or.inl h' => 
      rw [abs_of_nonneg h']
      have h'': 0 ≤ x + y := by linarith
      rw [abs_of_nonneg h'']
      
    | Or.inr h' => 
      rw [abs_of_neg h']
      match le_or_gt 0 (x + y) with
      | Or.inl hd =>
        rw [abs_of_nonneg hd]
        linarith
      | Or.inr hd => 
        rw [abs_of_neg hd]
        linarith

  | Or.inr h => 
    rw [abs_of_neg h]

    have h': y ≤ |y| := by
      exact le_abs_self y

    match le_or_gt 0 (x + y) with
    | Or.inl hd => 
      rw [abs_of_nonneg hd]
      linarith
      
    | Or.inr hd => 
      rw [abs_of_neg hd]
      ring_nf
      match le_or_gt 0 y with
      | Or.inl hd' => linarith
      | Or.inr hd' => 
        rw [abs_of_neg hd']
        linarith


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    match le_or_gt 0 y with
    | Or.inl hd =>
      rw [abs_of_nonneg] at h
      left; exact h; exact hd
    | Or.inr hd =>
      rw [abs_of_neg] at h
      right; exact h; exact hd
  . intro h
    match h with
    | Or.inl h => 
      apply lt_of_lt_of_le
      exact h
      exact le_abs_self y
    | Or.inr h => 
      apply lt_of_lt_of_le
      exact h
      exact neg_le_abs_self y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . intro h
    constructor
    . match le_or_gt 0 x with
      | Or.inl hd => 
        rw [abs_of_nonneg] at h
        linarith
        exact hd
      | Or.inr hd => 
        rw [abs_of_neg] at h
        linarith
        exact hd

    . exact lt_of_le_of_lt (le_abs_self x) h

  . intro h
    match le_or_gt 0 x with
    | Or.inl hd => 
      rw [abs_of_nonneg]
      linarith; exact hd
    | Or.inr hd => 
      rw [abs_of_neg]
      linarith; exact hd

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h⟩
  match h with
  | Or.inl hd => 
    apply ge_trans
    . apply ge_of_eq hd
    . apply add_nonneg
      . exact sq_nonneg x
      . exact sq_nonneg y
  | Or.inr hd => 
    apply ge_trans
    . apply ge_of_eq hd
    . apply add_nonneg
      . apply add_nonneg
        . exact sq_nonneg x
        . exact sq_nonneg y
      . norm_num

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  norm_num
  norm_num at h
  exact h

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h₂ : (x + y) * (x - y) = 0 := by
    rw [← h₁]
    ring

  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with hd | hd
  . right
    exact add_eq_zero_iff_eq_neg.mp hd
  . left
    apply sub_eq_zero.mp hd

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h₂ : (x + 1) * (x - 1) = 0 := by
    rw [← h₁]
    ring
  
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with hd | hd
  . right
    exact add_eq_zero_iff_eq_neg.mp hd
  . left
    exact sub_eq_zero.mp hd

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h₂ : (x + y) * (x - y) = 0 := by
    rw [← h₁]
    ring

  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with hd | hd
  . right
    exact add_eq_zero_iff_eq_neg.mp hd
  . left
    apply sub_eq_zero.mp hd

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  by_cases h' : P
  . constructor
    . intro hd
      right
      exact hd h'
    . intro hd
      intro he
      match hd with
      | Or.inl hd' => contradiction
      | Or.inr hd' => exact hd'
  . constructor
    . intro _
      left; exact h'
    . intro hd
      intro he
      match hd with
      | Or.inl _ => contradiction
      | Or.inr hd' => exact hd'

