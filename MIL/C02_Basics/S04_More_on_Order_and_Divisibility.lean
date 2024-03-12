import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply ge_antisymm
  . show max b a ≤ max a b
    apply max_le
    · exact le_max_right a b
    exact le_max_left a b

  . show max a b ≤ max b a
    apply max_le
    . exact le_max_right b a
    exact le_max_left b a
  
example : min (min a b) c = min a (min b c) := by
  have h : ∀ x y z : ℝ, min x (min y z) ≤ x := by
    intro x y z
    apply min_le_left x (min y z)
  have h₁ : ∀ x y z : ℝ, min (min x y) z ≤ z := by
    intro x y z
    apply min_le_right (min x y) z

  have h₂ : ∀ x y z : ℝ, y ≤ z → min x y ≤ z := by
    intro x y z
    intro h
    apply le_trans
    . apply min_le_right
    . apply h

  have h₃ : ∀ x y z : ℝ, x ≤ z → min x y ≤ z := by
    intro x y z
    intro h
    apply le_trans
    . apply min_le_left
    . apply h

  have h₄ : ∀ x y z  : ℝ, min x (min y z) ≤ z := by
    intro x y z
    apply h₂
    apply min_le_right

  have h₅ : ∀ x y z  : ℝ, min x (min y z) ≤ y := by
    intro x y z
    apply h₂
    apply min_le_left

  have h₆ : ∀ x y z  : ℝ, min (min x y) z ≤ x := by
    intro x y z
    apply h₃ 
    apply min_le_left

  have h₇ : ∀ x y z  : ℝ, min (min x y) z ≤ y := by
    intro x y z
    apply h₃
    apply min_le_right

  apply ge_antisymm
  . apply le_min
    . apply le_min
      . apply h
      . exact h₅ a b c 
    . exact h₄ a b c 
  . apply le_min
    . exact h₆ a b c
    . exact le_min (h₇ a b c) (h₁ a b c)
  
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . apply add_le_add
    . apply min_le_left
    . apply le_refl
  . apply add_le_add
    . apply min_le_right
    . apply le_refl

example : min a b + c = min (a + c) (b + c) := by
  have h₀ : min (a + c) (b + c) + -c ≤ min (a + c + -c) (b + c + -c) → 
            min (a + c) (b + c) ≤ min a b + c := by
    intro h
    rw [add_neg_cancel_right] at h
    rw [add_neg_cancel_right] at h
    norm_num
    exact le_total a b
  
  have h : min (a + c) (b + c) ≤ min a b + c := by
    apply h₀ 
    apply aux (a + c) (b + c) (-c)
    
    
  have h₂ : min a b + c ≤ min (a + c) (b + c) := by
    apply aux
  linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check add_neg_cancel_right

example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    . apply dvd_mul_of_dvd_right
      . apply dvd_mul_right
    . apply dvd_mul_left
  . apply dvd_mul_of_dvd_right h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  . apply dvd_gcd
    . apply gcd_dvd_right
    . apply gcd_dvd_left
  . apply dvd_gcd
    . apply gcd_dvd_right
    . apply gcd_dvd_left
end


