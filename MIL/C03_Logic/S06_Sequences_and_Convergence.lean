import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  have ε2plus : ε / 2 + ε / 2 = ε := by norm_num
  intro n hn
  have hd : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
  rw [hd]

  have he: ε / 2 + ε / 2 > 0 := by exact add_pos ε2pos ε2pos

  have hf : |s n - a + (t n - b)| < |ε / 2 + ε / 2| := by
    apply lt_of_le_of_lt
    . apply abs_add
    . rw [abs_of_pos he]
      apply add_lt_add
      . apply hs
        . exact le_of_max_le_left hn
      . apply ht
        . exact le_of_max_le_right hn

  apply lt_of_lt_of_le
  . apply hf
  . rw [ε2plus]
    rw [abs_of_pos εpos]

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h

  intro ε εpos
  dsimp
  have cεpos : (1 / |c|) * ε > 0 := by 
    apply mul_pos_iff.mpr
    . left
      constructor
      . apply div_pos
        . norm_num
        . exact acpos
      . exact εpos

  have he : ((1 / |c|) * ε * |c| = ε) := by
    rw [mul_comm]
    rw [← mul_assoc]
    rw [mul_one_div]
    rw [div_self]
    . ring
    . exact abs_ne_zero.mpr h
    
    

  rcases cs ((1 / |c|) * ε) cεpos with ⟨Ns, hs⟩
  use Ns
  intro n hn
  rw [sub_eq_add_neg]
  rw [← mul_neg]
  rw [← mul_add]
  rw [← sub_eq_add_neg]
  rw [abs_mul]
  rw [mul_comm] at he
  rw [← he]
  apply mul_lt_mul'
  . exact le_refl |c|
  . apply hs
    . exact hn
  . exact abs_nonneg (s n - a)
  . exact acpos
    
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn

  have he: |s n| - |a| < 1 := by
    match le_or_gt 0 a with
    | Or.inl hd =>
      have hf: |s n| - |a| ≤ |s n - a| := by 
        match le_or_gt 0 (s n) with
        | Or.inl hg => 
          rw [abs_of_nonneg, abs_of_nonneg]
          . exact le_abs_self (s n - a)
          . exact hd
          . exact hg
        | Or.inr hg => 
          rw [abs_of_nonneg hd]
          rw [abs_of_neg hg]
          have hl : s n - a < 0 := by 
            match eq_or_lt_of_le hd with
            | Or.inl hh =>
              rw [← hh]
              rw [sub_zero]
              exact hg
            | Or.inr hh => linarith
          rw [abs_of_neg hl]
          rw [neg_sub]
          linarith
          
      apply lt_of_le_of_lt hf
      . apply h
        apply hn
      

    | Or.inr hd =>
      rw [abs_of_neg hd]
      rw [sub_neg_eq_add]
      match le_or_gt 0 (s n) with
      | Or.inl hg => 
        rw [abs_of_nonneg hg]
        have hh : s n - a > 0 := by linarith
        have hi : s n + a < s n - a := by linarith
        have hj : s n - a = |s n - a| := by exact (abs_of_pos hh).symm
        apply lt_of_lt_of_le
        . apply hi
        . rw [hj]
          apply le_of_lt
          apply h
          exact hn
        
      | Or.inr hg => 
        rw [abs_of_neg hg]
        match le_or_gt 0 (s n - a) with
        | Or.inl hh => 
          linarith
        | Or.inr hh => 
          rw [← neg_neg a]
          rw [← neg_add (s n) (-a)]
          rw [← sub_eq_add_neg (s n) (a)]
          rw [← abs_of_neg]
          . apply h
            . exact hn
          . exact hh

  linarith
  

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

