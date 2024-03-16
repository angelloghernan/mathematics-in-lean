import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h x
    intro h'
    apply h
    apply Exists.intro x
    use h'
    
  . intro h x h'
    rcases h' with ⟨y, hb, hc⟩
    apply mem_of_eq_of_mem
    . exact hc.symm
    . exact h hb
      

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, hy⟩
  rw [Injective] at h
  apply mem_of_eq_of_mem
  . exact h hy.right.symm
  . exact hy.left

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨y, h, h'⟩
  rw [← h']
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x ha
  rcases h x with ⟨y, hy⟩
  use y
  constructor
  . simp
    rw [← hy] at ha
    exact ha
  . exact hy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x hx
  simp
  simp at hx
  rcases hx with ⟨y, hy⟩
  use y
  constructor
  . exact h hy.left
  . exact hy.right

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  simp at hx
  simp
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  . intro hx
    simp
    simp at hx
    assumption
  . intro hx
    simp at hx
    simp
    assumption

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x ⟨y, hy⟩
  simp at hy
  simp
  constructor
  . use y
    exact ⟨hy.left.left, hy.right⟩
  . use y
    exact ⟨hy.left.right, hy.right⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  simp
  have : y = z := by 
    apply h
    rw [hy.right, hz.right]
  use y
  constructor
  . nth_rewrite 2 [this]
    exact ⟨hy.left, hz.left⟩
  . exact hy.right

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x ⟨⟨y, hy⟩, ht⟩
  simp
  use y
  constructor
  . constructor
    . exact hy.left
    . intro hy2
      apply absurd ht
      simp
      use y
      exact ⟨hy2, hy.right⟩
  . exact hy.right

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨ha, hb⟩
  simp at ha
  simp at hb
  simp
  exact ⟨ha, hb⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  . rintro ⟨h, hx⟩
    simp at h
    simp
    rcases h with ⟨y, hy⟩
    use y
    constructor
    . rw [hy.right]
      exact ⟨hy.left, hx⟩
    . exact hy.right
  . rintro ⟨y, ⟨⟨ha, hb⟩, hc⟩⟩
    simp at hb
    simp
    constructor
    . use y
    . rw [hc] at hb
      assumption

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro x ⟨y, ⟨ha, hb⟩, hc⟩
  simp
  constructor
  . use y
  . simp at hb
    rw [hc] at hb
    assumption 

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨ha, hb⟩
  simp at hb
  simp
  constructor
  . use x
  . assumption

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  repeat rw [preimage]
  rw [image]
  rintro x ha
  rcases ha with h | h
  . simp
    left
    use x
  . simp
    simp at h
    right
    exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  . simp
    intro y i
    intro hy hfy
    use i
    use y
  . simp
    intro i y
    intro hy hfy
    use y
    constructor
    . use i
    . assumption

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rw [image]
  rintro x ⟨y, ⟨ha, hb⟩⟩
  simp at ha
  simp
  intro i
  use y
  constructor
  . exact ha i
  . exact hb

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x
  intro h
  simp at h
  simp
  rcases h i with ⟨y, ⟨_, hyb⟩⟩
  use y
  constructor
  . intro i₂
    rcases h i₂ with ⟨y₂, ⟨hya₂, hyb₂⟩⟩
    have : y = y₂ := by 
      rw [← hyb] at hyb₂
      use injf hyb₂.symm
    rw [this]
    assumption
  . assumption

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnneg y ynneg sqrteq
  simp at xnneg
  simp at ynneg
  rw [← sqrt_sq xnneg]
  rw [← sqrt_sq ynneg]
  repeat rw [pow_two]
  rw [sqrt_mul xnneg x]
  rw [sqrt_mul ynneg y]
  rw [sqrteq]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  rw [InjOn]
  intro x xnneg y ynneg sqeq
  repeat rw [pow_two] at sqeq
  have : sqrt (x * x) = sqrt (y * y) := by rw [sqeq]
  repeat rw [← pow_two] at this
  rw [sqrt_sq xnneg] at this
  rw [sqrt_sq ynneg] at this
  assumption

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . intro hx
    simp at hx
    simp
    rcases hx with ⟨y, hy⟩
    have : 0 ≤ sqrt y := by exact sqrt_nonneg y
    rw [hy.right] at this
    exact this

  . intro hx
    simp at hx
    simp
    use x ^ 2
    constructor
    . exact sq_nonneg x
    . exact sqrt_sq hx

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  rw [range]
  ext x
  constructor
  . simp
    intro y
    intro hy
    rw [← hy]
    exact sq_nonneg y
  . simp
    intro hx
    use sqrt x
    exact sq_sqrt hx

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

#print LeftInverse
#print RightInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro hi
    intro x
    apply hi
    apply inverse_spec
    use x
  . rw [LeftInverse]
    rw [Injective]
    intro h x y hxy
    rw [← h x]
    rw [← h y]
    rw [hxy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  rw [Surjective]
  rw [Function.RightInverse]
  constructor
  . intro h x
    apply inverse_spec
    exact h x
  . rw [LeftInverse]
    intro h x
    use (inverse f x)
    exact h x 


end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by exact h₁
    
  have h₃ : j ∉ S := by
    rw [h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
