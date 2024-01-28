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
  . intro h x xs
    rw [Set.subset_def] at h
    show f x ∈ v
    apply h (f x)
    use x, xs
  intro h y ⟨x, xs, fxy⟩
  rw [Set.subset_def] at h
  rw [← fxy]
  exact h x xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨y, ys, h'⟩
  have : y = x := h h'
  rw [← this]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y h
  rcases h with ⟨x, fxu, rfl⟩
  exact fxu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, rfl⟩
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yfs
  rcases yfs with ⟨x, xs, rfl⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x fxu
  exact h fxu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext y
  calc y ∈ f ⁻¹' (u ∪ v) ↔ f y ∈ u ∪ v := by rfl
    _ ↔ f y ∈ u ∨ f y ∈ v := by rfl
    _ ↔ y ∈ f ⁻¹' u ∨ y ∈ f ⁻¹' v := by rfl
    _ ↔ y ∈ f ⁻¹' u ∪ f ⁻¹' v := by rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y h
  rcases h with ⟨x, xst, rfl⟩
  constructor
  . use x, Set.mem_of_mem_inter_left xst
  . use x, Set.mem_of_mem_inter_right xst

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨⟨x₁, x₁s, h₁⟩, ⟨x₂, x₂t, h₂⟩⟩
  let h' := h₁
  rw [← h₂] at h'
  rw [← h h'] at x₂t
  use x₁, ⟨x₁s, x₂t⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨yfs, yft⟩
  rcases yfs with ⟨x, xs, rfl⟩
  have xt : x ∉ t := by
    contrapose! yft
    use x, yft
  use x, ⟨xs, xt⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨fxu, fxv⟩
  exact ⟨fxu, fxv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  . rintro ⟨⟨x, xs, rfl⟩, yv⟩
    use x, ⟨xs, yv⟩
  rintro ⟨x, ⟨xs, fxv⟩, rfl⟩
  exact ⟨⟨x, xs, by trivial⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, by trivial⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, by trivial⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  . left; use x, xs
  . right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  . intro ⟨x, ⟨i, xAi⟩, fxy⟩
    exact ⟨i, ⟨x, xAi, fxy⟩⟩
  intro ⟨i, ⟨x, xAi, fxy⟩⟩
  exact ⟨x, ⟨i, xAi⟩, fxy⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intro x xAi fxy i
  use x, xAi i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, _, fxy⟩
  use x
  constructor
  . intro i
    rcases h i with ⟨x', _, fx'y⟩
    rw [← fxy] at fx'y
    rw [← injf fx'y]
    assumption
  exact fxy

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
  intro x xnn y ynn fxfy
  calc x = (sqrt x) * (sqrt x) := by rw [mul_self_sqrt xnn]
    _ = (sqrt y) * (sqrt y) := by rw [fxfy]
    _ = y := by rw [mul_self_sqrt ynn]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnn y ynn fxfy
  simp at fxfy
  calc x = sqrt (x ^ 2) := by rw [sqrt_sq xnn]
    _ = sqrt (y ^ 2) := by rw [fxfy]
    _ = y := by rw [sqrt_sq ynn]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp
  constructor
  . rintro ⟨x, _, rfl⟩
    exact sqrt_nonneg _
  intro ynn
  use y * y
  exact ⟨mul_self_nonneg _, sqrt_mul_self ynn⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; simp
  constructor
  . rintro ⟨x, rfl⟩
    exact pow_two_nonneg _
  intro ynn
  use sqrt y
  exact sq_sqrt ynn

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

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf x
    let y := f x
    have h : ∃ x, f x = y := by use x
    rw [inverse, dif_pos h]
    have : f (choose h) = f x := choose_spec h
    exact injf this
  intro h x₁ x₂ feq
  calc x₁ = inverse f (f x₁) := by rw [h x₁]
    _ = inverse f (f x₂) := by rw [feq]
    _ = x₂ := by rw [h x₂]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro srjf y; exact inverse_spec y (srjf y)
  intro h y
  use inverse f y
  exact h y

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
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
