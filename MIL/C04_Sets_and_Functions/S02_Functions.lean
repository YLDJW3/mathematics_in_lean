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
  · -- f '' s ⊆ v → s ⊆ f ⁻¹' v
    rintro h x xs
    simp; apply h
    simp; use x
  · --s ⊆ f ⁻¹' v → f '' s ⊆ v
    rintro h y hy
    rcases hy with ⟨ x, hx ⟩
    rw [← hx.right]
    apply h
    apply hx.left

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x hx
  simp at hx
  rcases hx with ⟨ x', ⟨ hx1, hx2 ⟩ ⟩
  apply h at hx2
  rw [← hx2]
  apply hx1

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x h
  simp at h
  rcases h with ⟨ x', ⟨ hx1, hx2 ⟩ ⟩
  rw [← hx2]
  apply hx1

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y hy
  simp
  rcases h y with ⟨ x, hx ⟩
  use x
  rw [hx]
  exact ⟨ hy, rfl ⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intros y hy
  rcases hy with ⟨ x, hx ⟩
  simp
  use x
  constructor
  · apply h; apply hx.left
  · apply hx.right

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x h1
  simp at h1; simp
  apply h; apply h1

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · --x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
    intro h1; simp at h1
    simp; apply h1
  · --x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
    intro h1; simp at h1
    simp; apply h1

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y h1
  simp at h1
  rcases h1 with ⟨ x, ⟨ xs, xt ⟩, hxy ⟩
  simp; constructor
  · use x
  · use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y h1
  simp at h1
  simp
  rcases h1 with ⟨ ⟨ x, xs, fxy ⟩, ⟨ x', xt', fxy' ⟩ ⟩
  rw [← fxy'] at fxy
  apply h at fxy
  use x
  constructor
  rw [← fxy] at xt'
  exact ⟨ xs, xt' ⟩
  rw [fxy]; apply fxy'

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intros y h1
  simp at h1; simp
  rcases h1 with ⟨ ⟨ x, xs, hxy ⟩, h2 ⟩
  use x
  constructor
  · --x ∈ s ∧ x ∉ t
    constructor
    exact xs
    by_contra h3
    apply h2 at h3
    contradiction
  · apply hxy

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intros y h1
  simp at *
  apply h1

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · --y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intros h
    simp at *
    rcases h with ⟨ ⟨ x, xs, hxy ⟩ , yv ⟩
    use x
    constructor
    rw [hxy]
    exact ⟨ xs, yv ⟩
    apply hxy
  · --y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intros h
    simp at *
    rcases h with ⟨ x, ⟨ xs, fxv ⟩, fxy ⟩
    constructor
    use x
    rw [fxy] at fxv; apply fxv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intros y h
  simp at *
  rcases h with ⟨ x, ⟨ xs, fxu ⟩ , fxy ⟩
  constructor
  use x
  rw [fxy] at fxu; apply fxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intros x h
  simp at *
  constructor
  use x; exact ⟨ h.left, rfl ⟩
  exact h.right

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intros x h
  simp at *
  rcases h with h | h
  · left; use x
  · right; apply h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · --y ∈ f '' ⋃ i, A i → y ∈ ⋃ i, f '' A i
    intro h1; simp at *
    rcases h1 with ⟨ x, ⟨ i, hxai ⟩, hxy ⟩
    use i; use x
  · --y ∈ ⋃ i, f '' A i → y ∈ f '' ⋃ i, A i
    intro h; simp at *
    rcases h with ⟨ i, x, hxai, hxy ⟩
    use x
    constructor
    use i
    apply hxy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intros y h
  simp at *
  rcases h with ⟨ x, hx, hxy ⟩
  intros i
  use x
  constructor
  apply hx
  apply hxy

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intros y h
  simp at *
  rcases h i with ⟨ x, hxai, hxy ⟩
  use x
  constructor
  · -- ∀ (i : I), x ∈ A i
    intros j
    rcases h j with ⟨ x', hxaj', hxy' ⟩
    rw [← hxy'] at hxy
    apply injf at hxy
    rw [hxy]; apply hxaj'
  · apply hxy


example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext y
  constructor
  · intro h; simp at *
    apply h
  · intro h; simp at *
    apply h

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext y
  constructor
  · intro h; simp at *
    apply h
  · intro h; simp at *
    apply h

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
  intros x hx y hy heq
  calc x
    _ = √x ^ 2 := by rw [sq_sqrt hx]
    _ = √y ^ 2 := by rw [heq]
    _ = y := by rw [sq_sqrt hy]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intros x hx y hy heq
  simp at heq
  calc x
    _ = √(x ^ 2) := by rw [sqrt_sq hx]
    _ = √(y ^ 2) := by rw [heq]
    _ = y := by rw [sqrt_sq hy]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · intro h
    simp at *
    rcases h with ⟨x, h1, h2⟩
    rw [← h2]
    apply sqrt_nonneg
  · intros h
    simp at *
    use y ^ 2
    constructor
    · apply pow_two_nonneg
    · rw [sqrt_sq h]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor <;> intro h <;> simp at *
  · rcases h with ⟨ y, hy ⟩
    rw [← hy]
    apply pow_two_nonneg
  · use √x
    rw [sq_sqrt h]
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
  · --Injective f → LeftInverse (inverse f) f
    intros h x
    have hx: ∃ x', f x' = f x := by use x
    rw [inverse, dif_pos hx]
    apply h
    apply Classical.choose_spec hx
  · --LeftInverse (inverse f) f → Injective f
    intros h x y heq
    have hx := by apply h x
    have hy := by apply h y
    rw [← hx, ← hy, heq]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · --Surjective f → RightInverse (inverse f) f
    intros h x
    have hx := by apply h x
    rw [inverse, dif_pos hx]
    apply Classical.choose_spec hx
  · --RightInverse (inverse f) f → Surjective f
    intros h x
    have hx := by apply h x
    use inverse f x

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
  have h₂ : j ∈ S := by
    apply h₁
  have h₃ : j ∉ S := by
    rw [← h]
    apply h₁
  contradiction
-- COMMENTS: TODO: improve this
end
