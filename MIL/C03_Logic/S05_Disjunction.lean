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
  · rw [abs_of_neg h]
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
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · -- 0 ≤ x + y
    rw [abs_of_nonneg h]
    have hx := by apply le_abs_self x
    have hy := by apply le_abs_self y
    apply add_le_add hx hy
  · -- x + y < 0
    rw [abs_of_neg h]
    have hx := by apply neg_le_abs_self x
    have hy := by apply neg_le_abs_self y
    rw [neg_add]
    apply add_le_add hx hy

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · --x < |y| → x < y ∨ x < -y
    intros h1
    rcases le_or_gt 0 y with h | h
    · --nonneg
      rw [abs_of_nonneg h] at h1
      apply Or.inl h1
    · --neg
      rw [abs_of_neg h] at h1
      apply Or.inr h1
  · --x < y ∨ x < -y → x < |y|
    intros h1
    rcases h1 with h | h
    · -- x < y
      have h1 := by apply le_abs_self y
      apply lt_of_lt_of_le h h1
    · -- x < -y
      have h1 := by apply neg_le_abs_self y
      apply lt_of_lt_of_le h h1


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · --|x| < y → -y < x ∧ x < y
    rcases le_or_gt 0 x with h | h
    · --nonneg
      rw [abs_of_nonneg h]
      intros h1
      constructor
      repeat linarith
    · --neg
      rw [abs_of_neg h]
      intros h1
      constructor
      repeat linarith
  · ---y < x ∧ x < y → |x| < y
    intros h
    rcases le_or_gt 0 x with h1 | h1
    · --nonneg
      rw [abs_of_nonneg h1]
      apply h.right
    · --neg
      rw [abs_of_neg h1]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨ x, y, rfl | rfl ⟩ <;> have hx := pow_two_nonneg x <;> have hy := pow_two_nonneg y <;> linarith

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x + 1) * (x - 1) = 0 := by
    ring_nf; rw [h]; ring_nf
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h1 | h1
  · right; linarith
  · left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x + y) * (x - y) = 0 := by
    ring_nf; rw [h]; ring_nf
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h1 | h1
  · right; linarith
  · left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x + 1) * (x - 1) = 0 := by
    ring_nf; rw [h]; ring_nf
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h1 | h1
  · right
    calc x
      _ = x + 0 := by rw [add_zero]
      _ = x + (1 + -1) := by rw [add_neg_cancel]
      _ = x + 1 + -1 := by rw [← add_assoc]
      _ = 0 + -1 := by rw [h1]
      _ = -1 := by rw [zero_add]
  · left
    calc x
    _ = x - 1 + 1 := by rw [sub_add_cancel]
    _ = 0 + 1 := by rw[h1]
    _ = 1 := by rw[zero_add]


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x + y) * (x - y) = 0 := by
    ring_nf; rw [h]; ring_nf
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h1 | h1
  · right
    calc x
      _ = x + 0 := by rw [add_zero]
      _ = x + (y + -y) := by rw [add_neg_cancel]
      _ = x + y + -y := by rw [add_assoc]
      _ = 0 + -y := by rw [h1]
      _ = -y := by rw [zero_add]
  · left
    calc x
      _ = x - y + y := by rw [sub_add_cancel]
      _ = 0 + y := by rw [h1]
      _ = y := by rw [zero_add]
end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · --(P → Q) → ¬P ∨ Q
    intros h1
    by_cases h: P
    · right; apply h1; exact h
    · left; exact h
  · --¬P ∨ Q → P → Q
    intros h1 h2
    rcases h1 with h1 | h1
    · contradiction
    · exact h1
