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

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
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
  intros n hn
  have hns : n ≥ Ns := by apply le_trans (le_max_left Ns Nt) hn
  have hnt : n ≥ Nt := by apply le_trans (le_max_right Ns Nt) hn
  apply hs at hns
  apply ht at hnt
  have h1 := by apply add_lt_add hns hnt
  ring_nf at h1
  apply lt_of_le_of_lt _ h1
  have h2 : s n + t n - (a + b) = (s n - a) + (t n - b) := by ring_nf
  rw [h2]
  apply abs_add

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · -- c = 0
    convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  · -- c ≠ 0
    have acpos : 0 < |c| := abs_pos.mpr h
    intros ε εpos
    have εcpos : ε / |c| > 0 := by
      apply div_pos
      apply εpos
      apply acpos
    rcases cs (ε/|c|) εcpos with ⟨N, hN⟩
    use N
    dsimp
    intros n hn
    apply hN at hn
    rw [← mul_sub, abs_mul]
    have hc: |c| ≠ 0 := by linarith
    have heq: ε = ε / |c| * |c| := by rw [div_mul_cancel₀ _ hc]
    rw [heq, mul_comm]
    apply mul_lt_mul
    apply hn; linarith; assumption; apply le_of_lt εcpos


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intros n hn
  apply h at hn
  have h1 := by apply abs_add (s n - a) a
  ring_nf at h1
  apply lt_of_le_of_lt h1
  nth_rw 2 [add_comm]
  linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intros n hn
  have hn1 : n ≥ N₁ := by
    apply le_trans (le_max_right N₀ N₁) hn
  have hn0 : n ≥ N₀ := by
    apply le_trans (le_max_left N₀ N₁) hn
  apply h₁ at hn1; rw [sub_zero] at hn1
  rw [sub_zero, abs_mul]
  have h2: B * (ε / B) = ε := by
    rw [← mul_div_assoc, mul_comm, mul_div_cancel_right₀]
    symm
    apply ne_of_lt Bpos
  rw [← h2]
  apply mul_lt_mul_of_nonneg
  · -- |s n| < B
    apply h₀
    apply hn0
  · -- |t n| < ε / B
    apply hn1
  · -- 0 ≤ |s n|
    apply abs_nonneg
  · -- 0 ≤ |t n|
    apply abs_nonneg

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
  have : |a - b| > 0 := by
    have : a - b ≠ 0 := by
      rw [sub_ne_zero]
      apply abne
    rw [← abs_pos] at this
    apply this
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    change max Na Nb ≥ Na
    apply le_max_left Na Nb
  have absb : |s N - b| < ε := by
    apply hNb
    change max Na Nb ≥ Nb
    apply le_max_right Na Nb
  have : |a - b| < |a - b| := by
    have h1 := by apply abs_sub (s N - b) (s N - a)
    ring_nf at h1
    rw [add_comm, ← sub_eq_add_neg, add_comm] at h1
    apply lt_of_le_of_lt h1
    have h2: |a - b| = ε + ε := by
      change |a - b| = |a - b| / 2 + |a - b| / 2
      ring_nf
    rw [h2]
    apply add_lt_add
    apply absa
    apply absb
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
