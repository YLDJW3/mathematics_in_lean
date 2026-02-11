import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · -- n is Prime
    use n, np
  · -- n is not Prime
    induction' n using Nat.strong_induction_on with n ih
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np h with ⟨m, mltn, mdvdn, mne1⟩
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have mgt2 : 2 ≤ m := two_le this mne1
    by_cases mp : m.Prime
    · use m, mp
    · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
      use p, pp
      apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    have h := Nat.factorial_pos n
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial
    rw [Nat.prime_def] at pp
    linarith
    apply ple
  have : p ∣ 1 := by
    have h := Nat.dvd_sub pdvd this
    rw [add_comm, Nat.add_sub_cancel] at h
    exact h
  show False
  rw [Nat.dvd_one] at this
  rw [Nat.prime_def] at pp
  linarith
open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  apply Nat.Prime.eq_one_or_self_of_dvd prime_q at h
  rcases h with h1 | h2
  · rw [Nat.prime_def] at prime_p; linarith
  · exact h2

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · --empty
    simp at h₁
    linarith [prime_p.two_le]
  · --insert
    simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
    rw [mem_insert]
    rcases h₁ with h₁ | h₁
    · -- p | a
      rw [Nat.dvd_prime h₀.left] at h₁
      rcases h₁ with h₁ | h₁
      · rw [Nat.prime_def] at prime_p; linarith
      · apply Or.inl h₁
    · -- p | ∏ n ∈ s, n
      right; apply ih h₀.right h₁

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    have h1: 0 < ∏ i ∈ s', i := by
      apply Finset.prod_pos
      intros i hi
      rw [mem_s'] at hi
      rw [Nat.prime_def] at hi
      linarith
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply Finset.dvd_prod_of_mem
    rw [mem_s']
    apply pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  rw [Nat.dvd_one] at this
  rw [Nat.prime_def] at pp
  linarith

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · --n / m ∣ n
    apply Nat.div_dvd_of_dvd
    apply h₀
  · -- n / m < n
    apply Nat.div_lt_self
    repeat linarith

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · -- n is prime
    use n
  · --n is not prime
    induction' n using Nat.strong_induction_on with n ih
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
    have mge2 : 2 ≤ m := by
      apply two_le _ mne1
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
    have : m % 4 = 3 ∨ n / m % 4 = 3 := by
      apply mod_4_eq_3_or_mod_4_eq_3
      rw [neq, h]
    rcases this with h1 | h1
    . -- m % 4 = 3
      by_cases mp: m.Prime
      · --m is prime
        use m
      · --m is not prime
        have h2 := by apply ih m mltn h1 mp
        rcases h2 with ⟨ p, pp, pdvdm, hp ⟩
        use p
        refine ⟨ pp, ?_, hp ⟩
        apply dvd_trans pdvdm mdvdn
    . -- n / m % 4 = 3
      by_cases nmp: (n / m).Prime
      · -- n / m is prime
        use n / m
        refine ⟨ nmp, ?_, h1 ⟩
        nth_rw 2 [← neq]
        apply dvd_mul_left
      · -- n / m  is not prime
        have h2 : n / m < n := by
          apply Nat.div_lt_self
          repeat linarith
        have h3 := by apply ih (n / m) h2 h1 nmp
        rcases h3 with ⟨ p, pp, pdvdnm, hp ⟩
        use p
        refine ⟨ pp, ?_, hp ⟩
        apply dvd_trans pdvdnm
        nth_rw 2 [← neq]
        apply dvd_mul_left

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    simp
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    rw [← hs]
    exact ⟨ pp, p4eq ⟩
  have pne3 : p ≠ 3 := by
    intro peq3
    rw [peq3, ← Nat.dvd_add_iff_left] at pdvd
    have pdvd' : 3 ∣ 3 * ∏ i ∈ s.erase 3, i := by
      apply Nat.dvd_mul_right
    have pdvd'' := by apply Nat.dvd_sub pdvd pdvd'
    rw [← Nat.sub_mul] at pdvd''; ring_nf at pdvd''
    apply mem_of_dvd_prod_primes at pdvd''
    simp at pdvd''
    -- prime3
    decide
    -- ∀ n ∈ s.erase 3, Nat.Prime n
    intros x hx; simp at hx
    have hx1 := hx.right
    rw [← hs] at hx1
    apply hx1.left
    -- 3 dvd 3
    decide

  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
    rw [Nat.dvd_mul]
    use 1, p; simp
    apply Finset.dvd_prod_of_mem
    simp; exact ⟨pne3, ps⟩

  have : p ∣ 3 := by
    have h1 := by apply Nat.dvd_sub pdvd this
    ring_nf at h1
    rw [Nat.add_sub_cancel] at h1
    exact h1
  have : p = 3 := by
    rw [Nat.dvd_prime] at this
    rcases this with peq1 | peq3
    · rw [peq1] at p4eq; linarith
    · apply peq3
    decide
  contradiction
