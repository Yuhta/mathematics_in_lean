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
  cases le_or_gt 0 x
  next h => rw [abs_of_nonneg h]
  next h => linarith [abs_of_neg h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x
  next h => linarith [abs_of_nonneg h]
  next h => rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y)
  next h => linarith [abs_of_nonneg h, le_abs_self x, le_abs_self y]
  next h => linarith [abs_of_neg h, neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . cases le_or_gt 0 y
    next h =>
      rw [abs_of_nonneg h]
      intro h'
      left
      exact h'
    next h =>
      rw [abs_of_neg h]
      intro h'
      right
      exact h'
  . intro h
    cases h
    next h => linarith [le_abs_self y]
    next h => linarith [neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  cases le_or_gt 0 x
  next h =>
    rw [abs_of_nonneg h]
    constructor
    . intro h'
      have : -y < 0 := by linarith [lt_of_le_of_lt h h']
      exact ⟨lt_of_lt_of_le this h, h'⟩
    . rintro ⟨_, h'⟩
      exact h'
  next h =>
    rw [abs_of_neg h]
    constructor
    . intro h'
      exact ⟨by linarith, by linarith⟩
    . rintro ⟨h', _⟩
      linarith

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
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linarith
  have : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h' | h'
  . left; linarith
  . right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by linarith
  have : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h' | h'
  . left; linarith
  . right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := calc
    (x + 1) * (x - 1) = x ^ 2 - 1 ^ 2 := by rw [sq_sub_sq x 1]
    _ = 1 - 1 ^ 2 := by rw [h]
    _ = 0 := by ring
  have : x + 1 = 0 ∨ x - 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h' | h'
  . right; rw [eq_add_neg_of_add_eq h']; norm_num
  . left; rw [eq_add_of_sub_eq h']; norm_num

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by
    rw [← sq_sub_sq x y, h]; norm_num
  have : x + y = 0 ∨ x - y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h' | h'
  . right; rw [eq_add_neg_of_add_eq h']; norm_num
  . left; rw [eq_add_of_sub_eq h']; norm_num

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
  constructor
  . intro h
    by_cases h' : P
    . right; exact h h'
    . left; exact h'
  . intro h h'
    rcases h
    . contradiction
    . assumption

