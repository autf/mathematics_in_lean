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
  rw [le_abs]
  left
  apply le_refl

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [le_abs]
  right
  apply le_refl

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  · rw [neg_add]
    apply add_le_add <;> apply neg_abs_le
  · exact add_le_add (le_abs_self x) (le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rw [abs]
  constructor
  · intro h
    rcases max_choice y (-y) with pos | neg
    · left
      rw [pos] at h
      exact h
    · rw [neg] at h
      exact Or.inr h

  · rintro (lt | ltn)
    · exact lt_max_of_lt_left lt
    · exact lt_max_of_lt_right ltn

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  obtain ⟨xeq, _hx⟩ | ⟨xeq, _hx⟩ := abs_cases x
  <;> rw [xeq]
  <;> exact ⟨fun _ => ⟨by linarith, by linarith⟩, fun _ => by linarith⟩

  -- obtain ⟨xeq, hx⟩ | ⟨xeq, hx⟩ := abs_cases x
  -- · rw [xeq]
  --   constructor
  --   · intro h; exact ⟨by linarith, h⟩
  --   -- · exact fun ⟨_, lt⟩ ↦ lt
  --   · exact fun _ ↦ by linarith

  -- · rw [xeq]
  --   constructor
  --   · intros; exact ⟨by linarith, by linarith⟩
  --   · exact fun _ => by linarith

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
  obtain ⟨x, y, h | h⟩ := h <;> rw [h]
  · apply add_nonneg <;> apply pow_two_nonneg
  · apply add_nonneg
    apply add_nonneg <;> apply pow_two_nonneg
    linarith

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [pow_two] at h
  exact mul_self_eq_one_iff.mp h

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [pow_two, pow_two] at h
  exact mul_self_eq_mul_self_iff.mp h


section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [pow_two] at h
  exact mul_self_eq_one_iff.mp h

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [pow_two, pow_two] at h
  exact mul_self_eq_mul_self_iff.mp h

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
  · intro h
    by_cases h' : P
    exact Or.inr (h h' : Q)
    exact Or.inl (h' : ¬P)
  · rintro (np | q) h
    exact False.elim (np h)
    exact q
