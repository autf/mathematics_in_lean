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

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
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
  intro n hn
  have hns : n ≥ Ns := ge_trans hn (by apply le_max_left : Ns ≤ max Ns Nt)
  have hnt : n ≥ Nt := ge_trans hn (by apply le_max_right)
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := add_lt_add (hs n hns) (ht n hnt)
    _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε hε
  dsimp
  have heps : 0 < ε / |c| := by apply div_pos hε acpos
  rcases cs (ε / |c|) heps with ⟨N, hN⟩
  use N
  intro n hn
  calc
    |c * s n - c * a| = |c * (s n - a)| := by rw [← mul_sub_left_distrib]
    _ = |c| * |s n - a| := by apply abs_mul
  have : ε = |c| * (ε / |c|)
  · calc
    ε = 1 * ε := by ring
    _ = |c| / |c| * ε := by rw [div_self (ne_of_gt acpos)]
    _ = |c| * (ε / |c|) := by ring
  rw [this]
  apply mul_lt_mul_of_pos_left (hN n hn) acpos

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  have := h n hn
  calc
    |s n| = |s n - a + a| := by norm_num
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < 1 + |a| := by linarith
    _ = |a| + 1 := by ring

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n h
  calc
    |s n * t n - 0| = |s n * (t n - 0)| := by norm_num
    _ = |s n| * |t n - 0| := abs_mul _ _
    _ < B * (ε / B) := by
      apply mul_lt_mul'
      · apply le_of_lt
        exact h₀ n (le_of_max_le_left h)
      · exact h₁ n (le_of_max_le_right h)
      · norm_num
      · exact Bpos
    _ = B / B * ε := by ring
    _ = 1 * ε := by rw [div_self (ne_of_gt Bpos)]
    _ = ε := by ring

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
  have : |a - b| > 0 := abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := hNb N (le_max_right _ _)
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(s N - b) - (s N - a)| := by ring_nf
      _ ≤ |s N - b| + |s N - a| := abs_sub _ _
      _ < ε + ε := by linarith
      -- _ = |a - b| / 2 + |a - b| / 2 := by dsimp [ε] -- optional
      _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
