import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    · apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · apply le_trans
        apply inf_le_right
        apply inf_le_left
    · apply le_trans
      apply inf_le_right
      apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      · apply le_trans'
        apply le_sup_right
        apply le_sup_left
    · apply le_trans'
      apply le_sup_right
      apply le_sup_right
  · apply sup_le
    · apply le_trans'
      apply le_sup_left
      apply le_sup_left
    · apply sup_le
      · apply le_trans'
        apply le_sup_left
        apply le_sup_right
      · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm

  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left

  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    apply le_refl
    apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm

  · show x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    apply le_refl
    apply inf_le_left

  · show x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  -- rw [h (a ⊔ b), inf_comm (a ⊔ b), absorb1, inf_comm (a ⊔ b), h, ← sup_assoc, inf_comm c a, absorb2, inf_comm]
  apply Eq.symm
  calc
    (a ⊔ b) ⊓ (a ⊔ c) = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by apply h
    _ = a ⊓ (a ⊔ b) ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm]
    _ = a ⊔ (a ⊔ b) ⊓ c := by rw [absorb1]
    _ = a ⊔ c ⊓ (a ⊔ b) := by rw [inf_comm]
    _ = a ⊔ (c ⊓ a ⊔ c ⊓ b) := by rw [h]
    _ = a ⊔ c ⊓ a ⊔ c ⊓ b := by rw [sup_assoc]
    _ = a ⊔ a ⊓ c ⊔ c ⊓ b := by rw [inf_comm]
    _ = a ⊔ c ⊓ b := by rw [absorb2]
    _ = a ⊔ b ⊓ c := by rw [inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a ⊓ b), absorb2]
  rw [sup_comm (a ⊓ b), h, ← inf_assoc]
  rw [sup_comm c, absorb1]
  rw [sup_comm]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  -- apply sub_nonneg.mpr h
  calc
    0 = -a + a := by rw [neg_add_cancel]
    _ ≤ -a + b := by apply add_le_add_left h
    _ = b - a := by rw [neg_add_eq_sub]

example (h: 0 ≤ b - a) : a ≤ b := by
  -- apply le_of_sub_nonneg h
  calc
    a = a + 0 := by rw [add_zero]
    _ ≤ a + (b - a) := by apply add_le_add_left h
    _ = a + (b + -a) := by rw [sub_eq_add_neg]
    _ = a + (-a + b) := by rw [add_comm b]
    _ = a + -a + b := by rw [← add_assoc]
    _ = 0 + b := by rw [add_neg_cancel]
    _ = b := by rw [zero_add]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : 0 ≤ b - a := sub_nonneg_of_le h
  apply sub_nonneg.mp
  rw [← mul_sub_right_distrib]
  apply mul_nonneg this h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have := calc
    0 = dist x x := by rw [dist_self x]
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm y x]
    _ = dist x y * 2 := by ring
  have h2 : 0 < (2 : ℝ) := by norm_num
  apply (mul_nonneg_iff_of_pos_right h2).mp this

end
