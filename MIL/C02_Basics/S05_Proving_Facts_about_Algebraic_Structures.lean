import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
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
    . exact inf_le_right
    . exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . calc
      x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
      _ ≤ x := inf_le_left
    . apply le_inf
      . calc
        x ⊓ y ⊓ z ≤ x ⊓ y := inf_le_left
        _ ≤ y := inf_le_right
      . apply inf_le_right
  . apply le_inf
    . apply le_inf
      . apply inf_le_left
      . calc x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
        _ ≤ y := inf_le_left
    . calc x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
      _ ≤ z := inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    . exact le_sup_right
    . exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . apply sup_le
    . apply sup_le
      . apply le_sup_left
      . calc x ⊔ (y ⊔ z) ≥ y ⊔ z := le_sup_right
        _ ≥ y := le_sup_left
    . calc x ⊔ (y ⊔ z) ≥ y ⊔ z := le_sup_right
      _ ≥ z := le_sup_right
  . apply sup_le
    . calc x ⊔ y ⊔ z ≥ x ⊔ y := le_sup_left
      _ ≥ x := le_sup_left
    . apply sup_le
      . calc x ⊔ y ⊔ z ≥ x ⊔ y := le_sup_left
        _ ≥ y := le_sup_right
      . apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . apply inf_le_left
  apply le_inf
  . apply le_refl
  . exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . apply sup_le
    . apply le_refl
    . exact inf_le_left
  . exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply eq_comm.mp
  calc
    (a ⊔ b) ⊓ (a ⊔ c) = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by apply h
    _ = a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm, absorb1]
    _ = a ⊔ (a ⊓ c) ⊔ (c ⊓ b) := by rw [inf_comm, h, sup_assoc, inf_comm]
    _ = a ⊔ b ⊓ c := by rw [absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply eq_comm.mp
  calc
    a ⊓ b ⊔ a ⊓ c = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by apply h
    _ = a ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm, absorb2]
    _ = a ⊓ (c ⊔ a) ⊓ (c ⊔ b) := by rw [sup_comm, h, inf_assoc]
    _ = a ⊓ (c ⊔ b) := by rw [sup_comm, absorb1]
    _ = a ⊓ (b ⊔ c) := by rw [sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem t₁ (h : a ≤ b) : 0 ≤ b - a := by
  have h' : -a + a ≤ -a + b := by apply add_le_add_left h
  rw [← sub_eq_neg_add, ← sub_eq_neg_add, sub_self] at h'
  exact h'

theorem t₂ (h: 0 ≤ b - a) : a ≤ b := by
  have h' : a + 0 ≤ a + (b - a) := by apply add_le_add_left h
  rw [add_zero, ← add_comm_sub, sub_self, zero_add] at h'
  exact h'

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h'' : 0 ≤ (b - a) * c := mul_nonneg (t₁ _ _ h) h'
  rw [sub_mul] at h''
  exact t₂ _ _ h''

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 2 * dist x y ≥ 0 := calc
    2 * dist x y = dist x y + dist x y := two_mul _
    _ = dist x y + dist y x := by rw [dist_comm]
    _ ≥ dist x x := by apply dist_triangle
    _ = 0 := dist_self _
  apply nonneg_of_mul_nonneg_right h two_pos

end

