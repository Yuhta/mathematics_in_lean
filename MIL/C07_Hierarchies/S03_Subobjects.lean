import MIL.Common
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  inv_mem {s} : s ∈ carrier → s⁻¹ ∈ carrier

instance [Group G] : SetLike (Subgroup₁ G) G where
  coe s := s.toSubmonoid₁
  coe_injective' := Subgroup₁.ext

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem s := s.toSubmonoid₁.mul_mem
  one_mem s := s.toSubmonoid₁.one_mem

instance [Group G] (S : Subgroup₁ G) : Group S where
  inv s := ⟨s⁻¹, S.inv_mem s.property⟩
  mul_left_inv s := SetCoe.ext (mul_left_inv (s : G))

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] extends SubmonoidClass₁ S G where
  inv_mem {s : S} {x} : x ∈ s → x⁻¹ ∈ s

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  inv_mem := by intro s x xs; exact Subgroup₁.inv_mem s xs


instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z
      intro ⟨w₁, w₁n, z₁, z₁n, xy⟩
      intro ⟨w₂, w₂n, z₂, z₂n, yz⟩
      use w₁ * w₂, N.mul_mem' w₁n w₂n
      use z₁ * z₂, N.mul_mem' z₁n z₂n
      rw [← mul_assoc, xy, mul_comm y, mul_assoc, yz, ← mul_comm, mul_assoc, mul_comm z₂]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      intro a b ⟨w₁, w₁n, z₁, z₁n, ab⟩
      intro c d ⟨w₂, w₂n, z₂, z₂n, cd⟩
      simp
      use w₁ * w₂, N.mul_mem' w₁n w₂n
      use z₁ * z₂, N.mul_mem' z₁n z₂n
      rw [← mul_assoc, mul_comm a, mul_assoc c, mul_comm c, mul_assoc]
      rw [ab, cd]
      rw [← mul_assoc, mul_assoc b, mul_comm z₁, ← mul_assoc, mul_assoc])
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound; simp
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound; simp
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound; simp
      apply @Setoid.refl M N.Setoid
