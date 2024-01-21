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

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
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
  intro n nge
  have : n ≥ Ns := le_of_max_le_left nge
  have h₁ : |s n - a| < ε / 2 := hs n this
  have : n ≥ Nt := le_of_max_le_right nge
  have h₂ : |t n - b| < ε / 2 := ht n this
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have : ε / |c| > 0 := div_pos εpos acpos
  rcases cs (ε / |c|) this with ⟨N, h⟩
  use N
  intro n nge
  have : |c| ≠ 0 := by linarith
  calc |c * s n - c * a| = |c * (s n - a)| := by ring_nf
    _ = |c| * |s n - a| := abs_mul _ _
    _ < |c| * (ε / |c|) := (mul_lt_mul_left acpos).mpr (h n nge)
    _ = ε := mul_div_cancel' _ this

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc |s n| = |s n - a + a| := by ring_nf
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < |a| + 1 := by linarith [h n nge]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  by_cases h : t n = 0
  . rw [h]; norm_num; exact εpos
  have tnpos : |t n| > 0 := by
    contrapose! h
    apply abs_eq_zero.mp
    exact le_antisymm h (abs_nonneg _)
  have tnub : |t n| < ε / B := by
    rw [← sub_zero (t n)]
    apply h₁ n
    exact le_of_max_le_right nge
  calc |s n * t n - 0| = |s n * t n| := by ring_nf
    _ = |s n| * |t n| := abs_mul _ _
    _ < B * |t n| := (mul_lt_mul_right tnpos).mpr (h₀ n (le_of_max_le_left nge))
    _ < B * (ε / B) := (mul_lt_mul_left Bpos).mpr tnub
    _ = ε := mul_div_cancel' _ (ne_of_gt Bpos)

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
    apply lt_iff_le_and_ne.mpr
    constructor
    . exact abs_nonneg _
    contrapose! abne
    rw [eq_comm] at abne
    have : a - b = 0 := abs_eq_zero.mp abne
    linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := hNb N (le_max_right _ _)
  have : |a - b| < |a - b| := calc
    |a - b| = |(s N - b) - (s N - a)| := by ring_nf
    _ ≤ |s N - b| + |s N - a| := abs_sub _ _
    _ < ε + ε := add_lt_add absb absa
    _ = 2 * ε := by ring
    _ = |a - b| := by dsimp; linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

