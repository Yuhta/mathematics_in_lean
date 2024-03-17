import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  apply hf.comp
  apply Continuous.add
  apply continuous_pow
  exact continuous_id

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (eventually_of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε εpos
  rcases hu ε εpos with ⟨N, hN⟩
  use u N, hs N
  rw [dist_comm]
  apply hN N
  trivial

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_forall_le hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_forall_ge hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

#check IsCompact.isClosed

example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε εpos
  let φ (p : X × X) := dist (f p.1) (f p.2)
  let K := { p : X × X | ε ≤ φ p }
  rcases K.eq_empty_or_nonempty with hK | hK
  . use 1, by norm_num
    intro a b _
    contrapose! hK
    suffices ⟨a, b⟩ ∈ K by exact Set.nonempty_of_mem this
    exact hK
  have hK' : IsCompact K := by
    apply IsCompact.of_isClosed_subset isCompact_univ
    apply isClosed_le continuous_const
    rwa [← continuous_iff_continuous_dist]
    exact subset_univ K
  rcases hK'.exists_isMinOn hK continuous_dist.continuousOn with ⟨x, xK, hx⟩
  use dist x.1 x.2
  constructor
  . apply dist_pos.mpr
    by_contra h
    have : φ x = 0 := by
      rw [dist_eq_zero]
      exact congrArg f h
    have : φ x ≠ 0 := by
      apply ne_of_gt
      exact lt_of_lt_of_le εpos xK
    contradiction
  intro a b h
  contrapose! h
  have h : ⟨a, b⟩ ∈ K := by exact h
  exact hx h

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    suffices Tendsto (fun N : ℕ ↦ (1 / 2 ^ N * 2 : ℝ)) atTop (𝓝 0) by
      rcases (atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, _, hN⟩
      use N
      have := hN N left_mem_Ici
      rw [Set.mem_Ioo] at this
      have := this.right
      rwa [zero_add] at this
    rw [← zero_mul (2 : ℝ)]
    simp_rw [← one_div_pow]
    apply Tendsto.mul_const 2
    apply tendsto_pow_atTop_nhds_0_of_lt_1
    repeat norm_num
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by
      rw [dist_comm, add_zero]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := by
      apply dist_le_range_sum_dist (fun i ↦ u (N + i))
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := by
      apply Finset.sum_le_sum
      intro i _
      exact hu (N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by
      simp_rw [pow_add, one_div_pow, Finset.mul_sum]
    _ ≤ 1 / 2 ^ N * 2 := by
      rw [mul_le_mul_left]
      . apply sum_geometric_two_le
      rw [one_div_pos]
      apply pow_pos
      norm_num
    _ < ε := hN


open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := by
    apply pow_pos
    norm_num
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by
    intro n x δ δpos
    have hd := hd n
    rw [Dense] at hd
    simp_rw [Metric.mem_closure_iff] at hd
    have ho := ho n
    rw [Metric.isOpen_iff] at ho
    have δ_half_pos := half_pos δpos
    rcases hd x (δ / 2) δ_half_pos with ⟨y, hy, hxy⟩
    rcases ho y hy with ⟨ε, εpos, hyε⟩
    let r := min (B (n + 1)) (min (ε / 2) (δ / 2))
    use y, r
    constructor
    . apply lt_min_iff.mpr
      use Bpos (n + 1)
      apply lt_min_iff.mpr
      use half_pos εpos, δ_half_pos
    constructor
    . apply min_le_left
    rw [Set.subset_def]
    intro a hayr
    apply Set.mem_inter
    . calc dist a x ≤ dist a y + dist y x := dist_triangle _ _ _
      _ ≤ δ / 2 + δ / 2 := by
        apply add_le_add
        . calc dist a y ≤ r := hayr
          _ ≤ min (ε / 2) (δ / 2) := min_le_right _ _
          _ ≤ δ / 2 := min_le_right _ _
        rw [dist_comm]
        exact le_of_lt hxy
      _ = δ := add_halves _
    apply hyε
    calc dist a y ≤ r := hayr
    _ ≤ min (ε / 2) (δ / 2) := min_le_right _ _
    _ ≤ ε / 2 := min_le_left _ _
    _ < ε := half_lt_self εpos
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n ih
    . simp
      exact εpos
    apply Hpos
    exact ih
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n _
    . norm_num
    apply HB
    exact rpos n
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    intro n
    apply Hball
    exact rpos n
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    suffices dist (c n) (c (n + 1)) ≤ r n by
      exact le_trans this (rB n)
    rw [dist_comm, ← mem_closedBall]
    suffices c (n + 1) ∈ closedBall (c n) (r n) ∩ f n by
      exact mem_of_mem_inter_left this
    apply incl
    apply mem_closedBall_self
    apply le_of_lt
    exact rpos (n + 1)
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n m hmn
    induction' m, hmn using Nat.le_induction with m _ ih
    . exact subset_rfl
    apply subset_trans _ ih
    intro _ h
    exact mem_of_mem_inter_left (incl m h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    by_contra! h
    rcases h with ⟨n, hy⟩
    have hy : dist y (c n) > r n := not_le.mp hy
    let δ := dist y (c n) - r n
    have δpos : δ > 0 := sub_pos.mpr hy
    rw [Metric.tendsto_atTop] at ylim
    rcases ylim δ δpos with ⟨N, h⟩
    contrapose! h
    use max n N, le_max_right n N
    suffices dist y (c n) - dist (c (max n N)) y ≤ r n by
      exact sub_le_comm.mpr this
    calc dist y (c n) - dist (c (max n N)) y = dist (c n) y - dist (c (max n N)) y := by rw [dist_comm]
    _ ≤ |dist (c n) y - dist (c (max n N)) y| := le_abs_self _
    _ ≤ dist (c n) (c (max n N)) := abs_dist_sub_le _ _ _
    _ = dist (c (max n N)) (c n) := by rw [dist_comm]
    _ ≤ r n := by
      rw [← mem_closedBall]
      apply I n (max n N) (le_max_left n N)
      apply mem_closedBall_self
      apply le_of_lt
      exact rpos (max n N)
  constructor
  . rintro _ ⟨n, rfl⟩
    suffices y ∈ closedBall (c n) (r n) ∩ f n by
      exact mem_of_mem_inter_right this
    apply incl n
    exact yball (n + 1)
  have : ε ≥ min ε (B 0) := min_le_left _ _
  exact closedBall_subset_closedBall this (yball 0)
