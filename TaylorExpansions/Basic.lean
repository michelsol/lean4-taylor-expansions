import Mathlib

open Filter Topology Finset

/-- A complex or real function which is the sum of a power series `∑ aₙ xⁿ` of non zero radius,
has a taylor expansion at any order with coefficients `aₙ`. -/
theorem taylor_bigO_of_series_at_zero
    {𝕜 : Type u} [RCLike 𝕜]
    (f : 𝕜 → 𝕜) (a : ℕ → 𝕜)
    (r : ℝ) (hr : r > 0)
    (hfa : ∀ x : 𝕜, ‖x‖ < r → HasSum (λ n ↦ a n * x ^ n) (f x))
    (n : ℕ) :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, f x = ∑ k ∈ range (n + 1), a k * x ^ k + E x * x ^ (n + 1) := by

  let p := FormalMultilinearSeries.ofScalars 𝕜 a

  have hpa (k : ℕ) : p.coeff k = a k := by
    simp [p, FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

  have hpr : p.radius ≥ ENNReal.ofReal r := by
    by_cases radius_top : p.radius = ⊤
    . simp [radius_top]
    suffices p.radius.toReal ≥ r from ENNReal.ofReal_le_of_le_toReal this
    suffices ∀ r' > 0, r' < r → p.radius.toReal ≥ r' by
      contrapose! this
      use (p.radius.toReal + r) / 2
      split_ands
      . positivity
      . linarith
      . linarith
    intro r' hr' hr'2
    suffices p.radius ≥ ENNReal.ofReal r' from (ENNReal.ofReal_le_iff_le_toReal radius_top).mp this
    apply FormalMultilinearSeries.le_radius_of_summable
    suffices Summable λ n ↦ ‖a n * r' ^ n‖ from by
      simp [hr', abs_of_pos] at this
      simpa [hpa, hr'.le] using this
    rw [summable_norm_iff]
    use f r'
    apply hfa
    simp [hr', abs_of_pos, hr'2]

  have h1 : HasFPowerSeriesWithinAt f p .univ 0 := by
    use ENNReal.ofReal r
    constructor
    . simp [hpr]
    . simp [hr]
    . intro x hx hx2
      suffices HasSum (fun n => a n * x ^ n) (f x) from by
        convert this using 1
        . ext n
          simp [hpa]
          ring
        . simp
      exact hfa x (by simpa using hx2)

  have h2 : (λ y ↦ f y - p.partialSum (n + 1) y) =O[𝓝 0] λ y ↦ ‖y‖ ^ (n + 1) := by
    simpa using h1.isBigO_sub_partialSum_pow (n + 1)
  rw [Asymptotics.isBigO_iff'] at h2
  obtain ⟨c, hc, h2⟩ := h2
  use λ x ↦ (f x - p.partialSum (n + 1) x) / x ^ (n + 1)
  use c
  use by
    rw [Metric.eventually_nhds_iff] at h2 ⊢
    obtain ⟨ε, hε, h2⟩ := h2
    use ε ⊓ 1, by simp [hε]
    intro x hx
    obtain ⟨hx1, hx2⟩ : ‖x‖ < ε ∧ ‖x‖ < 1 := by simpa using hx
    specialize h2 (by simpa using hx1)
    by_cases hx3 : x = 0
    . suffices c ≥ 0 from by simpa [hx3] using this
      exact hc.le
    . apply_fun (fun y ↦ y / ‖x‖ ^ (n + 1)) at h2
      swap
      . apply monotone_div_right_of_nonneg
        positivity
      replace h2 : ‖f x - p.partialSum (n + 1) x‖ / ‖x‖ ^ (n + 1)
        ≤ c * ‖x‖ ^ (n + 1) / ‖x‖ ^ (n + 1) := by simpa using h2
      suffices ‖f x - p.partialSum (n + 1) x‖ / ‖x‖ ^ (n + 1) ≤ c from by simpa using this
      calc
        _ ≤ _ := h2
        _ = c * (‖x‖ ^ (n + 1) / ‖x‖ ^ (n + 1)) := by ring
        _ ≤ c * 1 := by
          gcongr
          calc
            _ = (1 : ℝ) := by
              apply (div_eq_one_iff_eq ?_).mpr rfl
              apply pow_ne_zero (n + 1)
              exact norm_ne_zero_iff.mpr hx3
            _ ≤ _ := by norm_num
        _ = _ := by ring

  rw [Metric.eventually_nhds_iff]
  use 1, by norm_num
  intro x hx
  replace hx : ‖x‖ < 1 := by simpa using hx
  by_cases hx2 : x = 0
  . suffices f 0 = a 0 from by simpa [hx2, zero_pow_eq] using this
    specialize hfa 0 (by simpa using hr)
    convert hfa.tsum_eq.symm using 1
    calc
      a 0 = ∑ n ∈ {0}, if n = 0 then a 0 else 0 := by simp
      _ = ∑' n : ℕ, if n = 0 then a 0 else 0 := by
        rw [tsum_eq_sum]
        intro k hk
        simp at hk
        simp [hk]
      _ = _ := by
        apply tsum_congr
        intro k
        by_cases hk : k = 0 <;> simp [hk]
  . suffices p.partialSum (n + 1) x = ∑ k ∈ range (n + 1), a k * x ^ k from by field_simp [this]
    suffices ∑ k ∈ range (n + 1), x ^ k * a k = ∑ k ∈ range (n + 1), a k * x ^ k from by
      simpa [FormalMultilinearSeries.partialSum, hpa] using this
    congr 1
    ext k
    ring

open Nat in
/-- A complex function which is holomorphic on an open ball centered at 0, has a taylor expansion
at any order with coefficients `aₖ = f'ᵏ(0) / k!`-/
theorem taylor_bigO_of_series_at_zero_of_differentiableOn_ℂ
    (f : ℂ → ℂ)
    (r : ℝ) (hr : r > 0)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, f x = ∑ k ∈ range (n + 1),
      iteratedDeriv k f 0 / k ! * x ^ k + E x * x ^ (n + 1) := by
  apply taylor_bigO_of_series_at_zero f (λ k ↦ iteratedDeriv k f 0 / k !) r hr
  intro x hx
  convert Complex.hasSum_taylorSeries_on_ball hf (by simpa using hx) using 1
  ext k
  simp
  ring

/-- Derive the little O expansion of a Taylor series from the big O expansion using `O(xⁿ⁺¹) = o(xⁿ)`-/
theorem taylor_littleO_of_bigO_at_zero {𝕜 : Type u} [RCLike 𝕜] {f r : 𝕜 → 𝕜} {n : ℕ}
    (h1 : ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
      ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1)) :
    ∃ (o : 𝕜 → 𝕜) (_ : Tendsto o (𝓝 0) (𝓝 0)), ∀ᶠ x in 𝓝 0, f x = r x + o x * x ^ n := by
  have ⟨E, C, hE, h1⟩ := h1
  use λ x ↦ E x * x
  use by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : ∀ᶠ x in 𝓝 0, 0 ≤ ‖E x * x‖ := by
      rw [Metric.eventually_nhds_iff]
      use 1, by norm_num
      intro x hx
      apply norm_nonneg
    have h3 : ∀ᶠ x in 𝓝 0, ‖E x * x‖ ≤ C * ‖x‖ := by
      rw [Metric.eventually_nhds_iff] at hE ⊢
      obtain ⟨ε, hε, hE⟩ := hE
      use ε, hε
      intro x hx
      specialize hE hx
      calc
        _ = ‖E x‖ * ‖x‖ := by apply norm_mul
        _ ≤ C * ‖x‖ := by gcongr
    apply squeeze_zero' h2 h3
    suffices Tendsto (λ t : 𝕜 ↦ C * ‖t‖) (𝓝 0) (𝓝 (C * 0)) from by simpa using this
    apply Tendsto.const_mul
    exact tendsto_norm_zero
  convert h1 using 4 with x
  ring

/-- Derive a Taylor expansion on ℝ from a Taylor expansion on ℂ -/
theorem taylor_bigO_at_zero_ℝ_of_ℂ (f r : ℝ → ℝ) (n : ℕ)
    (h1 : ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
      ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1)) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C), ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1) := by
  obtain ⟨E, C, hE, h1⟩ := h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨ε1, hε1, h1⟩ := h1
  use λ x ↦ (f x - r x) / x ^ (n + 1)
  use C
  use by
    rw [Metric.eventually_nhds_iff] at hE ⊢
    obtain ⟨ε2, hε2, hE⟩ := hE
    use ε1 ⊓ ε2 ⊓ 1, by simp [hε1, hε2]
    intro x hx
    simp at hx
    specialize hE (y := x) (by simpa using hx.left.right)
    by_cases hx2 : x = 0
    . subst hx2
      suffices 0 ≤ C from by simpa using this
      calc
        _ ≤ _ := by simp
        _ ≤ _ := hE
    specialize h1 (y := x) (by simpa using hx.left.left)
    replace h1 : E x * x ^ (n + 1) = f x - r x := by
      linear_combination -h1
    replace h1 : E x = (f x - r x) / x ^ (n + 1) := by
      refine eq_div_of_mul_eq ?_ h1
      simp [hx2]
    rw [h1] at hE
    convert hE using 1
    norm_cast
  rw [Metric.eventually_nhds_iff]
  use ε1, hε1
  intro x hx
  specialize h1 (y := x) (by simpa using hx)
  replace h1 : E x * x ^ (n + 1) = f x - r x := by linear_combination -h1
  by_cases hx2 : x = 0
  . simp [hx2] at h1 ⊢
    norm_cast at h1
    linarith
  . field_simp
