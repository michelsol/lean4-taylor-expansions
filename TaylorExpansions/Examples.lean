import TaylorExpansions.Real

open Filter Topology Finset

/- Show that `(1 + x) ^ (1 / x) ⟶ e` as `x ⟶ 0` -/
open Real in
example : Tendsto (λ x : ℝ ↦ (1 + x) ^ (1 / x)) (𝓝[≠] 0) (𝓝 (exp 1)) := by

-- The math argument is :
-- (1 + x) ^ (1 / x) = exp ((1 / x) * log (1 + x)) = exp ((1 / x) * (x + o(x)))
-- = exp (1 + o(1)) = exp 1 * exp (o(1)) = exp 1 * (1 + o(1)) = exp 1 + o(1)

-- First reformulate the limit in little-o form with an explicit error term.
  suffices ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
      ∀ᶠ x in 𝓝[≠] 0, (1 + x) ^ (1 / x) = exp 1 + e x from by
    obtain ⟨e, he, h1⟩ := this
    convert_to Tendsto (λ x ↦ exp 1 + e x) (𝓝[≠] 0) (𝓝 (exp 1)) using 0
    . exact tendsto_congr' h1
    convert_to Tendsto (λ x ↦ exp 1 + e x) (𝓝[≠] 0) (𝓝 (exp 1 + 0)) using 2
    . simp
    apply Tendsto.add
    . exact tendsto_const_nhds
    . exact tendsto_nhdsWithin_of_tendsto_nhds he

  -- These expansions get added here later
  have ⟨e1, he1, h1⟩ := Real.taylor_log_one_add_littleO_order1
  have ⟨e2, he2, h2⟩ := Real.taylor_exp_littleO_order0
  replace h2 := he1.eventually h2
  -- You can start filling use tactics with sorries, and work out the right expressions later
  use λ x ↦ exp 1 * e2 (e1 x)
  use by
    convert_to Tendsto (λ x ↦ exp 1 * e2 (e1 x)) (𝓝 0) (𝓝 (exp 1 * 0)) using 2
    . ring
    apply Tendsto.const_mul
    apply he2.comp he1
  rw [Metric.eventually_nhds_iff] at h1 h2
  obtain ⟨ε1, hε1, h1⟩ := h1
  obtain ⟨ε2, hε2, h2⟩ := h2
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
  use ε1 ⊓ ε2 ⊓ 1, by simp [hε1, hε2]
  intro x ⟨hx1, hx2⟩
  simp only [Metric.mem_ball, lt_inf_iff] at hx1
  simp at hx2
  specialize h1 hx1.left.left
  specialize h2 hx1.left.right
  -- You can focus on the calculations first and figure out which Taylor expansions are needed
  calc
    (1 + x) ^ (1 / x) = exp (log (1 + x) * (1 / x)) := by
      refine rpow_def_of_pos ?_ (1 / x)
      replace hx1 := hx1.right
      simp [abs_lt] at hx1
      linarith
    _ = exp (1 / x * log (1 + x)) := by ring_nf
    _ = exp (1 / x * (x + e1 x * x)) := by simp [h1]
    _ = exp (1 + e1 x) := by
      congr 1
      field_simp
      ring
    _ = exp 1 * exp (e1 x) := by apply exp_add
    _ = exp 1 * (1 + e2 (e1 x)) := by rw [h2]
    _ = _ := by ring


/- Show that `ln(cos(x)) / x^2 ⟶ -1/2` as `x ⟶ 0` -/
open Real in
example : Tendsto (λ x : ℝ ↦ log (cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (-1 / 2)) := by
  suffices ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
      ∀ᶠ x in 𝓝[≠] 0, log (cos x) / x ^ 2 = -1 / 2 + e x from by
    obtain ⟨e, he, h1⟩ := this
    convert_to Tendsto (λ x ↦ -1 / 2 + e x) (𝓝[≠] 0) (𝓝 (-1 / 2)) using 0
    . exact tendsto_congr' h1
    convert_to Tendsto (λ x ↦ -1 / 2 + e x) (𝓝[≠] 0) (𝓝 (-1 / 2 + 0)) using 2
    . simp
    apply Tendsto.add
    . exact tendsto_const_nhds
    . exact tendsto_nhdsWithin_of_tendsto_nhds he

  have ⟨e1, he1, h1⟩ := taylor_cos_littleO 1
  let e2 x := -1 / 2 * x ^ 2 + e1 x * x ^ 3
  have he2 : Tendsto e2 (𝓝 0) (𝓝 0) := by
    convert_to Tendsto e2 (𝓝 0) (𝓝 (-1 / 2 * 0 ^ 2 + 0 * 0 ^ 3)) using 2
    . ring
    apply Tendsto.add
    . apply Tendsto.const_mul
      apply Tendsto.pow
      exact tendsto_id
    . apply Tendsto.mul
      . exact he1
      . apply Tendsto.pow
        exact tendsto_id
  have ⟨e3, he3, h3⟩ := taylor_log_one_add_littleO_order1
  replace h3 := he2.eventually h3
  use λ x ↦ e1 x * x + e3 (e2 x) * -1 / 2 + e3 (e2 x) * e1 x * x
  use by
    convert_to Tendsto (fun x => e1 x * x + e3 (e2 x) * (-1 / 2) + e3 (e2 x) * e1 x * x) (𝓝 0)
      (𝓝 (0 * 0 + 0 * (-1 / 2) + 0 * 0 * 0)) using 2
    . ring
    . ring
    iterate 2 apply Tendsto.add
    . apply Tendsto.mul
      . exact he1
      . exact tendsto_id
    . apply Tendsto.mul_const (-1 / 2)
      . exact he3.comp he2
    . iterate 2 apply Tendsto.mul
      . exact he3.comp he2
      . exact he1
      . exact tendsto_id
  rw [Metric.eventually_nhds_iff] at h1 h3
  obtain ⟨ε1, hε1, h1⟩ := h1
  obtain ⟨ε3, hε3, h3⟩ := h3
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
  use ε1 ⊓ ε3
  use by simp [hε1, hε3]
  intro x ⟨hx1, hx2⟩
  simp only [Metric.mem_ball, lt_inf_iff] at hx1
  simp at hx2
  specialize h1 (y := x) (by simpa using hx1.left)
  specialize h3 (y := x) (by simpa using hx1.right)
  convert_to cos x = 1 + e2 x using 1 at h1
  . have c1 : range 2 = {0, 1} := by ext k; simp; omega
    simp [e2, c1]
    ring
  calc
    log (cos x) / x ^ 2 = log (1 + e2 x) / x ^ 2 := by congr 2
    _ = (-1 / 2 + e1 x * x) * (1 + e3 (e2 x)) * (x ^ 2 / x ^ 2) := by
      rw [h3]
      ring
    _ = (-1 / 2 + e1 x * x) * (1 + e3 (e2 x)) * 1 := by congr 1; field_simp
    _ = _ := by ring
