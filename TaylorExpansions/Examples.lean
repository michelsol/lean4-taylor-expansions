import TaylorExpansions.Basic

open Filter Topology Finset

open Real in
/-- Show that `(1 + x) ^ (1 / x) ⟶ e` as `x ⟶ 0` -/
example : Tendsto (λ x : ℝ ↦ (1 + x) ^ (1 / x)) (𝓝[≠] 0) (𝓝 (exp 1)) := by
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

-- (1 + x) ^ (1 / x) = exp ((1 / x) * log (1 + x)) = exp ((1 / x) * (x + o(x)))
-- = exp (1 + o(1)) = exp 1 * exp (o(1)) = exp 1 * (1 + o(1)) = exp 1 + o(1)

  have ⟨e1, he1, h1⟩ := taylor_rlog_one_add_littleO_order1
  have ⟨e2, he2, h2⟩ := taylor_rexp_littleO_order0
  replace h2 := he1.eventually h2
  -- You can start by filling use's with junk values, and work out the right expressions later
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
  -- So that you can focus on the calculations first and figure out which Taylor expansions are needed
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
