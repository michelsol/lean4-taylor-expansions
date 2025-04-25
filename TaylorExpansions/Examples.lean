import TaylorExpansions.Basic

open Filter Topology Finset

open Real in
/-- (1 + 1/n)^n ⟶ e -/
example : Tendsto (λ n : ℕ ↦ (1 + (1 : ℝ) / n) ^ n) atTop (𝓝 (exp 1)) := by
  suffices ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
      ∀ᶠ x in 𝓝[≠] 0, (1 + x) ^ (1 / x) = exp 1 + e x by
    obtain ⟨e, he, h1⟩ := this
    let f (n : ℕ) := exp 1 + e (1 / n)
    have h2 : Tendsto f atTop (𝓝 (exp 1)) := by
      suffices Tendsto f atTop (𝓝 (exp 1 + 0)) from by convert this using 2; simp
      apply Tendsto.add
      . exact tendsto_const_nhds
      . show Tendsto (e ∘ λ n : ℕ ↦ 1 / n) atTop (𝓝 0)
        apply Tendsto.comp he
        exact tendsto_one_div_atTop_nhds_zero_nat
    convert h2 using 0
    apply Iff.symm (tendsto_congr' ?_)
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at h1
    obtain ⟨ε, hε, h1⟩ := h1
    rw [EventuallyEq, eventually_atTop]
    use Nat.ceil (1 / ε + 1)
    intro k hk
    replace hk : k ≥ 1 / ε + 1 := Nat.le_of_ceil_le hk
    have hε' : 1 / ε > 0 := by positivity
    have hk' : (k : ℝ) > 0 := by linarith
    replace hk : k > 1 / ε := by linarith
    replace hk : (1 : ℝ) / k < ε := by refine (one_div_lt hε hk').mp hk
    have h3 : (1 : ℝ) / k ∈ Metric.ball 0 ε ∩ {0}ᶜ := by
      constructor
      . simpa using hk
      . norm_cast at hk'; simp; omega
    specialize h1 h3
    dsimp at h1
    symm
    convert h1 using 3
    calc
      ((1 : ℝ) + 1 / k) ^ k = (1 + 1 / k) ^ (k : ℝ) := by norm_cast
      _ = _ := by congr 1; simp


-- (1 + x) ^ (1 / x) = exp ((1 / x) * log (1 + x)) = exp ((1 / x) * (x + o(x)))
-- = exp (1 + o(1)) = exp 1 * exp (o(1)) = exp 1 * (1 + o(1)) = exp 1 + o(1)
  have ⟨e1, he1, h1⟩ := taylor_rlog_one_add_littleO_order1
  have ⟨e2, he2, h2⟩ := taylor_rexp_littleO_order0
  replace h2 := he1.eventually h2
  use λ x ↦ exp 1 * e2 (e1 x)
  use by
    convert_to Tendsto (λ x ↦ rexp 1 * e2 (e1 x)) (𝓝 0) (𝓝 (rexp 1 * 0)) using 2
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
