import TaylorExpansions.Basic

namespace Complex
open Filter Topology Finset

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + E x * x ^ (n + 1) := by
  have h1 := taylor_bigO_of_series_at_zero (λ x : ℂ ↦ 1 / (1 - x)) (λ n : ℕ ↦ (1 : ℂ)) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n ↦ x ^ n) (1 - x)⁻¹ from by simpa using this
    exact hasSum_geometric_of_norm_lt_one hx
    ) n
  convert h1 using 11
  ring

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + e x * x ^ n := by
    exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_sub_bigO n)


/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ k * x ^ k + E x * x ^ (n + 1) := by
  obtain ⟨E, C, hE, h1⟩ := taylor_one_div_one_sub_bigO n
  use λ x ↦ E (-x) * (-1) ^ (n + 1), C, by
    rw [Metric.eventually_nhds_iff] at hE ⊢
    obtain ⟨ε, hε, hE⟩ := hE
    use ε, hε
    intro x hx
    simpa using hE (by simpa using hx)
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  specialize h1 (y := -x) (by simpa using hx)
  convert h1 using 2
  . simp
  . apply sum_congr rfl
    intro k hk
    ring
  . ring

/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_add_bigO n)



/-- `log (1 - z) = -z - z²/2 - ... - zⁿ/n + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_log_one_sub_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, log (1 - z) = ∑ k ∈ range (n + 1), -1 / k * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ log (1 - x)) (λ n : ℕ ↦ -1 / n) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n : ℕ ↦ x ^ n / n) (-log (1 - x)) from by
      convert this.neg using 1
      . field_simp
      . simp
    exact hasSum_taylorSeries_neg_log hx
    ) n

/-- `log (1 - z) = -z - z²/2 - ... - zⁿ/n + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_log_one_sub_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, log (1 - z) = ∑ k ∈ range (n + 1), -1 / k * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_log_one_sub_bigO n)

/-- `log (1 + z) = z - z²/2 + ... + (-1)ⁿ⁺¹ zⁿ/n + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_log_one_add_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, log (1 + z) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ log (1 + x)) (λ n : ℕ ↦ (-1) ^ (n + 1) / n) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n : ℕ ↦ (-1) ^ (n + 1) * x ^ n / n) (log (1 + x)) from by
      convert this using 1
      field_simp
    exact hasSum_taylorSeries_log hx
    ) n

/-- `log (1 + z) = z - z²/2 + ... + (-1)ⁿ⁺¹ zⁿ/n + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_log_one_add_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, log (1 + z) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * z ^ k + e z * z ^ n := by
    exact taylor_littleO_of_bigO_at_zero (taylor_log_one_add_bigO n)


open Nat in
/-- `exp(z) = 1 + z + z²/2 + z³/6 + ... + zⁿ/n! + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_exp_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, exp z = ∑ k ∈ range (n + 1), 1 / k ! * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ exp x) (λ n : ℕ ↦ 1 / n !) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (fun n => (n !⁻¹ : ℂ) • x ^ n) (NormedSpace.exp ℂ x) from by
      convert this using 1
      . field_simp
      . rw [exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' x
    ) n

open Nat in
/-- `exp(z) = 1 + z + z²/2 + z³/6 + ... + zⁿ/n! + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_exp_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, exp z = ∑ k ∈ range (n + 1), 1 / k ! * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_exp_bigO n)


open Nat in
/-- `(1 + z) ^ a = 1 + a * z + ... + a(a - 1)...(a - n + 1)/n! * zⁿ + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_one_add_pow_bigO (n : ℕ) (a : ℂ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, (1 + z) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * z ^ k + E z * z ^ (n + 1) := by
  have h0 z (hz : z ∈ Metric.ball 0 1) : 1 + z ∈ slitPlane := by
    left
    simp only [add_re, one_re]
    simp at hz
    have d1 := abs_le.mp (Complex.abs_re_le_abs z)
    linarith
  have ⟨E, C, hE, h1⟩ :=
    taylor_bigO_of_series_at_zero_of_differentiableOn_ℂ (λ z ↦ (1 + z) ^ a) 1 (by norm_num) (by
      let f (z : ℂ) := (1 + z)
      let g (z : ℂ) := z ^ a
      show DifferentiableOn _ (g ∘ f) _
      apply DifferentiableOn.comp (t := slitPlane)
      . intro z hz
        exact DifferentiableWithinAt.cpow (by fun_prop) (by fun_prop) hz
      . fun_prop
      . exact h0) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, h1⟩ := h1
  rw [Metric.eventually_nhds_iff]
  use ε ⊓ 1
  use by simp [hε]
  intro z hz
  simp at hz
  specialize h1 (by simpa using hz.left)
  convert h1 using 5 with k hk
  have h1 k (z : ℂ) (hz : z ∈ Metric.ball 0 1) : (iteratedDeriv k (fun z => (1 + z) ^ a) z) = (∏ j ∈ range k, (a - j)) * (1 + z) ^ (a - k) := by
    induction' k with k ih generalizing z hz
    . simp
    . calc
        _ = deriv (λ y ↦ (iteratedDeriv k fun z => (1 + z) ^ a) y) z := by rw [iteratedDeriv_succ]
        _ = derivWithin (λ y ↦ (iteratedDeriv k fun z => (1 + z) ^ a) y) (Metric.ball 0 1) z := by
          refine Eq.symm (derivWithin_of_isOpen ?_ hz)
          exact Metric.isOpen_ball
        _ = derivWithin (λ y ↦ ((∏ j ∈ range k, (a - j)) * (1 + y) ^ (a - k))) (Metric.ball 0 1) z := by
          apply derivWithin_congr
          . intro y hy; simp [ih y hy]
          . simp [ih z hz]
        _ = deriv (λ y ↦ ((∏ j ∈ range k, (a - j)) * (1 + y) ^ (a - k))) z := by
          refine derivWithin_of_isOpen ?_ hz
          exact Metric.isOpen_ball
        _ = (∏ j ∈ range k, (a - j)) * deriv (fun x => (1 + x) ^ (a - k)) z := by simp
        _ = (∏ j ∈ range k, (a - j)) * ((a - k) * (1 + z) ^ (a - (k + 1))) := by
          congr 1
          let f (z : ℂ) := (1 + z)
          let g (z : ℂ) := z ^ (a - k)
          have d1 : 1 + z ∈ slitPlane := by
            left
            simp only [add_re, one_re]
            simp at hz
            have d1 := abs_le.mp (Complex.abs_re_le_abs z)
            linarith
          show deriv (g ∘ f) z = _
          have c1 : deriv f z = 1 := by
            rw [deriv_add]
            rw [deriv_const]
            rw [deriv_id'']
            . simp
            . fun_prop
            . fun_prop
          have c2 : deriv g (1 + z) = (a - k) * (1 + z) ^ (a - k - 1) := by
            exact (hasStrictDerivAt_cpow_const d1).hasDerivAt.deriv
          rw [deriv_comp]
          . rw [c1, c2]
            ring_nf
          . exact (hasStrictDerivAt_cpow_const d1).differentiableAt
          . fun_prop
        _ = _ := by simp [prod_range_succ]; ring
  simp [h1 k 0 (by simp)]

open Nat in
/-- `(1 + z) ^ a = 1 + a * z + ... + a(a - 1)...(a - n + 1)/n! * zⁿ + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_one_add_pow_littleO (n : ℕ) (a : ℂ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, (1 + z) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_add_pow_bigO n a)


open Nat in
-- `cos(z) = 1 - z²/2 + ... + (-1)ᵐ z²ᵐ/(2m)! + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_cos_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, cos z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * z ^ (2 * k) + E z * z ^ (2 * m + 2) := by
  have h1 := taylor_bigO_of_series_at_zero cos (λ j : ℕ ↦ if j % 2 = 0 then (-1) ^ (j / 2) / j ! else 0) 1 (by norm_num) (by
    intro z hz
    convert Complex.hasSum_cos z using 0
    apply hasSum_iff_hasSum_of_ne_zero_bij (λ ⟨k, hk⟩ ↦ 2 * k)
    . intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp at hij
      simp [hij]
    . intro j hj
      obtain ⟨hj1, hj2, hj3⟩ : j % 2 = 0 ∧ ¬j ! = 0 ∧ (z = 0 → j = 0) := by simpa using hj
      simp
      use j / 2
      split_ands
      . intro hz; simp [hj3 hz]
      . convert hj2 using 3; omega
      . omega
    . intro ⟨k, hk⟩
      simp
      ring
  ) (2 * m + 1)
  convert h1 using 10 with E C hE z
  have h2 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h2, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = (-1) ^ k / ↑(2 * k)! * z ^ (2 * k) + 0 := by simp
    _ = _ := by
      have c1 : (2 * k) % 2 = 0 := by omega
      have c2 : (2 * k + 1) % 2 ≠ 0 := by omega
      simp [c1, c2]

open Nat in
/-- `cos(z) = 1 - z²/2 + ... + (-1)ᵐ z²ᵐ/(2m)! + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_cos_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, cos z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * z ^ (2 * k) + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_cos_bigO m)


open Nat in
-- `sin(z) = z - z³/6 + ... + (-1)ᵐ z²ᵐ⁺¹/(2m + 1)! + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_sin_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, sin z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k + 1) ! * z ^ (2 * k + 1) + E z * z ^ (2 * m + 2) := by
  have h1 := taylor_bigO_of_series_at_zero sin (λ j : ℕ ↦ if j % 2 = 1 then (-1) ^ (j / 2) / j ! else 0) 1 (by norm_num) (by
    intro z hz
    convert Complex.hasSum_sin z using 0
    apply hasSum_iff_hasSum_of_ne_zero_bij (λ ⟨k, hk⟩ ↦ 2 * k + 1)
    . intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp at hij
      simp [hij]
    . intro j hj
      obtain ⟨hj1, hj2, hj3⟩ : j % 2 = 1 ∧ ¬j ! = 0 ∧ (z = 0 → j = 0) := by simpa using hj
      simp
      use j / 2
      split_ands
      . intro hz; specialize hj3 hz; omega
      . convert hj2 using 3; omega
      . omega
    . intro ⟨k, hk⟩
      have c1 : (2 * k + 1) % 2 = 1 := by omega
      have c2 : (2 * k + 1) / 2 = k := by omega
      simp [c1, c2]
      ring
  ) (2 * m + 1)
  convert h1 using 10 with E C hE z
  have h2 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h2, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = (-1) ^ k / (2 * k + 1) ! * z ^ (2 * k + 1) + 0 := by simp
    _ = _ := by
      have c1 : (2 * k) % 2 ≠ 1 := by omega
      have c2 : (2 * k + 1) % 2 = 1 := by omega
      have c3 : (2 * k + 1) / 2 = k := by omega
      simp [c1, c2, c3]

open Nat in
-- `sin(z) = z - z³/6 + ... + (-1)ᵐ z²ᵐ⁺¹/(2m + 1)! + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_sin_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, sin z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k + 1) ! * z ^ (2 * k + 1) + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sin_bigO m)


-- `arctan(z) = z - z³/3 + ... + (-1)ᵐ z²ᵐ⁺¹/(2m + 1) + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_arctan_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, arctan z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k + 1) * z ^ (2 * k + 1) + E z * z ^ (2 * m + 2) := by
  have h1 := taylor_bigO_of_series_at_zero arctan (λ j : ℕ ↦ if j % 2 = 1 then (-1) ^ (j / 2) / j else 0) 1 (by norm_num) (by
    intro z hz
    convert Complex.hasSum_arctan hz using 0
    apply hasSum_iff_hasSum_of_ne_zero_bij (λ ⟨k, hk⟩ ↦ 2 * k + 1)
    . intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp at hij
      simp [hij]
    . intro j hj
      obtain ⟨hj1, hj2, hj3⟩ : j % 2 = 1 ∧ ¬j = 0 ∧ (z = 0 → j = 0) := by simpa using hj
      simp
      use j / 2
      split_ands
      . intro hz; specialize hj3 hz; omega
      . norm_cast
      . omega
    . intro ⟨k, hk⟩
      have c1 : (2 * k + 1) % 2 = 1 := by omega
      have c2 : (2 * k + 1) / 2 = k := by omega
      simp [c1, c2]
      ring
  ) (2 * m + 1)
  convert h1 using 10 with E C hE z
  have h2 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h2, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = (-1) ^ k / (2 * k + 1) * z ^ (2 * k + 1) + 0 := by simp
    _ = _ := by
      have c1 : (2 * k) % 2 ≠ 1 := by omega
      have c2 : (2 * k + 1) % 2 = 1 := by omega
      have c3 : (2 * k + 1) / 2 = k := by omega
      simp [c1, c2, c3]

-- `arctan(z) = z - z³/3 + ... + (-1)ᵐ z²ᵐ⁺¹/(2m + 1) + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_arctan_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, arctan z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k + 1) * z ^ (2 * k + 1) + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_arctan_bigO m)


open Nat in
-- `cosh(z) = 1 + z²/2 + ... + z²ᵐ/(2m)! + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_cosh_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, cosh z = ∑ k ∈ range (m + 1), z ^ (2 * k) / (2 * k) ! + E z * z ^ (2 * m + 2) := by
  have h1 := taylor_bigO_of_series_at_zero cosh (λ j : ℕ ↦ if j % 2 = 0 then 1 / j ! else 0) 1 (by norm_num) (by
    intro z hz
    convert Complex.hasSum_cosh z using 0
    apply hasSum_iff_hasSum_of_ne_zero_bij (λ ⟨k, hk⟩ ↦ 2 * k)
    . intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp at hij
      simp [hij]
    . intro j hj
      obtain ⟨hj1, hj2, hj3⟩ : j % 2 = 0 ∧ ¬j ! = 0 ∧ (z = 0 → j = 0) := by simpa using hj
      simp
      use j / 2
      split_ands
      . intro hz; specialize hj3 hz; omega
      . convert hj2 using 3; omega
      . omega
    . intro ⟨k, hk⟩
      have c1 : (2 * k) % 2 = 0 := by omega
      have c2 : (2 * k) / 2 = k := by omega
      simp [c1, c2]
      ring
  ) (2 * m + 1)
  convert h1 using 10 with E C hE z
  have h2 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h2, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = z ^ (2 * k) / (2 * k) ! + 0 := by simp
    _ = _ := by
      have c1 : (2 * k) % 2 = 0 := by omega
      have c2 : (2 * k + 1) % 2 ≠ 0 := by omega
      simp [c1, c2]
      ring

open Nat in
-- `cosh(z) = 1 + z²/2 + ... + z²ᵐ/(2m)! + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_cosh_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, cosh z = ∑ k ∈ range (m + 1), z ^ (2 * k) / (2 * k) ! + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_cosh_bigO m)


open Nat in
-- `sinh(z) = z + z³/6 + ... + z²ᵐ⁺¹/(2m + 1)! + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_sinh_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, sinh z = ∑ k ∈ range (m + 1), z ^ (2 * k + 1) / (2 * k + 1) ! + E z * z ^ (2 * m + 2) := by
  have h1 := taylor_bigO_of_series_at_zero sinh (λ j : ℕ ↦ if j % 2 = 1 then 1 / j ! else 0) 1 (by norm_num) (by
    intro z hz
    convert Complex.hasSum_sinh z using 0
    apply hasSum_iff_hasSum_of_ne_zero_bij (λ ⟨k, hk⟩ ↦ 2 * k + 1)
    . intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp at hij
      simp [hij]
    . intro j hj
      obtain ⟨hj1, hj2, hj3⟩ : j % 2 = 1 ∧ ¬j ! = 0 ∧ (z = 0 → j = 0) := by simpa using hj
      simp
      use j / 2
      split_ands
      . intro hz; specialize hj3 hz; omega
      . convert hj2 using 3; omega
      . omega
    . intro ⟨k, hk⟩
      have c1 : (2 * k + 1) % 2 = 1 := by omega
      have c2 : (2 * k + 1) / 2 = k := by omega
      simp [c1, c2]
      ring
  ) (2 * m + 1)
  convert h1 using 10 with E C hE z
  have h2 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h2, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = z ^ (2 * k + 1) / (2 * k + 1) ! + 0 := by simp
    _ = _ := by
      have c1 : (2 * k) % 2 ≠ 1 := by omega
      have c2 : (2 * k + 1) % 2 = 1 := by omega
      simp [c1, c2]
      ring

open Nat in
-- `sinh(z) = z + z³/6 + ... + z²ᵐ⁺¹/(2m + 1)! + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_sinh_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, sinh z = ∑ k ∈ range (m + 1), z ^ (2 * k + 1) / (2 * k + 1) ! + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sinh_bigO m)


end Complex
