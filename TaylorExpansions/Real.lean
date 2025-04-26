import TaylorExpansions.Complex

namespace Real
open Filter Topology Finset

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + E x * x ^ (n + 1) := by
  have h1 := taylor_bigO_of_series_at_zero (λ x : ℝ ↦ 1 / (1 - x)) (λ n : ℕ ↦ (1 : ℝ)) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n ↦ x ^ n) (1 - x)⁻¹ from by simpa using this
    exact hasSum_geometric_of_norm_lt_one hx
    ) n
  convert h1 using 11
  ring

/-- `1 / (1 - x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + E x * x := by
  convert taylor_one_div_one_sub_bigO 0 using 9 with O C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + x + E x * x ^ 2 := by
  convert taylor_one_div_one_sub_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + e x * x ^ n := by
    exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_sub_bigO n)

/-- `1 / (1 - x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + e x := by
  convert taylor_one_div_one_sub_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + x + e x * x := by
  convert taylor_one_div_one_sub_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]


/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
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

/-- `1 / (1 + x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 + E x * x := by
  convert taylor_one_div_one_add_bigO 0 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `1 / (1 + x) = 1 - x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 - x + E x * x ^ 2 := by
  convert taylor_one_div_one_add_bigO 1 using 10 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]
  ring

/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_add_bigO n)

/-- `1 / (1 + x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 + e x := by
  convert taylor_one_div_one_add_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 + x) = 1 - x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 - x + e x * x := by
  convert taylor_one_div_one_add_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]
  ring


/-- `log (1 - x) = -x - x²/2 - ... - xⁿ/n + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = ∑ k ∈ range (n + 1), -1 / k * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_log_one_sub_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ log (1 - x)) (λ x ↦ ∑ k ∈ range (n + 1), -1 / k * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . rw [Complex.ofReal_log]
    . simp
    . have hx2 := hx.right
      rw [abs_lt] at hx2
      linarith
  . norm_cast

/-- `log (1 - x) = O(x)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = E x * x := by
  convert taylor_log_one_sub_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 - x) = -x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = -x + E x * x ^ 2 := by
  convert taylor_log_one_sub_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `log (1 - x) = -x - x²/2 - ... - xⁿ/n + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = ∑ k ∈ range (n + 1), -1 / k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_log_one_sub_bigO n)

/-- `log (1 - x) = o(1)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = e x := by
  convert taylor_log_one_sub_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 - x) = -x + o(x)` as `x ⟶ 0`. -/
theorem taylor_log_one_sub_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = -x + e x * x := by
  convert taylor_log_one_sub_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]


/-- `log (1 + x) = x - x²/2 + ... + (-1)ⁿ⁺¹ xⁿ/n + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_log_one_add_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ log (1 + x)) (λ x ↦ ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . rw [Complex.ofReal_log]
    . simp
    . have hx2 := hx.right
      rw [abs_lt] at hx2
      linarith
  . norm_cast

/-- `log (1 + x) = O(x)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = E x * x := by
  convert taylor_log_one_add_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 + x) = x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = x + E x * x ^ 2 := by
  convert taylor_log_one_add_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `log (1 + x) = x - x²/2 + ... + (-1)ⁿ⁺¹ xⁿ/n + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_log_one_add_bigO n)

/-- `log (1 + x) = o(1)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = e x := by
  convert taylor_log_one_add_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 + x) = x + o(x)` as `x ⟶ 0`. -/
theorem taylor_log_one_add_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = x + e x * x := by
  convert taylor_log_one_add_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]


open Nat in
/-- `exp(x) = 1 + x + x²/2 + x³/6 + ... + xⁿ/n! + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_exp_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = ∑ k ∈ range (n + 1), 1 / k ! * x ^ k + E x * x ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℝ ↦ exp x) (λ n : ℕ ↦ 1 / n !) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (fun n => (n !⁻¹ : ℝ) • x ^ n) (NormedSpace.exp ℝ x) from by
      convert this using 1
      . field_simp
      . rw [exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' x
    ) n

/-- `exp(x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_exp_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = 1 + E x * x := by
  convert taylor_exp_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `exp(x) = 1 + x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_exp_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = 1 + x + E x * x ^ 2 := by
  convert taylor_exp_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

open Nat in
/-- `exp(x) = 1 + x + x²/2 + x³/6 + ... + xⁿ/n! + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_exp_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = ∑ k ∈ range (n + 1), 1 / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_exp_bigO n)

/-- `exp(x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_exp_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = 1 + e x := by
  convert taylor_exp_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `exp(x) = 1 + x + o(x)` as `x ⟶ 0`. -/
theorem taylor_exp_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = 1 + x + e x * x := by
  convert taylor_exp_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]


open Nat in
/-- `(1 + x) ^ a = 1 + a * x + ... + a(a - 1)...(a - n + 1)/n! * xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_bigO (n : ℕ) (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_one_add_pow_bigO n a
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ (1 + x) ^ a) (λ x ↦ ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . norm_cast
    refine Complex.ofReal_cpow ?_ a
    have hx2 := hx.right
    rw [abs_lt] at hx2
    linarith
  . norm_cast

/-- `(1 + x) ^ a = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_bigO_order0 (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + E x * x := by
  convert taylor_one_add_pow_bigO 0 a using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `(1 + x) ^ a = 1 + a * x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_bigO_order1 (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + a * x + E x * x ^ 2 := by
  convert taylor_one_add_pow_bigO 1 a using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

open Nat in
/-- `(1 + x) ^ a = 1 + a * x + ... + a(a - 1)...(a - n + 1)/n! * xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_littleO (n : ℕ) (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_add_pow_bigO n a)

/-- `(1 + x) ^ a = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_littleO_order0 (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + e x := by
  convert taylor_one_add_pow_littleO 0 a using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `(1 + x) ^ a = 1 + a * x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_add_pow_littleO_order1 (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + a * x + e x * x := by
  convert taylor_one_add_pow_littleO 1 a using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]


open Nat in
/-- `√(1 + x) = 1 + x/2 - x²/8 + ... + (1/2)(1/2 - 1)...(1/2 - n + 1)/n! * xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = ∑ k ∈ range (n + 1), (∏ j ∈ range k, ((1 : ℝ) / 2 - j)) / k ! * x ^ k + E x * x ^ (n + 1) := by
  convert taylor_one_add_pow_bigO n (1 / 2) using 9 with E C hE x
  apply sqrt_eq_rpow

/-- `√(1 + x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + E x * x := by
  convert taylor_sqrt_one_add_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `√(1 + x) = 1 + x/2 + O(x²)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + x / 2 + E x * x ^ 2 := by
  convert taylor_sqrt_one_add_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  field_simp [h1]

open Nat in
/-- `√(1 + x) = 1 + x/2 - x²/8 + ... + (1/2)(1/2 - 1)...(1/2 - n + 1)/n! * xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = ∑ k ∈ range (n + 1), (∏ j ∈ range k, ((1 : ℝ) / 2 - j)) / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sqrt_one_add_bigO n)

/-- `√(1 + x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + e x := by
  convert taylor_sqrt_one_add_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `√(1 + x) = 1 + x/2 + o(x)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + x / 2 + e x * x := by
  convert taylor_sqrt_one_add_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  field_simp [h1]


open Nat in
/-- `cos(x) = 1 - x²/2 + ... + (-1)ᵐ x²ᵐ/(2m)! + O(x²ᵐ⁺²)` as `x ⟶ 0`. -/
theorem taylor_cos_bigO (m : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cos x = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k) + E x * x ^ (2 * m + 2) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_cos_bigO m
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ cos x) (λ x ↦ ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k)) (2 * m + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 1
  . simp
  . norm_cast

/-- `cos(x) = 1 + O(x²)` as `x ⟶ 0`. -/
theorem taylor_cos_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cos x = 1 + E x * x ^ 2 := by
  convert taylor_cos_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

open Nat in
/-- `cos(x) = 1 - x²/2 + ... + (-1)ᵐ x²ᵐ/(2m)! + o(x²ᵐ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_cos_littleO (m : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cos x = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k) + e x * x ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_cos_bigO m)

/-- `cos(x) = 1 + o(x)` as `x ⟶ 0`. -/
theorem taylor_cos_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cos x = 1 + e x * x := by
  convert taylor_cos_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]


open Nat in
/-- `sin(x) = x - x³/6 + ... + (-1)ⁿ x²ⁿ⁺¹/(2n + 1)! + O(x²ⁿ⁺²)` as `x ⟶ 0`. -/
theorem taylor_sin_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, sin x = ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) ! * x ^ (2 * k + 1) + E x * x ^ (2 * n + 2) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_sin_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ sin x) (λ x ↦ ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) ! * x ^ (2 * k + 1)) (2 * n + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 1
  . simp
  . norm_cast

/-- `sin(x) = x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_sin_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, sin x = x + E x * x ^ 2 := by
  convert taylor_sin_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

open Nat in
/-- `sin(x) = x - x³/6 + ... + (-1)ⁿ x²ⁿ⁺¹/(2n + 1)! + o(x²ⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_sin_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, sin x = ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) ! * x ^ (2 * k + 1) + e x * x ^ (2 * n + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sin_bigO n)

/-- `sin(x) = x + o(x)` as `x ⟶ 0`. -/
theorem taylor_sin_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, sin x = x + e x * x := by
  convert taylor_sin_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]


/-- `arctan(x) = x - x³/3 + ... + (-1)ⁿ x²ⁿ⁺¹/(2n + 1) + O(x²ⁿ⁺²)` as `x ⟶ 0`. -/
theorem taylor_arctan_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, arctan x = ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) * x ^ (2 * k + 1) + E x * x ^ (2 * n + 2) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_arctan_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ arctan x) (λ x ↦ ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) * x ^ (2 * k + 1)) (2 * n + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 1
  . simp
  . norm_cast

/-- `arctan(x) = x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_arctan_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, arctan x = x + E x * x ^ 2 := by
  convert taylor_arctan_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `arctan(x) = x - x³/3 + ... + (-1)ⁿ x²ⁿ⁺¹/(2n + 1) + o(x²ⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_arctan_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, arctan x = ∑ k ∈ range (n + 1), (-1) ^ k / (2 * k + 1) * x ^ (2 * k + 1) + e x * x ^ (2 * n + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_arctan_bigO n)

/-- `arctan(x) = x + o(x)` as `x ⟶ 0`. -/
theorem taylor_arctan_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, arctan x = x + e x * x := by
  convert taylor_arctan_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]


open Nat in
/-- `cosh(x) = 1 + x²/2 + ... + x²ⁿ/(2n)! + O(x²ⁿ⁺²)` as `x ⟶ 0`. -/
theorem taylor_cosh_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cosh x = ∑ k ∈ range (n + 1), 1 / (2 * k) ! * x ^ (2 * k) + E x * x ^ (2 * n + 2) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_cosh_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ cosh x) (λ x ↦ ∑ k ∈ range (n + 1), 1 / (2 * k) ! * x ^ (2 * k)) (2 * n + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 2
  . simp
  . norm_cast
    apply sum_congr rfl
    intro k hk
    ring

/-- `cosh(x) = 1 + O(x²)` as `x ⟶ 0`. -/
theorem taylor_cosh_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cosh x = 1 + E x * x ^ 2 := by
  convert taylor_cosh_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

open Nat in
/-- `cosh(x) = 1 + x²/2 + ... + x²ⁿ/(2n)! + o(x²ⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_cosh_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cosh x = ∑ k ∈ range (n + 1), 1 / (2 * k) ! * x ^ (2 * k) + e x * x ^ (2 * n + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_cosh_bigO n)

/-- `cosh(x) = 1 + o(x)` as `x ⟶ 0`. -/
theorem taylor_cosh_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cosh x = 1 + e x * x := by
  convert taylor_cosh_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]


open Nat in
/-- `sinh(x) = x + x³/6 + ... + x²ⁿ⁺¹/(2n + 1)! + O(x²ⁿ⁺²)` as `x ⟶ 0`. -/
theorem taylor_sinh_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, sinh x = ∑ k ∈ range (n + 1), 1 / (2 * k + 1) ! * x ^ (2 * k + 1) + E x * x ^ (2 * n + 2) := by
  have ⟨E, C, hE, h1⟩ := Complex.taylor_sinh_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ sinh x) (λ x ↦ ∑ k ∈ range (n + 1), 1 / (2 * k + 1) ! * x ^ (2 * k + 1)) (2 * n + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 2
  . simp
  . norm_cast
    apply sum_congr rfl
    intro k hk
    ring

/-- `sinh(x) = x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_sinh_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, sinh x = x + E x * x ^ 2 := by
  convert taylor_sinh_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

open Nat in
/-- `sinh(x) = x + x³/6 + ... + x²ⁿ⁺¹/(2n + 1)! + o(x²ⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_sinh_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, sinh x = ∑ k ∈ range (n + 1), 1 / (2 * k + 1) ! * x ^ (2 * k + 1) + e x * x ^ (2 * n + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sinh_bigO n)

/-- `sinh(x) = x + o(x)` as `x ⟶ 0`. -/
theorem taylor_sinh_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, sinh x = x + e x * x := by
  convert taylor_sinh_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]


end Real
