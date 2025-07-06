--auther bangji hu
import Mathlib

open Finset Real Nat

/--e is irrational-/
theorem e_irrational_complete : Irrational (exp 1) := by
  

  rw [irrational_iff_ne_rational]
  intro a b h_eq

  wlog hb_pos : 0 < b generalizing a b
  case inr =>
    -- The denominator b cannot be zero since e ≠ 0
    have b_ne_zero : b ≠ 0 := by
      intro h_zero
      rw [h_zero, Int.cast_zero, div_zero] at h_eq
      exact Real.exp_ne_zero 1 h_eq
    -- If b is not positive, then it must be negative
    have b_neg : b < 0 := by
      push_neg at hb_pos
      exact lt_of_le_of_ne hb_pos b_ne_zero
    -- Negating b gives us a positive denominator
    have neg_b_pos : 0 < (-b) := neg_pos.mpr b_neg
    -- We can rewrite the equation with negated numerator and denominator
    have h_eq_neg : Real.exp 1 = ↑(-a) / ↑(-b) := by
      simp only [Int.cast_neg] at h_eq ⊢
      rw [h_eq]; ring
    exact this (-a) (-b) h_eq_neg neg_b_pos

  -- The denominator is nonzero since b > 0
  have b_ne_zero : b ≠ 0 := ne_of_gt hb_pos
  let q := b.natAbs
  -- We work with the natural number q = |b|
  have q_pos : 0 < q := Int.natAbs_pos.mpr b_ne_zero
  -- Since b > 0, we have b = q
  have hb_eq : b = ↑q := (Int.natAbs_of_nonneg (le_of_lt hb_pos)).symm

  by_cases h_q_eq_one : q = 1
  ·    -- We know that e is between 2 and 3
    have h_e_bounds : 2 < Real.exp 1 ∧ Real.exp 1 < 3 := by
      constructor
      case left =>
        linarith [exp_one_gt_d9]
      case right =>
        linarith [exp_one_lt_d9]
    -- No integer lies strictly between 2 and 3
    have h_not_int : ¬∃ n : ℤ, Real.exp 1 = n := by
      intro ⟨n, hn⟩
      -- n must be greater than 2 since exp(1) > 2
      have h_gt_2 : (2 : ℝ) < n := by rw [← hn]; exact h_e_bounds.1
      -- n must be less than 3 since exp(1) < 3
      have h_lt_3 : (n : ℝ) < 3 := by rw [← hn]; exact h_e_bounds.2
      -- Since n > 2 as an integer, we must have n ≥ 3
      have h_ge_3 : 3 ≤ n := by
        -- Convert the real inequality to integer inequality
        have : 2 < n := Int.cast_lt.mp h_gt_2
        omega
      -- But n < 3 as a real number, contradiction
      have : n < 3 := Int.cast_lt.mp h_lt_3
      omega
    -- If q = 1, then exp(1) = a which contradicts that e is not an integer
    have h_eq_one : Real.exp 1 = a := by
      -- When q = 1, we have b = 1
      have : b = 1 := by rw [hb_eq, h_q_eq_one]; simp
      rw [this] at h_eq
      simp at h_eq
      exact h_eq
    exact h_not_int ⟨a, h_eq_one⟩

  -- Since q ≠ 1 and q > 0, we have q ≥ 2
  have h_q_ge_two : 2 ≤ q := by
    push_neg at h_q_eq_one
    have h_q_ne_one : q ≠ 1 := h_q_eq_one
    omega

  let S_q := expNear (q + 1) 1 0
  let R_q := Real.exp 1 - S_q

  -- S_q is the partial sum of the exponential series up to q terms
  have h_S_q_eq : S_q = ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial := by
    simp only [S_q, expNear, mul_zero, add_zero]
    congr 1
    ext k
    simp [one_pow]

  -- The remainder R_q is bounded by 1/(q·q!)
  -- and there is at least one positive term outside the partial sum,
  -- then its partial sum is strictly less than its total sum.
  have my_sum_lt_tsum_of_nonneg {f : ℕ → ℝ} {s : Finset ℕ} (h_summable : Summable f)
      (h_nonneg : ∀ i, 0 ≤ f i) (h_exists_pos : ∃ i, i ∉ s ∧ 0 < f i) :
      ∑ i ∈ s, f i < tsum f := by
    by_contra h_contra
    push_neg at h_contra
    -- If partial sum ≥ total sum, then they must be equal by antisymmetry
    have h_eq : ∑ i ∈ s, f i = tsum f := by
      apply le_antisymm
      · exact sum_le_tsum s (fun i _ => h_nonneg i) h_summable
      · exact h_contra
    obtain ⟨i, hi_not_in_s, hi_pos⟩ := h_exists_pos
    let s' := s ∪ {i}
    -- Adding the positive term makes the partial sum strictly larger
    have h_strict : ∑ j ∈ s, f j < ∑ j ∈ s', f j := by
      rw [sum_union (disjoint_singleton_right.mpr hi_not_in_s)]
      rw [sum_singleton]
      linarith
    -- The extended partial sum is still bounded by the total sum
    have h_sum'_le : ∑ j ∈ s', f j ≤ tsum f := by
      exact sum_le_tsum s' (fun j _ => h_nonneg j) h_summable
    rw [h_eq] at h_strict
    exact not_lt.mpr h_sum'_le h_strict
  have h_remainder_bound : R_q < 1 / (q * q.factorial) := by
    simp only [R_q]
    rw [h_S_q_eq]

    -- The key bound: exp(1) - partial sum < 1/(q·q!)
    have h_remainder_lt : Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial <
        1 / (q * q.factorial) := by
      -- Helper function: exponential series representation for any real number
      have add (x : ℝ) : HasSum (fun n => x ^ n / n.factorial) (Real.exp x) := by
         convert NormedSpace.expSeries_div_hasSum_exp ℝ x
         exact Real.exp_eq_exp_ℝ
      -- exp(1) equals the infinite series sum
      have series : Real.exp 1 = ∑' k : ℕ, (1 : ℝ) / (k.factorial : ℝ) := by
         rw [← (add 1).tsum_eq]
         apply congr_arg
         funext n
         simp
      -- Error bound from Taylor's theorem with remainder
      have h_bound : |Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial| ≤
                     1 ^ (q + 1) * ((q + 1).succ / ((q + 1).factorial * (q + 1))) := by
        -- |1| ≤ 1 for the Taylor bound
        have hx_le_one : |(1 : ℝ)| ≤ 1 := by
         rw [abs_one]
        convert Real.exp_bound hx_le_one (by linarith : 0 < q + 1)
        simp_rw [one_pow];simp;simp

      -- Simplify the bound expression
      have h_simpl : (1 : ℝ) ^ (q + 1) * (((q + 1).succ : ℝ) / (((q + 1).factorial : ℝ) * ((q + 1) : ℝ))) =
                     ((q + 2) : ℝ) / (((q + 1).factorial : ℝ) * ((q + 1) : ℝ)) := by
         simp [one_pow, succ_eq_add_one]
         ring
      -- The remainder is positive (partial sum < infinite sum)
      have h_pos : 0 < Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial := by
        rw [sub_pos, series]
        apply my_sum_lt_tsum_of_nonneg
        · -- The exponential series is summable
          have h_summable : Summable (fun n : ℕ => (1 : ℝ) ^ n / n.factorial) := by
            apply summable_pow_div_factorial
          simpa [one_pow] using h_summable
        · intro i
          apply div_nonneg
          norm_num
          exact Nat.cast_nonneg _
        · use (q + 1)
          constructor
          · simp [range_succ]
          · apply div_pos
            norm_num
            exact Nat.cast_pos.mpr (Nat.factorial_pos _)

      -- Use the error bound to get an upper bound for the remainder
      have h_bound' : Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial ≤
              (q + 2) / ((q + 1).factorial * (q + 1)) := by
        rw [← abs_of_pos h_pos]
        calc |Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial|
          _ ≤ 1 ^ (q + 1) * ((q + 1).succ / ((q + 1).factorial * (q + 1))) := h_bound
          _ = (q + 2) / ((q + 1).factorial * (q + 1)) := h_simpl

      calc Real.exp 1 - ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial
        _ ≤ (q + 2) / ((q + 1).factorial * (q + 1)) := h_bound'
        _ = (q + 2) / ((q + 1) * q.factorial * (q + 1)) := by
          rw [factorial_succ q];simp
        _ = (q + 2) / ((q + 1)^2 * q.factorial) := by ring
        _ < 1 / (q * q.factorial) := by
             rw [div_lt_div_iff₀ (by positivity) (by positivity)]
             rw [one_mul]
             rw [← mul_assoc]
             rw [mul_lt_mul_right (by positivity : (0 : ℝ) < q.factorial)]
             norm_cast
             ring_nf
             omega


    exact h_remainder_lt

  -- The remainder R_q is positive

  have h_remainder_pos : 0 < R_q := by
    simp only [R_q]
    rw [h_S_q_eq]
    -- The partial sum is strictly less than exp(1)
    have h_sum_lt : ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial < Real.exp 1 := by

      by_contra h_not_lt
      simp at h_not_lt

      -- The next term in the series is positive
      have h_next_pos : 0 < (1 : ℝ) / (q + 1).factorial := by
        apply div_pos
        · norm_num
        · exact Nat.cast_pos.mpr (factorial_pos (q + 1))

      -- Adding one more term still gives a bound ≤ exp(1)
      have h_exp_ge_next : ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial + (1 : ℝ) / (q + 1).factorial ≤ Real.exp 1 := by
        -- Extending the sum by one term
        have h_sum_eq : ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial + (1 : ℝ) / (q + 1).factorial =
          ∑ k ∈ range (q + 2), (1 : ℝ) / k.factorial := by
          rw [← sum_range_succ]

        rw [h_sum_eq]
        convert Real.sum_le_exp_of_nonneg zero_le_one (q + 2) using 1
        simp [one_pow]

      -- This leads to a contradiction: exp(1) < exp(1)
      have h_contra : Real.exp 1 < Real.exp 1 := by
        calc Real.exp 1
          _ ≤ ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial := by
            -- Alternative representation using factorial inverses
            have h_equiv : ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial = ∑ x ∈ range (q + 1), (x.factorial : ℝ)⁻¹ := by
              simp only [one_div]
            rw [h_equiv]
            exact h_not_lt
          _ < ∑ k ∈ range (q + 1), (1 : ℝ) / k.factorial + (1 : ℝ) / (q + 1).factorial := by
            linarith [h_next_pos]
          _ ≤ Real.exp 1 := h_exp_ge_next

      exact lt_irrefl _ h_contra

    linarith [h_sum_lt]

  -- Express a in terms of q and exp(1)
  have h_a_eq : (a : ℝ) = q * Real.exp 1 := by
    rw [h_eq, hb_eq]
    field_simp

  let Q := (q.factorial : ℝ)

  -- Q * S_q is an integer since S_q involves factorial fractions
  have h_QSq_int : ∃ m : ℤ, Q * S_q = m := by
    simp only [Q, S_q, h_S_q_eq, mul_sum]

    use ∑ k ∈ range (q + 1), (q.factorial / k.factorial : ℤ)

    rw [Int.cast_sum]
    apply sum_congr rfl
    intro k hk

    -- Each term k! divides q! for k ≤ q
    have hk_le : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)

    simp only [mul_one_div]

    -- k! divides q! when k ≤ q
    have h_dvd : k.factorial ∣ q.factorial := Nat.factorial_dvd_factorial hk_le
    rw [← Nat.cast_div h_dvd]
    rw [Nat.cast_div h_dvd]
    exact Eq.symm (Int.cast_div_ofNat_charZero h_dvd)
    apply Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    apply Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

  obtain ⟨m, hm⟩ := h_QSq_int

  let N := Q * a - q * m

  -- Define N = Q*a - q*m, which will be our problematic integer
  have h_N_eq : N = Q * q * R_q := by
    simp only [N]
    rw [h_a_eq, ← hm]
    ring

  -- N is an integer by construction
  have h_N_int : ∃ n : ℤ, N = n := by
    use (q.factorial : ℤ) * a - (q : ℤ) * m
    simp only [N, Q]
    norm_cast

  -- N is both positive and less than 1
  have h_N_bounds : 0 < N ∧ N < 1 := by
    constructor
    · rw [h_N_eq]
      simp only [Q]
      apply mul_pos
      apply mul_pos
      · exact Nat.cast_pos.mpr (factorial_pos q)
      · exact Nat.cast_pos.mpr q_pos
      · exact h_remainder_pos
    · rw [h_N_eq]
      simp only [Q]
      -- We need both q and q! to be positive for the calculation
      have h_q_pos : (0 : ℝ) < q := Nat.cast_pos.mpr q_pos
      -- q! is also positive
      have h_factorial_pos : (0 : ℝ) < q.factorial := Nat.cast_pos.mpr (factorial_pos q)
      calc q.factorial * q * R_q
        _ < q.factorial * q * (1 / (q * q.factorial)) := by
          apply mul_lt_mul_of_pos_left h_remainder_bound
          exact mul_pos h_factorial_pos h_q_pos
        _ = 1 := by
          -- q * q! ≠ 0 for the division cancellation
          have h_nonzero : (q : ℝ) * q.factorial ≠ 0 := by
            exact mul_ne_zero (ne_of_gt h_q_pos) (ne_of_gt h_factorial_pos)
          rw [mul_comm (q.factorial : ℝ) q]
          rw [mul_div_cancel₀ _ h_nonzero]

  obtain ⟨n, hn⟩ := h_N_int
  -- The integer n satisfies 0 < n < 1 as a real number
  have h_int_between : 0 < (n : ℝ) ∧ (n : ℝ) < 1 := by
    rw [← hn]
    exact h_N_bounds

  -- But no integer can satisfy 0 < k < 1
  have h_no_int : ¬∃ k : ℤ, 0 < (k : ℝ) ∧ (k : ℝ) < 1 := by
    intro ⟨k, h_pos, h_lt⟩
    -- If k > 0 as an integer, then k ≥ 1
    have h_ge_one : 1 ≤ k := by
      -- Convert integer positivity to real positivity
      have h_pos_int : 0 < k := Int.cast_pos.mp h_pos
      omega
    -- So k ≥ 1 as a real number too
    have h_ge_one_real : (1 : ℝ) ≤ (k : ℝ) := by
      norm_cast
    linarith [h_lt, h_ge_one_real]

  exact h_no_int ⟨n, h_int_between⟩
