import OMAStatements.S_oeis_a055203

namespace OMA.S_oeis_a055203

private theorem weight_zero : weight 0 = 1 := by
  norm_num [weight, Finset.sum_range_succ]

private theorem weight_one : weight 1 = 1 := by
  norm_num [weight, Finset.sum_range_succ, Nat.choose]

private theorem weight_two : weight 2 = 6 := by
  norm_num [weight, Finset.sum_range_succ, Nat.choose]

private theorem weight_three : weight 3 = 62 := by
  norm_num [weight, Finset.sum_range_succ, Nat.choose]

theorem term_mod12 (n : ℕ) : (term n : ZMod 12) = 1 := by
  cases n with
  | zero => simp [term, weight_zero]
  | succ n =>
    simp only [term, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_eq_single 1]
    · simp [weight_one, Nat.stirlingSecond_one_right]
    · intro k hk hk1
      rcases (show k = 0 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | rfl | hk4
      · simp
      · have h : (((2 : ℕ).factorial : ℕ) : ZMod 12) * (weight 2 : ZMod 12) = 0 := by
          rw [weight_two]
          decide
        rw [mul_right_comm, h, zero_mul]
      · have h : (((3 : ℕ).factorial : ℕ) : ZMod 12) * (weight 3 : ZMod 12) = 0 := by
          rw [weight_three]
          decide
        rw [mul_right_comm, h, zero_mul]
      · obtain ⟨q,hq⟩ := (show 12 ∣ (4 : ℕ).factorial by decide).trans
          (Nat.factorial_dvd_factorial hk4)
        have hz : ((12 : ℕ) : ZMod 12) = 0 := by decide
        rw [hq, Nat.cast_mul, hz]
        simp
    · simp

end OMA.S_oeis_a055203
namespace OMA.S_oeis_a055203

theorem term_truncate (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (term n : ZMod m) =
      ∑ k ∈ Finset.range m,
        (k.factorial : ZMod m) * (Nat.stirlingSecond n k : ZMod m) * (weight k : ZMod m) := by
  simp only [term, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
  intro k _ hk
  have hmk : m ≤ k := by simpa using hk
  obtain ⟨q, hq⟩ := (Nat.dvd_factorial hm hmk)
  simp [hq]

end OMA.S_oeis_a055203

/-- Pure powers modulo `m` have period `φ m` once the exponent is at least `m`.
The proof checks each prime-power divisor of the modulus: either the base is a
unit there and Euler's theorem applies, or the base's powers are both zero
there. -/
theorem zmod_pow_add_totient_eq_of_le {m j n : ℕ} (hm : 0 < m) (hn : m ≤ n) :
    (j : ZMod m) ^ (n + m.totient) = (j : ZMod m) ^ n := by
  have hnpos : 0 < n := lt_of_lt_of_le hm hn
  by_cases hj : j ≤ 1
  · interval_cases j <;> simp [hnpos.ne' ]
  have hj2 : 2 ≤ j := by omega
  have hle : j ^ n ≤ j ^ (n + m.totient) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)
  rw [← Nat.cast_pow, ← Nat.cast_pow]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' hle).2
  refine (Nat.dvd_iff_prime_pow_dvd_dvd (j ^ (n + m.totient) - j ^ n) m).2 ?_
  intro p k hp hpk
  by_cases hpj : p ∣ j
  · have hkn : k ≤ n := by
      by_cases hk : k = 0
      · simp [hk]
      · calc
          k ≤ p ^ k := by
            exact (Nat.lt_two_pow_self (n := k)).le.trans (Nat.pow_le_pow_left hp.two_le k)
          _ ≤ m := Nat.le_of_dvd hm hpk
          _ ≤ n := hn
    have hdiv : p ^ k ∣ j ^ n := by
      exact (Nat.pow_dvd_pow p hkn).trans (pow_dvd_pow_of_dvd hpj n)
    have hdiv' : p ^ k ∣ j ^ (n + m.totient) :=
      hdiv.trans (Nat.pow_dvd_pow j (Nat.le_add_right _ _))
    exact Nat.dvd_sub hdiv' hdiv
  · have hcop : j.Coprime (p ^ k) :=
      (Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).2 hpj)).symm
    have hEuler : j ^ (p ^ k).totient ≡ 1 [MOD p ^ k] := Nat.ModEq.pow_totient hcop
    have hφdvd : (p ^ k).totient ∣ m.totient := Nat.totient_dvd_of_dvd hpk
    obtain ⟨t, ht⟩ := hφdvd
    have hperiod : j ^ m.totient ≡ 1 [MOD p ^ k] := by
      rw [ht, pow_mul]
      simpa using Nat.ModEq.pow t hEuler
    have hpow : j ^ (n + m.totient) ≡ j ^ n [MOD p ^ k] := by
      have hmul := Nat.ModEq.mul_left (j ^ n) hperiod
      simpa [pow_add] using hmul
    exact (Nat.ModEq.symm hpow).dvd'
namespace OMA.S_oeis_a055203

/-- The ordered (labelled-block) Stirling coefficient `k! S(n,k)`, viewed in `ℤ`. -/
def orderedStirlingCoefficient (n k : ℕ) : ℤ :=
  (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ)

/-- The first row of the ordered Stirling coefficients. -/
theorem orderedStirlingCoefficient_zero (k : ℕ) :
    orderedStirlingCoefficient 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [orderedStirlingCoefficient]
  | succ k => simp [orderedStirlingCoefficient]

/-- The first column vanishes after the initial entry. -/
theorem orderedStirlingCoefficient_succ_zero (n : ℕ) :
    orderedStirlingCoefficient (n + 1) 0 = 0 := by
  simp [orderedStirlingCoefficient]

/-- Recurrence for labelled set partitions, obtained directly from
`Nat.stirlingSecond_succ_succ`. -/
theorem orderedStirlingCoefficient_succ_succ (n k : ℕ) :
    orderedStirlingCoefficient (n + 1) (k + 1) =
      (k + 1 : ℤ) * orderedStirlingCoefficient n (k + 1) +
        (k + 1 : ℤ) * orderedStirlingCoefficient n k := by
  simp only [orderedStirlingCoefficient, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [Nat.stirlingSecond_succ_succ]
  push_cast
  ring

end OMA.S_oeis_a055203

open scoped BigOperators

namespace OMA.S_oeis_a055203

theorem binomial_recurrence (j : ℕ) (f g : ℕ → ℤ)
    (hzero : g 0 = 0)
    (hsucc : ∀ k : ℕ, g (k + 1) = (k + 1 : ℤ) * (f (k + 1) + f k)) :
    (∑ k ∈ Finset.range (j + 1), (j.choose k : ℤ) * g k) =
      (j : ℤ) * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℤ) * f k := by
  let first : ℕ → ℤ := fun k => (j.choose k : ℤ) * k * f k
  let second : ℕ → ℤ := fun k => (j.choose k : ℤ) * (j - k : ℤ) * f k
  have hsum : ∀ k ∈ Finset.range j,
      (j.choose (k + 1) : ℤ) * g (k + 1) = first (k + 1) + second k := by
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hchoose : (j.choose (k + 1) : ℤ) * ((k : ℤ) + 1) =
        (j.choose k : ℤ) * ((j : ℤ) - k) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hkj] using
        congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_succ_right_eq j k)
    rw [hsucc]
    dsimp [first, second]
    calc
      _ = (j.choose (k + 1) : ℤ) * ((k : ℤ) + 1) * f (k + 1) +
          ((j.choose (k + 1) : ℤ) * ((k : ℤ) + 1)) * f k := by ring
      _ = _ := by nth_rw 2 [hchoose]
  have hshift :
      (∑ k ∈ Finset.range j, first (k + 1)) = ∑ k ∈ Finset.range (j + 1), first k := by
    rw [Finset.sum_range_succ']
    simp [first]
  have hlast :
      (∑ k ∈ Finset.range j, second k) = ∑ k ∈ Finset.range (j + 1), second k := by
    rw [Finset.sum_range_succ]
    simp [second]
  rw [Finset.sum_range_succ']
  simp only [hzero, mul_zero, add_zero]
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, hshift, hlast, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [first, second]
  ring

end OMA.S_oeis_a055203
namespace OMA.S_oeis_a055203

theorem pow_eq_sum_choose_mul_orderedStirlingCoefficient (j n : ℕ) :
    (j : ℤ) ^ n =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℤ) * orderedStirlingCoefficient n k := by
  induction n with
  | zero =>
    rw [pow_zero, Finset.sum_eq_single 0]
    · simp [orderedStirlingCoefficient_zero]
    · intro k _ hk
      simp [orderedStirlingCoefficient_zero, hk]
    · simp
  | succ n ih =>
    rw [binomial_recurrence j _ _ (orderedStirlingCoefficient_succ_zero n)]
    · rw [← ih, pow_succ, mul_comm]
    · intro k
      rw [orderedStirlingCoefficient_succ_succ, mul_add]

end OMA.S_oeis_a055203

open scoped BigOperators

namespace OMA.S_oeis_a055203

/-- A unit-diagonal binomial transform preserves equality in the reverse direction. -/
theorem eq_of_binomial_sums_eq {R : Type*} [Ring R] {f g : ℕ → R}
    (h : ∀ j : ℕ, (∑ k ∈ Finset.range (j + 1), (j.choose k : R) * f k) =
                    ∑ k ∈ Finset.range (j + 1), (j.choose k : R) * g k) :
    f = g := by
  funext j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hj := h j
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hj
    simp only [Nat.choose_self, Nat.cast_one, one_mul] at hj
    have hprefix :
        (∑ k ∈ Finset.range j, (j.choose k : R) * f k) =
           ∑ k ∈ Finset.range j, (j.choose k : R) * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    rw [hprefix] at hj
    exact add_left_cancel hj

end OMA.S_oeis_a055203
namespace OMA.S_oeis_a055203

theorem term_period_of_binomial_transform (m n : ℕ) (hm : 0 < m) (hn : m ≤ n)
    (formula : ∀ j t : ℕ, (j : ℤ) ^ t =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℤ) *
        ((k.factorial : ℤ) * Nat.stirlingSecond t k))
    (power_period : ∀ j : ℕ, (j : ZMod m) ^ (n + m.totient) = (j : ZMod m) ^ n) :
    (term (n + m.totient) : ZMod m) = (term n : ZMod m) := by
  have cast_formula (j t : ℕ) :
      (j : ZMod m) ^ t = ∑ k ∈ Finset.range (j + 1), (j.choose k : ZMod m) *
        ((k.factorial : ZMod m) * Nat.stirlingSecond t k) := by
    simpa only [Int.cast_mul, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
      using congrArg (fun x : ℤ => (x : ZMod m)) (formula j t)
  have coefficients : (fun k => (k.factorial : ZMod m) * Nat.stirlingSecond (n + m.totient) k) =
      fun k => (k.factorial : ZMod m) * Nat.stirlingSecond n k := by
    apply eq_of_binomial_sums_eq
    intro j
    simp only [← cast_formula, power_period]
  rw [term_truncate m _ hm (by omega), term_truncate m n hm hn]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun x => x * (weight k : ZMod m)) (congrFun coefficients k)

end OMA.S_oeis_a055203
open OMA.S_oeis_a055203 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055203.main := by
  refine ⟨term_mod12, fun m hm => ⟨m, fun n hn => ?_⟩⟩
  apply term_period_of_binomial_transform m n hm hn
  · intro j t
    exact pow_eq_sum_choose_mul_orderedStirlingCoefficient j t
  · intro j
    exact zmod_pow_add_totient_eq_of_le hm hn
