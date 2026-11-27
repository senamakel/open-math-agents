import OMAStatements.S_oeis_a343260

namespace OMA.S_oeis_a343260

open Polynomial

theorem term_modEq_of_derivative_and_value (n : ℕ)
    (hD : (n : ℤ) ∣ ((Chebyshev.C ℤ (n : ℤ)).derivative.eval 1))
    (hC : (Chebyshev.C ℤ (n : ℤ)).eval 1 = 1) :
    Int.ModEq ((n : ℤ)^2) (term n) 1 := by
  obtain ⟨d,hd⟩ := hD
  obtain ⟨c,hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add
    (Chebyshev.C ℤ (n : ℤ)) 1 (n : ℤ)
  simp only [hd, hC, add_comm (a := (1 : ℤ))] at hc
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(c+d), ?_⟩
  change 1 - (Chebyshev.C ℤ (n : ℤ)).eval ((n : ℤ)+1) = _
  rw [← hc]
  ring

theorem prime_power_modulus (p r : ℕ) :
    ((p^r : ℕ) : ℤ)^2 = (p : ℤ)^(2*r) := by
  rw [Nat.cast_pow, Nat.mul_comm 2 r, pow_mul]

end OMA.S_oeis_a343260

open Polynomial

namespace OMA.S_oeis_a343260

private theorem rat_derivative_at_one (n : ℤ) :
    (Chebyshev.C ℚ n).derivative.eval 1 = (n : ℚ) * (Chebyshev.S ℚ (n-1)).eval 1 := by
  have hc := congrArg (fun p : Polynomial ℚ => p.derivative.eval (1/2))
    (Chebyshev.C_comp_two_mul_X ℚ n)
  simp only [derivative_comp, derivative_mul, derivative_X, derivative_ofNat,
    zero_mul, mul_one, eval_mul, eval_comp, eval_ofNat, eval_X,
    Chebyshev.T_derivative_eq_U] at hc
  norm_num at hc
  have hs := congrArg (fun p : Polynomial ℚ => p.eval (1/2))
    (Chebyshev.S_comp_two_mul_X ℚ (n-1))
  simp only [eval_comp, eval_mul, eval_ofNat, eval_X] at hs
  norm_num at hs
  rw [← hs] at hc
  linarith

theorem index_dvd_derivative_at_one (n : ℕ) :
    (n : ℤ) ∣ ((Chebyshev.C ℤ (n : ℤ)).derivative.eval 1) := by
  refine ⟨(Chebyshev.S ℤ ((n:ℤ)-1)).eval 1, ?_⟩
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_natCast]
  have hC : (((Chebyshev.C ℤ (n:ℤ)).derivative.eval 1 : ℤ) : ℚ) =
      (Chebyshev.C ℚ (n:ℤ)).derivative.eval 1 := by
    change (Int.castRingHom ℚ) _ = _
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map,
      Polynomial.Chebyshev.map_C, map_one]
  have hS : (((Chebyshev.S ℤ ((n:ℤ)-1)).eval 1 : ℤ) : ℚ) =
      (Chebyshev.S ℚ ((n:ℤ)-1)).eval 1 := by
    change (Int.castRingHom ℚ) _ = _
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map,
      Polynomial.Chebyshev.map_S, map_one]
  rw [hC,hS]
  simpa using rat_derivative_at_one (n:ℤ)

end OMA.S_oeis_a343260

namespace OMA.S_oeis_a343260

private noncomputable def chebAtOne (n : ℕ) : ℤ :=
  (Polynomial.Chebyshev.C ℤ (n : ℤ)).eval 1

private theorem chebAtOne_add_two (n : ℕ) :
    chebAtOne (n + 2) = chebAtOne (n + 1) - chebAtOne n := by
  have h := congrArg (fun q : Polynomial ℤ => q.eval 1)
    (Polynomial.Chebyshev.C_add_two ℤ (n : ℤ))
  convert h using 1 <;> norm_cast
  simp [chebAtOne, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X]

private theorem chebAtOne_zero : chebAtOne 0 = 2 := by
  simp [chebAtOne, Polynomial.Chebyshev.C_zero]
private theorem chebAtOne_one : chebAtOne 1 = 1 := by simp [chebAtOne]
private theorem chebAtOne_two : chebAtOne 2 = -1 := by
  rw [chebAtOne_add_two, chebAtOne_one, chebAtOne_zero]
  norm_num
private theorem chebAtOne_three : chebAtOne 3 = -2 := by
  rw [chebAtOne_add_two, chebAtOne_two, chebAtOne_one]
  norm_num
private theorem chebAtOne_four : chebAtOne 4 = -1 := by
  rw [chebAtOne_add_two, chebAtOne_three, chebAtOne_two]
  norm_num
private theorem chebAtOne_five : chebAtOne 5 = 1 := by
  rw [chebAtOne_add_two, chebAtOne_four, chebAtOne_three]
  norm_num
private theorem chebAtOne_six : chebAtOne 6 = 2 := by
  rw [chebAtOne_add_two, chebAtOne_five, chebAtOne_four]
  norm_num
private theorem chebAtOne_seven : chebAtOne 7 = 1 := by
  rw [chebAtOne_add_two, chebAtOne_six, chebAtOne_five]
  norm_num

private theorem chebAtOne_period_six (n : ℕ) :
    chebAtOne (n + 6) = chebAtOne n := by
  induction n using Nat.twoStepInduction with
  | zero => exact (chebAtOne_six).trans chebAtOne_zero.symm
  | one => exact (chebAtOne_seven).trans chebAtOne_one.symm
  | more n ih0 ih1 =>
      have hnext := chebAtOne_add_two (n + 6)
      have hbase := chebAtOne_add_two n
      have ih0' : chebAtOne (n + 6) = chebAtOne n := ih0
      have ih1' : chebAtOne (n + 1 + 6) = chebAtOne (n + 1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih1
      have hnext' : chebAtOne (n + 2 + 6) =
          chebAtOne (n + 1 + 6) - chebAtOne (n + 6) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
      rw [hnext', ih1', ih0', hbase]

private theorem chebAtOne_six_mul_add (q n : ℕ) :
    chebAtOne (6 * q + n) = chebAtOne n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h := chebAtOne_period_six (6 * q + n)
      have hidx : 6 * (q + 1) + n = (6 * q + n) + 6 := by omega
      rw [hidx, h, ih]

theorem chebC_eval_one_eq_one_of_mod_six (n : ℕ)
    (h : n % 6 = 1 ∨ n % 6 = 5) :
    (Polynomial.Chebyshev.C ℤ (n : ℤ)).eval 1 = 1 := by
  have hdecomp : n = 6 * (n / 6) + n % 6 := by omega
  rw [hdecomp]
  change chebAtOne (6 * (n / 6) + n % 6) = 1
  rw [chebAtOne_six_mul_add]
  rcases h with h | h
  · rw [h]
    exact chebAtOne_one
  · rw [h]
    exact chebAtOne_five

theorem prime_power_mod_six_eq_one_or_five {p r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : p ^ r % 6 = 1 ∨ p ^ r % 6 = 5 := by
  have hpr : p % 6 = 1 ∨ p % 6 = 5 := by
    have hlt : p % 6 < 6 := Nat.mod_lt _ (by omega)
    have hne2 : p % 2 ≠ 0 := by
      intro h
      have hdiv : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
      have : 2 = p := (Nat.dvd_prime hp).mp hdiv |>.resolve_left (by omega)
      omega
    have hne3 : p % 3 ≠ 0 := by
      intro h
      have hdiv : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
      have : 3 = p := (Nat.dvd_prime hp).mp hdiv |>.resolve_left (by omega)
      omega
    interval_cases hrem : p % 6 <;> simp_all <;> omega
  rcases hpr with hp1 | hp5r
  · have hpow : ∀ r : ℕ, p ^ r % 6 = 1 := by
      intro r
      induction r with
      | zero => norm_num
      | succ r ih =>
          rw [pow_succ, Nat.mul_mod, hp1, ih]
    exact Or.inl (hpow r)
  · have hpow : ∀ r : ℕ, p ^ r % 6 = 1 ∨ p ^ r % 6 = 5 := by
      intro r
      induction r with
      | zero => norm_num
      | succ r ih =>
          rw [pow_succ, Nat.mul_mod, hp5r]
          rcases ih with ih | ih
          · rw [ih]
            norm_num
          · rw [ih]
            norm_num
    exact hpow r

end OMA.S_oeis_a343260
open OMA.S_oeis_a343260 in
theorem OMA.solution : type_of% @OMA.S_oeis_a343260.main := by
  intro p r hp hp5 _
  rw [← prime_power_modulus p r]
  exact term_modEq_of_derivative_and_value (p^r) (index_dvd_derivative_at_one (p^r))
    (chebC_eval_one_eq_one_of_mod_six (p^r) (prime_power_mod_six_eq_one_or_five hp hp5))
