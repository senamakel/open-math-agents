import OMAStatements.S_oeis_a129194

import Mathlib

/-! The reduced denominator differs only by the factor of two allowed by parity. -/

theorem square_linear_gcd_dvd (n : ℤ) : Int.gcd (n^2) (4*n-2) ∣ 2 := by
  apply Int.natCast_dvd_natCast.mp
  have hd1 := Int.gcd_dvd_left (n^2) (4*n-2)
  have hd2 := Int.gcd_dvd_right (n^2) (4*n-2)
  have he : (2 : ℤ) = n^2*8 - (4*n-2)*(2*n+1) := by ring
  change (Int.gcd (n^2) (4*n-2) : ℤ) ∣ 2
  nth_rw 2 [he]
  exact Int.dvd_sub (dvd_mul_of_dvd_left hd1 _) (dvd_mul_of_dvd_left hd2 _)

theorem denominator_parity (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) / 2)^2 * (3 - (-1)^n) =
      ((((4 : ℚ) / n - 2 / (n : ℚ)^2).den : ℕ) : ℚ) := by
  have hx : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hxZ : ((n : ℤ)^2) ≠ 0 := by positivity
  have heq : ((4 : ℚ) / n - 2 / (n : ℚ)^2) =
      Rat.divInt (4 * (n : ℤ) - 2) ((n : ℤ)^2) := by
    rw [Rat.divInt_eq_div]
    push_cast
    field_simp
  rw [heq, Rat.den_divInt, if_neg hxZ]
  simp only [Int.natAbs_pow, Int.natAbs_natCast]
  let g := Int.gcd ((n : ℤ)^2) (4*(n : ℤ)-2)
  change ((n : ℚ) / 2)^2 * (3 - (-1)^n) = ((n^2/g : ℕ) : ℚ)
  have hg : g = 1 ∨ g = 2 := (Nat.dvd_prime Nat.prime_two).mp (square_linear_gcd_dvd n)
  rcases Nat.even_or_odd n with h | h
  · have hn2 : 2 ∣ n := even_iff_two_dvd.mp h
    have hnsq : 2 ∣ n^2 := hn2.trans (dvd_pow_self _ (by decide))
    have hg2 : 2 ∣ g := Int.dvd_gcd (by exact_mod_cast hnsq) (by omega)
    have hg' : g = 2 := by rcases hg with h | h <;> omega
    rw [h.neg_one_pow, hg']
    have hmul : (((n^2/2 : ℕ) : ℚ) * 2) = (n : ℚ)^2 := by
      exact_mod_cast Nat.div_mul_cancel hnsq
    linarith
  · have hn2 : ¬ 2 ∣ n := by
      intro hdiv
      exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hdiv)
    have hg' : g = 1 := by
      rcases hg with h1 | h2
      · exact h1
      · exfalso
        apply hn2
        apply Nat.prime_two.dvd_of_dvd_pow
        have hm : (g : ℤ) ∣ (n : ℤ)^2 := Int.gcd_dvd_left _ _
        rw [h2] at hm
        exact_mod_cast hm
    rw [h.neg_one_pow, hg', Nat.div_one, Nat.cast_pow]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a129194.main :=

  denominator_parity
