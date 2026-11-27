import OMAStatements.S_oeis_a158623

namespace OMA.S_oeis_a158623

private theorem fraction_closed (n : ℕ) (hn : 1 ≤ n) :
    fraction n = 2*((n : ℚ)^2+n+1)/(3*n*(n+1)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [fraction]
  | succ n hn ih =>
      have hi : Finset.Icc 2 (n+1) = insert (n+1) (Finset.Icc 2 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n+1 ∉ Finset.Icc 2 n := by simp
      rw [fraction, hi, Finset.prod_insert hnot, ← fraction, ih]
      have hn' : (0 : ℚ) < n := by exact_mod_cast hn
      push_cast
      field_simp
      <;> ring

private theorem fraction_den_twice (n : ℕ) (hn : 1 ≤ n) :
    2 * term n = (if n % 3 = 1 then 1 else 3) * (n*(n+1)) := by
  let C := n*(n+1)+1
  let D := n*(n+1)/2
  have hd : 2*D = n*(n+1) := by
    dsimp [D]
    apply Nat.mul_div_cancel'
    by_cases h : 2 ∣ n
    · exact dvd_mul_of_dvd_left h _
    · have h' : 2 ∣ n+1 := by omega
      exact dvd_mul_of_dvd_right h' _
  have hpos : 0 < D := by
    have h := Nat.mul_pos hn (show 0 < n+1 by omega)
    omega
  have hcop : C.Coprime D := by
    apply Nat.Coprime.of_dvd_right (show D ∣ n*(n+1) from ⟨2, by omega⟩)
    dsimp [C]
    simpa [Nat.coprime_add_self_left, add_comm] using
      (show (1 + n*(n+1)).Coprime (n*(n+1)) by simp)
  have hfrac : fraction n = (C : ℚ)/(3*D) := by
    rw [fraction_closed n hn]
    have he : (2 : ℚ)*D = (n : ℚ)*(n+1) := by exact_mod_cast hd
    have hc : (C : ℚ) = (n : ℚ)^2+n+1 := by
      dsimp [C]
      push_cast
      ring
    rw [hc]
    have hp : (0 : ℚ) < n := by exact_mod_cast hn
    have hq : (0 : ℚ) < D := by exact_mod_cast hpos
    field_simp
    nlinarith
  have hmod : 3 ∣ C ↔ n % 3 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [C]
    rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod n 1 3]
    have h : n % 3 < 3 := Nat.mod_lt _ (by decide)
    generalize hr : n % 3 = r at *
    interval_cases r <;> decide
  unfold term
  by_cases hr : n % 3 = 1
  · obtain ⟨a, ha⟩ := hmod.mpr hr
    have hca : a.Coprime D := hcop.of_dvd_left ⟨3, by omega⟩
    have hr' : fraction n = (a : ℚ)/(D : ℚ) := by
      rw [hfrac, ha]
      push_cast
      have hp : (0 : ℚ) < D := by exact_mod_cast hpos
      field_simp
    have hD' : (0 : ℤ) < D := by exact_mod_cast hpos
    have hden := Rat.den_div_eq_of_coprime (a := (a : ℤ)) hD' (by simpa using hca)
    have : (fraction n).den = D := by
      rw [hr']
      simpa only [Int.toNat_natCast, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] using
        (congrArg Int.toNat hden)
    simp [hr, this, hd]
  · have hC3 : C.Coprime 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h => hr (hmod.mp h)
    have hc' := hC3.mul_right hcop
    have hD' : (0 : ℤ) < ((3*D : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_pos (by decide : 0 < 3) hpos)
    have hden := Rat.den_div_eq_of_coprime (a := (C : ℤ)) hD' (by
      simpa only [Int.natAbs_natCast] using hc')
    have : (fraction n).den = 3*D := by
      rw [hfrac]
      have hh := congrArg Int.toNat hden
      simp only [Int.toNat_natCast, Int.cast_natCast] at hh
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
    simp only [hr, if_false, this]
    omega

private theorem prove_main (n : ℕ) (hn : 2 ≤ n) :
    (term (n+9) : ℤ) = 3*(term (n+6) : ℤ)-3*(term (n+3) : ℤ)+(term n : ℤ) := by
  let C : ℕ := if n % 3 = 1 then 1 else 3
  have he (i : ℕ) : 2 * (term (n+3*i) : ℤ) =
      (C : ℤ)*((n : ℤ)+3*i)*((n : ℤ)+3*i+1) := by
    have hn' : 1 ≤ n+3*i := by omega
    have h := fraction_den_twice (n+3*i) hn'
    have hm : (n+3*i)%3 = n%3 := by simp [Nat.add_mod]
    rw [hm] at h
    change 2 * term (n+3*i) = C * ((n+3*i)*(n+3*i+1)) at h
    rw [← Nat.mul_assoc] at h
    exact_mod_cast h
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  norm_num at h0 h1 h2 h3
  have hscaled : 2*(term (n+9) : ℤ) =
      2*(3*(term (n+6) : ℤ)-3*(term (n+3) : ℤ)+(term n : ℤ)) := by
    linear_combination h3-3*h2+3*h1-h0
  omega

end OMA.S_oeis_a158623

theorem OMA.solution : type_of% @OMA.S_oeis_a158623.main :=
  OMA.S_oeis_a158623.prove_main
