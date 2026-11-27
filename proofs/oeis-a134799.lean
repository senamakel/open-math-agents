import OMAStatements.S_oeis_a134799

namespace OMA.S_oeis_a134799

private def exponent (n : ℕ) : ℕ := (3^n+1)/2

private theorem base_odd (n : ℕ) : 3^n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

private theorem exponent_pos (n : ℕ) : 0 < exponent n := by
  have := base_odd n
  have hp : 1 ≤ 3^n := Nat.one_le_pow n 3 (by decide)
  unfold exponent
  omega

private theorem exponent_step (n : ℕ) : exponent (n+1)+1 = 3*exponent n := by
  have := base_odd n
  unfold exponent
  rw [pow_succ]
  omega

private theorem scaled_step (A : ℤ) {d : ℕ} (hd : 0 < d) (hA : ¬ (3:ℤ) ∣ A) :
    ∃ B : ℤ, ¬ (3:ℤ) ∣ B ∧
      A * ((3:ℤ)^(d*2)-A^2) = 2*B := by
  have hm : (2:ℤ) ∣ A * ((3:ℤ)^(d*2)-A^2) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    push_cast
    have hthree : (3 : ZMod 2) = 1 := by decide
    rw [hthree, one_pow]
    exact (show ∀ x : ZMod 2, x * (1-x^2) = 0 by decide) _
  obtain ⟨B,hB⟩ := hm
  refine ⟨B, ?_, hB⟩
  intro h
  have hz : (B : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  have he := congrArg (fun x : ℤ => (x : ZMod 3)) hB
  push_cast at he
  rw [hz, mul_zero] at he
  have ht : (3 : ZMod 3) = 0 := by decide
  rw [ht, zero_pow (by omega : d*2 ≠ 0), zero_sub] at he
  have hAz : (A : ZMod 3) ≠ 0 := fun ha =>
    hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ha)
  exact (mul_ne_zero hAz (neg_ne_zero.mpr (pow_ne_zero _ hAz))) he

private theorem rational_step (A B : ℤ) (d e : ℕ) (hde : e+1=3*d)
    (hAB : A * ((3:ℤ)^(d*2) - A^2) = 2*B) :
    (3/2 : ℚ) * ((A : ℚ)/3^d) * (1 - (((A : ℚ)/3^d))^2) = (B : ℚ)/3^e := by
  let X : ℚ := 3^d
  let Y : ℚ := 3^e
  have hx : X ≠ 0 := by dsimp [X]; positivity
  have hy : Y ≠ 0 := by dsimp [Y]; positivity
  have hY : Y*3 = X^3 := by
    dsimp [X,Y]
    rw [← pow_succ, hde, mul_comm 3 d, pow_mul]
  have hN : (A : ℚ)*(X^2-(A : ℚ)^2) = 2*(B : ℚ) := by
    have h := congrArg (fun x : ℤ => (x : ℚ)) hAB
    push_cast at h
    rw [pow_mul] at h
    exact h
  change (3/2 : ℚ) * ((A : ℚ)/X) * (1 - ((A : ℚ)/X)^2) = (B : ℚ)/Y
  calc
    _ = (3*((A : ℚ)*(X^2-(A : ℚ)^2)))/(2*X^3) := by
      field_simp [hx]
    _ = _ := by
      rw [hN, ← hY]
      field_simp [hy]

private theorem represent (n : ℕ) :
    ∃ A : ℤ, ¬ (3:ℤ) ∣ A ∧ iterate n = (A : ℚ) / 3^exponent n := by
  induction n with
  | zero => exact ⟨1, by decide, by norm_num [iterate, exponent]⟩
  | succ n ih =>
    obtain ⟨A, hA, hv⟩ := ih
    obtain ⟨B, hB, hAB⟩ := scaled_step A (exponent_pos n) hA
    exact ⟨B, hB, by rw [iterate, hv]; exact rational_step A B _ _ (exponent_step n) hAB⟩

private theorem prove_main (n : ℕ) : (iterate n).den = 3 * term n := by
  obtain ⟨A,hA,hv⟩ := represent n
  have hcop : A.natAbs.Coprime (3^exponent n) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun h => hA (Int.natCast_dvd.mpr h)
  have hpos : 0 < ((3:ℤ)^exponent n) := by positivity
  have hdn := Rat.den_div_eq_of_coprime hpos (by simpa using hcop)
  have hd : (iterate n).den = 3^exponent n := by
    rw [hv]
    exact_mod_cast hdn
  rw [hd, term, mul_comm, ← pow_succ]
  congr 1
  have := base_odd n
  have hp : 1 ≤ 3^n := Nat.one_le_pow n 3 (by decide)
  unfold exponent
  omega

end OMA.S_oeis_a134799

theorem OMA.solution : type_of% @OMA.S_oeis_a134799.main :=
  OMA.S_oeis_a134799.prove_main
