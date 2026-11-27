import OMAStatements.S_oeis_a266491

namespace OMA.S_oeis_a266491

private def annihilator (i n : ℕ) : ℤ :=
  row i (n+4) + 2*row i (n+2) + row i n

private theorem annihilator_zero_row (n : ℕ) : annihilator 0 n = 6*((n : ℤ)+2) := by
  simp only [annihilator, row, base, Nat.cast_add, Nat.cast_ofNat]
  have h4 : (n+4)%4=n%4 := by omega
  rw [h4]
  have hh : n%4<4 := Nat.mod_lt _ (by decide)
  have h2 : (n+2)%4 = (n%4+2)%4 := by omega
  rw [h2]
  interval_cases h : n%4 <;> norm_num <;> ring

private theorem annihilator_succ (i n : ℕ) :
    annihilator (i+1) n = annihilator i (n+1) - annihilator i n := by
  simp only [annihilator, row]
  rw [show n+1+4=n+4+1 by omega, show n+1+2=n+2+1 by omega]
  ring

private theorem annihilator_vanish (i n : ℕ) : annihilator (i+2) n = 0 := by
  induction i generalizing n with
  | zero =>
    simp only [Nat.zero_add]
    change annihilator (1+1) n = 0
    rw [annihilator_succ, annihilator_succ 0, annihilator_succ 0]
    simp only [annihilator_zero_row, Nat.cast_add, Nat.cast_one]
    ring
  | succ i ih =>
    change annihilator ((i+2)+1) n = 0
    rw [annihilator_succ, ih, ih, sub_self]

private theorem row_shift (i n : ℕ) : row i (n+1) = row (i+1) n + row i n := by
  rw [row]
  ring

private theorem row_shift_two (i n : ℕ) :
    row i (n+2) = row (i+2) n + 2*row (i+1) n + row i n := by
  rw [show n+2=(n+1)+1 by omega, row_shift i (n+1), row_shift (i+1) n, row_shift i n]
  ring

theorem row_recurrence (i n : ℕ) (hi : 2 ≤ i) :
    row (i+4) n + 4*row (i+3) n + 8*row (i+2) n + 8*row (i+1) n + 4*row i n = 0 := by
  have h : annihilator i n = 0 := by
    rw [show i=i-2+2 by omega]
    exact annihilator_vanish _ _
  unfold annihilator at h
  rw [show n+4=(n+2)+2 by omega, row_shift_two i (n+2),
    row_shift_two (i+2) n, row_shift_two (i+1) n, row_shift_two i n] at h
  linear_combination h


end OMA.S_oeis_a266491

namespace OMA.S_oeis_a266491
/-- The sign in the first column, with period eight. -/
def columnSign (i : ℕ) : ℤ :=
  match i % 8 with
  | 0 => 0
  | 1 => -1
  | 2 => 1
  | 3 => -1
  | 4 => 0
  | 5 => 1
  | 6 => -1
  | _ => 1

/-- The signed closed form for the first column, from row two onward. -/
def signedColumn (i : ℕ) : ℤ := scale i * (i : ℤ) * columnSign i

end OMA.S_oeis_a266491
namespace OMA.S_oeis_a266491

private theorem scale_offset (i j : ℕ) (hi : 2 ≤ i) :
    scale (i+j) = scale i * 2 ^ ((i%2+j)/2) := by
  have he : (i+j)/2-1 = i/2-1 + (i%2+j)/2 := by omega
  simp only [scale, he, pow_add]

private theorem signed_recurrence (i : ℕ) (hi : 2 ≤ i) :
    signedColumn (i+4) + 4*signedColumn (i+3) + 8*signedColumn (i+2) +
      8*signedColumn (i+1) + 4*signedColumn i = 0 := by
  simp only [signedColumn, scale_offset i _ hi, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hr : i % 2 = (i % 8) % 2 := by omega
  rw [hr]
  interval_cases h : i % 8 <;> norm_num [columnSign, Nat.add_mod, h] <;> ring

theorem first_column (i : ℕ) :
    (row i 0 / scale i).natAbs = if i % 4 = 0 then 0 else i := by
  have hs (i : ℕ) (hi : 2 ≤ i) : row i 0 = signedColumn i := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases hsmall : i < 6
      · interval_cases i <;> norm_num [row, base, signedColumn, scale, columnSign]
      · let j := i-4
        have hj : 2 ≤ j := by dsimp [j]; omega
        have hji : j+4=i := by dsimp [j]; omega
        have hrow := row_recurrence j 0 hj
        have hsign := signed_recurrence j hj
        rw [hji, ih (j+3) (by omega) (by omega), ih (j+2) (by omega) (by omega),
          ih (j+1) (by omega) (by omega), ih j (by omega) hj] at hrow
        rw [hji] at hsign
        omega
  by_cases hi : 2 ≤ i
  · rw [hs i hi, signedColumn, mul_assoc, Int.mul_ediv_cancel_left _ (by
      unfold scale
      positivity)]
    have hm : i%8 < 8 := Nat.mod_lt _ (by decide)
    have h4 : i%4=(i%8)%4 := by omega
    rw [h4]
    interval_cases h : i%8 <;> norm_num [columnSign, h, Int.natAbs_mul]
  · interval_cases i <;> norm_num [row, base, scale]


end OMA.S_oeis_a266491
namespace OMA.S_oeis_a266491

private theorem row_four_even (n : ℕ) : (2 : ℤ) ∣ row 4 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> norm_num [row, base]
    · have hrec := annihilator_vanish 2 (n-4)
      change row 4 (n-4+4)+2*row 4 (n-4+2)+row 4 (n-4)=0 at hrec
      rw [show n-4+4=n by omega] at hrec
      have hprev := ih (n-4) (by omega)
      obtain ⟨x,hx⟩ := hprev
      refine ⟨-row 4 (n-4+2)-x, ?_⟩
      omega

private theorem scale_mono_dvd {i j : ℕ} (hij : i ≤ j) : scale i ∣ scale j := by
  unfold scale
  exact pow_dvd_pow _ (by omega)

theorem all_rows_divisible (i n : ℕ) : scale i ∣ row i n := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 6
    · interval_cases i
      · norm_num [scale]
      · norm_num [scale]
      · norm_num [scale]
      · norm_num [scale]
      · simpa [scale] using row_four_even n
      · simpa [scale, row] using dvd_sub (row_four_even (n+1)) (row_four_even n)
    · let j := i-4
      have hj : 2 ≤ j := by dsimp [j]; omega
      have hj4 : j+4=i := by dsimp [j]; omega
      have hr := row_recurrence j n hj
      have hd (d : ℕ) (c : ℤ) (hd : d < 4) (hc : (4 : ℤ) ∣ c) :
          scale i ∣ c * row (j+d) n := by
        have hrow := (scale_mono_dvd (show j ≤ j+d by omega)).trans
          (ih (j+d) (by omega))
        have hs : scale i = 4 * scale j := by
          rw [← hj4, scale_offset j 4 hj]
          have he : (j%2+4)/2 = 2 := by omega
          rw [he]
          ring
        rw [hs]
        exact mul_dvd_mul hc hrow
      have h₃ := hd 3 4 (by decide) (by decide)
      have h₂ := hd 2 8 (by decide) (by decide)
      have h₁ := hd 1 8 (by decide) (by decide)
      have h₀ := hd 0 4 (by decide) (by decide)
      have ht := dvd_neg.mpr (dvd_add (dvd_add (dvd_add h₃ h₂) h₁) h₀)
      have he : row i n = -(4*row (j+3) n + 8*row (j+2) n + 8*row (j+1) n + 4*row j n) := by
        rw [hj4] at hr
        omega
      rw [he]
      exact ht


end OMA.S_oeis_a266491

theorem OMA.solution : type_of% @OMA.S_oeis_a266491.main :=
  ⟨OMA.S_oeis_a266491.all_rows_divisible, OMA.S_oeis_a266491.first_column⟩
