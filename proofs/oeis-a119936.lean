import OMAStatements.S_oeis_a119936


namespace MatrixRow

abbrev entry := OMA.S_oeis_a119936.entry

/-- The numerator obtained by scaling the row entry by `n * L^2`. -/
def scaled (n L j : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc j n, (L / i) * ∑ k ∈ Finset.Icc j i, L / k

/-- Clearing the Cesàro denominators gives the natural-number expression `scaled`. -/
theorem entry_scaled (n L j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hdiv : ∀ i ∈ Finset.Icc 1 n, i ∣ L) :
    (scaled n L j : ℚ) = (n : ℚ) * (L : ℚ) ^ 2 * entry n j := by
  have hquot (i : ℕ) (hi : i ∈ Finset.Icc j n) :
      ((L / i : ℕ) : ℚ) = (L : ℚ) / (i : ℚ) := by
    apply Nat.cast_div
    · apply hdiv
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · exact_mod_cast (show i ≠ 0 by
        have := Finset.mem_Icc.mp hi
        omega)
  have hinner (i : ℕ) (hi : i ∈ Finset.Icc j n) :
      ((∑ k ∈ Finset.Icc j i, L / k : ℕ) : ℚ) =
        ∑ k ∈ Finset.Icc j i, (L : ℚ) / (k : ℚ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hquot k (Finset.mem_Icc.mpr ⟨by
      exact (Finset.mem_Icc.mp hk).1,
      le_trans (Finset.mem_Icc.mp hk).2 (Finset.mem_Icc.mp hi).2⟩)
  have hscale (i : ℕ) (hi : i ∈ Finset.Icc j n) :
      ((L / i : ℕ) : ℚ) *
          ((∑ k ∈ Finset.Icc j i, L / k : ℕ) : ℚ) =
        (L : ℚ) ^ 2 * (1 / (i : ℚ)) *
          ∑ k ∈ Finset.Icc j i, (1 / (k : ℚ)) := by
    rw [hquot i hi, hinner i hi]
    have hi0 : (i : ℚ) ≠ 0 := by
      exact_mod_cast (show i ≠ 0 by
        have := Finset.mem_Icc.mp hi
        omega)
    have hsum :
        (∑ k ∈ Finset.Icc j i, (L : ℚ) / (k : ℚ)) =
          (L : ℚ) * ∑ k ∈ Finset.Icc j i, (1 / (k : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℚ) ≠ 0 := by
        exact_mod_cast (show k ≠ 0 by
          have hik := Finset.mem_Icc.mp hi
          have hki := Finset.mem_Icc.mp hk
          omega)
      field_simp
    rw [hsum]
    ring
  unfold scaled entry OMA.S_oeis_a119936.entry
  simp only [Nat.cast_sum, Nat.cast_mul]
  calc
    (∑ i ∈ Finset.Icc j n,
        (↑(L / i : ℕ) : ℚ) *
          ∑ k ∈ Finset.Icc j i, (↑(L / k : ℕ) : ℚ)) =
        ∑ i ∈ Finset.Icc j n,
          (L : ℚ) ^ 2 * (1 / (i : ℚ)) *
            ∑ k ∈ Finset.Icc j i, (1 / (k : ℚ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Nat.cast_sum] using hscale i hi
    _ = (n : ℚ) * (L : ℚ) ^ 2 *
        ((1 / (n : ℚ)) * ∑ i ∈ Finset.Icc j n,
          (1 / (i : ℚ)) * ∑ k ∈ Finset.Icc j i, (1 / (k : ℚ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hn0 : (n : ℚ) ≠ 0 := by
        exact_mod_cast (show n ≠ 0 by omega)
      have hi0 : (i : ℚ) ≠ 0 := by
        exact_mod_cast (show i ≠ 0 by
          have := Finset.mem_Icc.mp hi
          omega)
      field_simp

private lemma sum_Icc_succ_left_nat (j n : ℕ) (hj : j ≤ n)
    (f : ℕ → ℕ) :
    (∑ i ∈ Finset.Icc j n, f i) = f j + ∑ i ∈ Finset.Icc (j + 1) n, f i := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hj, Finset.sum_insert]
  simp

/-- Adjacent row differences have the integer numerator given by the tail sum. -/
theorem scaled_succ_difference (n L j : ℕ) (_hj : 1 ≤ j) (hjn : j ≤ n) :
    scaled n L j = scaled n L (j + 1) +
      (L / j) * ∑ i ∈ Finset.Icc j n, L / i := by
  have hinner (i : ℕ) (hi : j ≤ i) :
      (∑ k ∈ Finset.Icc j i, L / k) = L / j +
        ∑ k ∈ Finset.Icc (j + 1) i, L / k := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hi, Finset.sum_insert]
    simp
  have houter (f : ℕ → ℕ) :
      (∑ i ∈ Finset.Icc j n, f i) = f j +
        ∑ i ∈ Finset.Icc (j + 1) n, f i :=
    sum_Icc_succ_left_nat j n hjn f
  unfold scaled
  calc
    (∑ i ∈ Finset.Icc j n, (L / i) * ∑ k ∈ Finset.Icc j i, L / k) =
        ∑ i ∈ Finset.Icc j n,
          ((L / i) * (L / j) + (L / i) *
            ∑ k ∈ Finset.Icc (j + 1) i, L / k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinner i (Finset.mem_Icc.mp hi).1]
      ring
    _ = (L / j) * ∑ i ∈ Finset.Icc j n, L / i +
        ∑ i ∈ Finset.Icc j n,
          (L / i) * ∑ k ∈ Finset.Icc (j + 1) i, L / k := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Nat.mul_comm]
    _ = (L / j) * ∑ i ∈ Finset.Icc j n, L / i +
        ∑ i ∈ Finset.Icc (j + 1) n,
          (L / i) * ∑ k ∈ Finset.Icc (j + 1) i, L / k := by
      rw [houter (fun i => (L / i) * ∑ k ∈ Finset.Icc (j + 1) i, L / k)]
      simp
    _ = scaled n L (j + 1) + (L / j) * ∑ i ∈ Finset.Icc j n, L / i := by
      unfold scaled
      omega

end MatrixRow



open Finset

theorem exists_prime_unit_row_diff (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    ∃ m ∈ Finset.Icc 1 n, ¬ p ∣ (((Finset.Icc 1 n).lcm id) / m) *
      (∑ i ∈ Finset.Icc m n, ((Finset.Icc 1 n).lcm id) / i) := by
  let L := (Finset.Icc 1 n).lcm id
  have hLpos : 0 < L := by
    have hLne : L ≠ 0 := (Finset.lcm_ne_zero_iff).2 (by
      intro i hi
      have hi' : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      exact (show i ≠ 0 by omega))
    omega

  have hex : ∃ m ∈ Finset.Icc 1 n, ¬ p ∣ L / m := by
    by_contra! h
    have hpL : p ∣ L := by
      have h1 : 1 ∈ Finset.Icc 1 n := by simp; omega
      simpa using h 1 h1
    have hdiv : ∀ i ∈ Finset.Icc 1 n, i ∣ L / p := by
      intro i hi
      have hpi : p ∣ L / i := h i hi
      have hil : i ∣ L := Finset.dvd_lcm hi
      have hprod : p * i ∣ L := by
        rw [Nat.dvd_div_iff_mul_dvd hil] at hpi
        simpa [Nat.mul_comm] using hpi
      have : i ∣ L / p := (Nat.dvd_div_iff_mul_dvd hpL).2 (by simpa [Nat.mul_comm] using hprod)
      exact this
    have hLL : L ∣ L / p := Finset.lcm_dvd hdiv
    have hpgt : 1 < p := lt_of_lt_of_le (by decide) hp.two_le
    have hlt : L / p < L := Nat.div_lt_self hLpos hpgt
    have hpLe : p ≤ L := Nat.le_of_dvd hLpos hpL
    have hle : L ≤ L / p := Nat.le_of_dvd (Nat.div_pos hpLe hp.pos) hLL
    omega
  let s := (Finset.Icc 1 n).filter (fun m => ¬ p ∣ L / m)
  have hs : s.Nonempty := by
    rcases hex with ⟨m, hm, hmp⟩
    exact ⟨m, mem_filter.mpr ⟨hm, hmp⟩⟩
  let m := s.max' hs
  have hmS : m ∈ s := Finset.max'_mem s hs
  have hmI : m ∈ Finset.Icc 1 n := (mem_filter.mp hmS).1
  have hmIne : 1 ≤ m ∧ m ≤ n := by simpa only [Finset.mem_Icc] using hmI
  have hmp : ¬ p ∣ L / m := (mem_filter.mp hmS).2
  have hmax : ∀ i ∈ s, i ≤ m := fun i hi => Finset.le_max' s i hi
  have htail : ∀ i ∈ Finset.Icc m n, i ≠ m → p ∣ L / i := by
    intro i hi hne
    have hin : i ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc] at hi ⊢
      exact ⟨le_trans hmIne.1 (by omega), hi.2⟩
    by_contra hnot
    have his : i ∈ s := mem_filter.mpr ⟨hin, hnot⟩
    have : i ≤ m := hmax i his
    have hi' : m ≤ i ∧ i ≤ n := by simpa only [Finset.mem_Icc] using hi
    omega
  let T := ∑ i ∈ Finset.Icc m n, L / i
  have htailSum : p ∣ ∑ i ∈ (Finset.Icc m n).erase m, L / i := by
    apply Finset.dvd_sum
    intro i hi
    apply htail i (Finset.mem_of_mem_erase hi)
    exact Finset.ne_of_mem_erase hi
  have hmem : m ∈ Finset.Icc m n := Finset.mem_Icc.mpr ⟨le_rfl, hmIne.2⟩
  have hsum : T = L / m + ∑ i ∈ (Finset.Icc m n).erase m, L / i := by
    dsimp [T]
    rw [← Finset.sum_erase_add (Finset.Icc m n) (fun i => L / i) hmem]
    simp [add_comm]
  have hTmod : p ∣ T - L / m := by
    rw [hsum]
    simp only [Nat.add_sub_cancel_left]
    exact htailSum
  refine ⟨m, hmI, ?_⟩
  intro hprod
  have hfactor := hp.dvd_mul.mp hprod
  rcases hfactor with ha | hT
  · exact hmp ha
  · have hT' : p ∣ L / m + ∑ i ∈ (Finset.Icc m n).erase m, L / i := by
      rw [← hsum]
      exact hT
    have ha : p ∣ L / m := (Nat.dvd_add_left htailSum).mp hT'
    exact hmp ha



theorem exact_lcm_of_scaled_entries {ι : Type*} (s : Finset ι)
    (q : ι → ℚ) (B : ι → ℕ) (D : ℕ) (hD : 0 < D)
    (hscale : ∀ j ∈ s, (D : ℚ) * q j = B j)
    (hprime : ∀ p : ℕ, p.Prime → ∃ j ∈ s, ¬ p ∣ B j) :
    s.lcm (fun j => (q j).den) = D := by
  let M := s.lcm (fun j => (q j).den)
  have hMD : M ∣ D := by
    apply Finset.lcm_dvd
    intro j hj
    have hne : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hq : q j = Rat.divInt (B j : ℤ) (D : ℤ) := by
      rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
      apply (eq_div_iff hne).mpr
      rw [mul_comm]
      exact hscale j hj
    rw [hq]
    exact_mod_cast Rat.den_dvd (B j : ℤ) (D : ℤ)
  obtain ⟨c, hc⟩ := hMD
  have hc1 : c = 1 := by
    by_contra h
    obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd h
    obtain ⟨j, hj, hnot⟩ := hprime p hp
    have hden : (q j).den ∣ M := Finset.dvd_lcm (f := fun j => (q j).den) hj
    obtain ⟨u, hu⟩ := hden
    have hs := hscale j hj
    have hdn : ((q j).den : ℚ) ≠ 0 := by exact_mod_cast (q j).den_ne_zero
    have hInt : (B j : ℤ) = (p : ℤ) * ((q j).num * ↑u * ↑(c/p)) := by
      have hca : c = p*(c/p) := (Nat.mul_div_cancel' hpc).symm
      have hRat : (B j : ℚ) = (p : ℚ) * ((q j).num * (u : ℚ) * ((c/p : ℕ) : ℚ)) := by
        have hcancel : D = (q j).den * u * (p*(c/p)) := by
          rw [hc, hu, ← hca]
        rw [← hs, hcancel]
        push_cast
        conv_lhs => arg 2; rw [← (q j).num_div_den]
        field_simp

      apply Int.cast_injective (α := ℚ)
      push_cast
      exact hRat
    apply hnot
    exact_mod_cast (show (p : ℤ) ∣ (B j : ℤ) from ⟨_, hInt⟩)
  change M = D
  simpa [hc1] using hc.symm


namespace MatrixRow

theorem prove_main (n : ℕ) (hn : 0 < n) :
    (Finset.Icc 1 n).lcm (fun j => (entry n j).den) =
      n * ((Finset.Icc 1 n).lcm id)^2 := by
  let S := Finset.Icc 1 n
  let L := S.lcm id
  have hL : 0 < L := Nat.pos_of_ne_zero <| Finset.lcm_ne_zero_iff.mpr (by
    intro i hi
    change i ≠ 0
    have := (Finset.mem_Icc.mp hi).1
    omega)
  have hD : 0 < n*L^2 := Nat.mul_pos hn (pow_pos hL _)
  refine exact_lcm_of_scaled_entries S (entry n) (scaled n L) _ hD ?_ ?_
  · intro j hj
    obtain ⟨hj1,hjn⟩ := Finset.mem_Icc.mp hj
    push_cast
    exact (entry_scaled n L j hj1 hjn (fun i hi => Finset.dvd_lcm hi)).symm
  · intro p hp
    obtain ⟨m, hm, hdiff⟩ := exists_prime_unit_row_diff n p hn hp
    obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hm
    have hd := scaled_succ_difference n L m hm1 hmn
    by_cases hm' : p ∣ scaled n L m
    · have hs : p ∣ scaled n L (m+1) → False := by
        intro hs
        have h := Nat.dvd_sub hm' hs
        rw [hd, Nat.add_sub_cancel_left] at h
        exact hdiff h
      refine ⟨m+1, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hs⟩
      by_contra! ht
      have he : scaled n L (m+1) = 0 := by
        rw [scaled, Finset.Icc_eq_empty_of_lt ht, Finset.sum_empty]
      exact hs (he ▸ dvd_zero p)
    · exact ⟨m, hm, hm'⟩

end MatrixRow
theorem OMA.solution : type_of% @OMA.S_oeis_a119936.main :=
  MatrixRow.prove_main
